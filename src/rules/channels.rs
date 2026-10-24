//! Diagnostics for Effect, Stream and Layer type channels.
use std::collections::{HashMap, HashSet, VecDeque};

use tsrs_ast::{self as ast, Kind, Node, Symbol};
use tsrs_checker::{ContextFlags, SignatureKind, Type, TypeFlags};
use tsrs_core::P;

use super::{RelatedDiagnostic, RuleContext};
use crate::Rule;
use crate::semantic::{Channels, LAZY_ALLOW_ASYNC, TransformationKind};

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::FloatingEffectInVitest,
        Rule::MissingEffectError,
        Rule::MissingEffectContext,
        Rule::MissingLayerContext,
        Rule::EffectInVoidSuccess,
        Rule::EffectInFailure,
        Rule::UnknownInEffectCatch,
        Rule::GlobalErrorInEffectCatch,
        Rule::GlobalErrorInEffectFailure,
        Rule::AnyUnknownInErrorContext,
        Rule::UnsafeEffectTypeAssertion,
        Rule::LazyPromiseInEffectSync,
        Rule::PromiseInEffectSuccess,
        Rule::StrictBooleanExpressions,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    if ctx.enabled(Rule::MissingEffectError)
        || ctx.enabled(Rule::MissingEffectContext)
        || ctx.enabled(Rule::MissingLayerContext)
    {
        check_relation_errors(ctx);
    }
    if ctx.enabled(Rule::EffectInVoidSuccess) {
        check_void_success(ctx);
    }
    if ctx.enabled(Rule::EffectInFailure) {
        check_nested_failure(ctx);
    }
    if ctx.enabled(Rule::AnyUnknownInErrorContext) {
        check_any_unknown(ctx);
    }
    if ctx.enabled(Rule::PromiseInEffectSuccess) {
        check_promise_success(ctx);
    }
    if ctx.enabled(Rule::StrictBooleanExpressions) {
        check_boolean_conditions(ctx);
    }
    let mut nodes = Vec::new();
    super::walk(ctx.file.as_node(), &mut |node| nodes.push(node));
    for node in nodes {
        if node.kind() == Kind::CallExpression {
            if ctx.enabled(Rule::FloatingEffectInVitest) {
                check_vitest(ctx, node);
            }
            if ctx.enabled(Rule::UnknownInEffectCatch)
                || ctx.enabled(Rule::GlobalErrorInEffectCatch)
            {
                check_catch(ctx, node);
            }
            if ctx.enabled(Rule::LazyPromiseInEffectSync) {
                check_lazy_promise(ctx, node);
            }
        }
        if ctx.enabled(Rule::GlobalErrorInEffectFailure) && node.kind() == Kind::NewExpression {
            check_global_error_failure(ctx, node);
        }
        if ctx.enabled(Rule::UnsafeEffectTypeAssertion)
            && matches!(
                node.kind(),
                Kind::AsExpression | Kind::TypeAssertionExpression
            )
        {
            check_assertion(ctx, node);
        }
    }
}

fn unhandled(ctx: &mut RuleContext<'_>, source: P<Type>, target: P<Type>) -> Vec<P<Type>> {
    ctx.union_members(source)
        .into_iter()
        .filter(|&member| !ctx.checker.is_type_assignable_to(member, target))
        .collect()
}

fn format_types(ctx: &mut RuleContext<'_>, types: &[P<Type>]) -> String {
    types
        .iter()
        .map(|&t| ctx.type_string(t))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn check_relation_errors(ctx: &mut RuleContext<'_>) {
    for error in ctx.checker.get_relation_errors(ctx.file) {
        if (ctx.enabled(Rule::MissingEffectError) || ctx.enabled(Rule::MissingEffectContext))
            && let (Some(source), Some(target)) =
                (ctx.effect_type(error.source), ctx.effect_type(error.target))
        {
            if ctx.enabled(Rule::MissingEffectError)
                && !source.e.flags().intersects(TypeFlags::Never)
            {
                let missing = unhandled(ctx, source.e, target.e);
                if !missing.is_empty() {
                    let message = format_types(ctx, &missing);
                    ctx.emit(
                        Rule::MissingEffectError,
                        error.error_node,
                        377003,
                        &[message],
                    );
                }
            }
            if ctx.enabled(Rule::MissingEffectContext) {
                let missing = unhandled(ctx, source.r, target.r);
                if !missing.is_empty() {
                    let message = format_types(ctx, &missing);
                    let related = missing_context_related(ctx, error.error_node, &missing);
                    let index = ctx.emit(
                        Rule::MissingEffectContext,
                        error.error_node,
                        377004,
                        &[message],
                    );
                    ctx.diagnostics[index].related = related;
                }
            }
        }
        if ctx.enabled(Rule::MissingLayerContext)
            && let (Some(source), Some(target)) =
                (ctx.layer_type(error.source), ctx.layer_type(error.target))
        {
            let missing = unhandled(ctx, source.r, target.r);
            if !missing.is_empty() {
                let mut names = missing
                    .into_iter()
                    .map(|t| ctx.type_string(t))
                    .collect::<Vec<_>>();
                names.sort();
                ctx.emit(
                    Rule::MissingLayerContext,
                    error.error_node,
                    377034,
                    &[names.join(" | ")],
                );
            }
        }
    }
}

fn is_type_equivalent(node: P<Node>) -> bool {
    let Some(parent) = node.parent() else {
        return false;
    };
    match node.kind() {
        Kind::Identifier if parent.name() == Some(node) => match parent.kind() {
            Kind::PropertyAccessExpression => !ast::is_part_of_type_node(parent),
            Kind::VariableDeclaration
            | Kind::Parameter
            | Kind::PropertyDeclaration
            | Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment => true,
            _ => false,
        },
        Kind::ParenthesizedExpression | Kind::SatisfiesExpression => true,
        _ => false,
    }
}

// The original type parser rejects these nodes before calling the checker.
fn type_candidate(node: P<Node>) -> bool {
    if !(ast::is_expression(node) || ast::is_type_node(node) || ast::is_declaration(node))
        || node.kind() == Kind::ImportClause
    {
        return false;
    }
    if let Some(parent) = node.parent()
        && (ast::is_jsx_tag_name(node)
            || (parent.kind() == Kind::JsxAttribute && parent.name() == Some(node))
            || (node.kind() == Kind::TemplateExpression
                && parent.kind() == Kind::TaggedTemplateExpression)
            || (node.kind() == Kind::MetaProperty && parent.kind() == Kind::CallExpression))
    {
        return false;
    }
    if matches!(
        node.kind(),
        Kind::Identifier | Kind::PropertyAccessExpression | Kind::ExpressionWithTypeArguments
    ) {
        let mut current = Some(node);
        while let Some(n) = current {
            match n.kind() {
                Kind::Identifier | Kind::PropertyAccessExpression => current = n.parent(),
                Kind::ExpressionWithTypeArguments => {
                    if let Some(heritage) = n.parent().filter(|p| p.kind() == Kind::HeritageClause)
                        && (heritage
                            .parent()
                            .is_some_and(|p| p.kind() == Kind::InterfaceDeclaration)
                            || heritage.as_heritage_clause().token() == Kind::ImplementsKeyword)
                    {
                        return false;
                    }
                    break;
                }
                _ => break,
            }
        }
    }
    true
}

fn first_strict_effect(ctx: &mut RuleContext<'_>, ty: P<Type>) -> Option<P<Type>> {
    ctx.union_members(ty)
        .into_iter()
        .find(|&t| ctx.strict_effect_type(t).is_some())
}

fn check_nested_failure(ctx: &mut RuleContext<'_>) {
    let mut stack = vec![(ctx.file.as_node(), false)];
    let mut skip = HashSet::new();
    while let Some((node, visited)) = stack.pop() {
        if !visited {
            stack.push((node, true));
            node.for_each_child(&mut |child| {
                stack.push((child, false));
                false
            });
            continue;
        }
        if skip.contains(&node) {
            if let Some(parent) = node.parent() {
                skip.insert(parent);
            }
            continue;
        }
        if is_type_equivalent(node) || !type_candidate(node) || ctx.cannot_be_effect_type(node) {
            continue;
        }
        let ty = ctx.ty(node);
        let Some(effect) = ctx.strict_effect_type(ty) else {
            continue;
        };
        let Some(nested) = first_strict_effect(ctx, effect.e) else {
            continue;
        };
        let name = ctx.type_string(nested);
        ctx.emit(Rule::EffectInFailure, node, 377054, &[name]);
        if let Some(parent) = node.parent() {
            skip.insert(parent);
        }
    }
}

#[derive(Clone, Copy)]
enum Expected {
    Node(P<Node>),
    Symbol(P<Symbol>, P<Node>),
    Type(P<Type>),
}

fn inferred_return(ctx: &mut RuleContext<'_>, declaration: P<Node>) -> Option<P<Type>> {
    declaration.body()?;
    let ty = ctx.ty(declaration);
    let sigs = ctx.checker.get_signatures_of_type(ty, SignatureKind::Call);
    if sigs.len() > 1 {
        let types = sigs
            .iter()
            .map(|&s| ctx.checker.get_return_type_of_signature(s))
            .collect::<Vec<_>>();
        return Some(ctx.checker.get_union_type(&types));
    }
    let sig = ctx
        .checker
        .get_signature_from_declaration_exported(declaration);
    if let Some(predicate) = ctx.checker.get_type_predicate_of_signature(sig)
        && let Some(ty) = predicate.type_()
    {
        return Some(ty);
    }
    Some(ctx.checker.get_return_type_of_signature(sig))
}

fn assignment_sites(ctx: &mut RuleContext<'_>) -> Vec<(P<Node>, P<Node>, Expected)> {
    let mut result = Vec::new();
    let mut queue = VecDeque::from([ctx.file.as_node()]);
    while let Some(node) = queue.pop_front() {
        match node.kind() {
            Kind::VariableDeclaration => {
                if let (Some(name), Some(value)) =
                    (node.name(), node.as_variable_declaration().initializer())
                {
                    result.push((name, value, Expected::Node(name)));
                    queue.push_back(value);
                    continue;
                }
            }
            Kind::CallExpression => {
                let sig = ctx.checker.get_resolved_signature_exported(node);
                for (&param, &arg) in sig
                    .parameters()
                    .iter()
                    .zip(node.as_call_expression().arguments().nodes())
                {
                    result.push((arg, arg, Expected::Symbol(param, node)));
                }
            }
            Kind::Identifier
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::NoSubstitutionTemplateLiteral => {
                if let Some(parent) = node.parent().filter(|p| {
                    matches!(
                        p.kind(),
                        Kind::PropertyAssignment | Kind::ShorthandPropertyAssignment
                    )
                }) && parent.name() == Some(node)
                    && let Some(object) = parent
                        .parent()
                        .filter(|p| p.kind() == Kind::ObjectLiteralExpression)
                    && matches!(node.kind(), Kind::Identifier | Kind::StringLiteral)
                    && let Some(contextual) =
                        ctx.checker.get_contextual_type(object, ContextFlags::None)
                    && let Some(symbol) = ctx.checker.get_property_of_type(contextual, node.text())
                {
                    result.push((node, node, Expected::Symbol(symbol, node)));
                }
            }
            Kind::BinaryExpression
                if node.as_binary_expression().operator_token().kind() == Kind::EqualsToken =>
            {
                let binary = node.as_binary_expression();
                result.push((binary.left(), binary.right(), Expected::Node(binary.left())));
                queue.push_back(binary.right());
                continue;
            }
            Kind::ReturnStatement => {
                if let (Some(value), Some(function)) =
                    (node.expression(), ast::get_containing_function(node))
                    && let Some(expected) = inferred_return(ctx, function)
                {
                    result.push((node, value, Expected::Type(expected)));
                }
            }
            Kind::ArrowFunction => {
                if let Some(body) = node.body().filter(|b| b.kind() != Kind::Block) {
                    let expected = if node.type_parameters().is_empty() {
                        ctx.checker.get_contextual_type(body, ContextFlags::None)
                    } else {
                        inferred_return(ctx, node)
                    };
                    if let Some(expected) = expected {
                        result.push((body, body, Expected::Type(expected)));
                    }
                    body.for_each_child(&mut |child| {
                        queue.push_back(child);
                        false
                    });
                    continue;
                }
            }
            Kind::SatisfiesExpression => {
                if let (Some(value), Some(ty)) = (node.expression(), node.type_node()) {
                    result.push((value, value, Expected::Node(ty)));
                    queue.push_back(value);
                    continue;
                }
            }
            _ => {}
        }
        node.for_each_child(&mut |child| {
            queue.push_back(child);
            false
        });
    }
    result
}

fn check_void_success(ctx: &mut RuleContext<'_>) {
    for (location, value, expected) in assignment_sites(ctx) {
        if ctx.cannot_be_effect_type(value) || !type_candidate(value) {
            continue;
        }
        let real = ctx.ty(value);
        let Some(real_effect) = ctx.effect_type(real) else {
            continue;
        };
        let expected = match expected {
            Expected::Node(node) => ctx.ty(node),
            Expected::Type(ty) => ty,
            Expected::Symbol(symbol, node) => {
                let Some(ty) = ctx
                    .checker
                    .get_type_of_symbol_at_location(symbol, Some(node))
                else {
                    continue;
                };
                ty
            }
        };
        if expected == real {
            continue;
        }
        let Some(expected_effect) = ctx.effect_type(expected) else {
            continue;
        };
        if !expected_effect.a.flags().intersects(TypeFlags::Void) {
            continue;
        }
        if let Some(nested) = first_strict_effect(ctx, real_effect.a) {
            let name = ctx.type_string(nested);
            ctx.emit(Rule::EffectInVoidSuccess, location, 377020, &[name]);
        }
    }
}

fn check_catch(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let callee = node.as_call_expression().expression();
    if !["tryPromise", "try", "tryMap", "tryMapPromise"]
        .iter()
        .any(|name| ctx.is_api(callee, "Effect", name))
    {
        return;
    }
    let signature = ctx.checker.get_resolved_signature_exported(node);
    let Some(&parameter) = signature.parameters().first() else {
        return;
    };
    let Some(ty) = ctx
        .checker
        .get_type_of_symbol_at_location(parameter, Some(node))
    else {
        return;
    };
    let mut unknown = false;
    let mut global = false;
    for object in ctx.union_members(ty) {
        let Some(symbol) = ctx.checker.get_property_of_type(object, "catch") else {
            continue;
        };
        let Some(callback) = ctx
            .checker
            .get_type_of_symbol_at_location(symbol, Some(node))
        else {
            continue;
        };
        let Some(&sig) = ctx
            .checker
            .get_signatures_of_type(callback, SignatureKind::Call)
            .first()
        else {
            continue;
        };
        let result = ctx.checker.get_return_type_of_signature(sig);
        unknown |= result
            .flags()
            .intersects(TypeFlags::Any | TypeFlags::Unknown);
        global |= ctx.is_global_error_type(result);
    }
    if unknown && ctx.enabled(Rule::UnknownInEffectCatch) {
        let name = ctx.text(callee);
        ctx.emit(Rule::UnknownInEffectCatch, callee, 377021, &[name]);
    }
    if global && ctx.enabled(Rule::GlobalErrorInEffectCatch) {
        let name = ctx.text(callee);
        ctx.emit(Rule::GlobalErrorInEffectCatch, callee, 377022, &[name]);
    }
}

fn check_global_error_failure(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let ty = ctx.ty(node);
    if !ctx.is_global_error_type(ty) {
        return;
    }
    let mut parent = node.parent();
    while let Some(ancestor) = parent {
        parent = ancestor.parent();
        if !type_candidate(ancestor) || ctx.cannot_be_effect_type(ancestor) {
            continue;
        }
        let ty = ctx.ty(ancestor);
        let Some(effect) = ctx.effect_type(ty) else {
            continue;
        };
        if ctx
            .union_members(effect.e)
            .into_iter()
            .any(|e| ctx.is_global_error_type(e))
        {
            ctx.emit(Rule::GlobalErrorInEffectFailure, node, 377023, &[]);
        }
        break;
    }
}

fn parse_channels(ctx: &mut RuleContext<'_>, ty: P<Type>) -> Option<Channels> {
    ctx.effect_type(ty)
        .or_else(|| ctx.stream_type(ty))
        .or_else(|| ctx.layer_type(ty))
}

fn check_assertion(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let Some(expr) = node.expression() else {
        return;
    };
    if ctx.cannot_be_effect_type(expr) {
        return;
    }
    let original = ctx.ty(expr);
    let asserted = ctx.ty(node);
    let (Some(original), Some(asserted)) =
        (parse_channels(ctx, original), parse_channels(ctx, asserted))
    else {
        return;
    };
    let mut related = Vec::new();
    for (name, original, asserted) in [
        ("error", original.e, asserted.e),
        ("requirements", original.r, asserted.r),
    ] {
        if !original.flags().intersects(TypeFlags::Any)
            && !ctx.checker.is_type_assignable_to(original, asserted)
        {
            let original_name = ctx.type_string(original);
            let asserted_name = ctx.type_string(asserted);
            related.push(ctx.related(
                ctx.file,
                node.type_node().unwrap_or(node),
                377087,
                &[name.to_string(), original_name, asserted_name],
            ));
        }
    }
    if !related.is_empty() {
        let index = ctx.emit(Rule::UnsafeEffectTypeAssertion, node, 377075, &[]);
        ctx.diagnostics[index].related = related;
    }
}

fn check_any_unknown(ctx: &mut RuleContext<'_>) {
    struct Match {
        node: P<Node>,
        message: String,
        r: TypeFlags,
        e: TypeFlags,
        start: u32,
        end: u32,
    }
    let mut matches: Vec<Match> = Vec::new();
    let mut stack = Vec::new();
    ctx.file.as_node().for_each_child(&mut |child| {
        stack.push(child);
        false
    });
    while let Some(node) = stack.pop() {
        if ast::is_type_node(node)
            || matches!(
                node.kind(),
                Kind::TypeAliasDeclaration | Kind::InterfaceDeclaration
            )
            || (node.kind() == Kind::AsExpression
                && node
                    .type_node()
                    .is_some_and(|t| t.kind() == Kind::AnyKeyword))
        {
            continue;
        }
        if matches!(
            node.kind(),
            Kind::Parameter | Kind::PropertyDeclaration | Kind::VariableDeclaration
        ) && let Some(annotation) = node.type_node()
        {
            let ty = ctx.ty(annotation);
            if ctx.strict_effect_type(ty).is_some() || ctx.layer_type(ty).is_some() {
                continue;
            }
        }
        node.for_each_child(&mut |child| {
            stack.push(child);
            false
        });
        if is_type_equivalent(node) || ctx.cannot_be_effect_type(node) || !type_candidate(node) {
            continue;
        }
        let ty = if node.kind() == Kind::CallExpression {
            let signature = ctx.checker.get_resolved_signature_exported(node);
            ctx.checker.get_return_type_of_signature(signature)
        } else {
            ctx.ty(node)
        };
        let Some(channels) = ctx.strict_effect_type(ty).or_else(|| ctx.layer_type(ty)) else {
            continue;
        };
        let r = channels.r.flags() & (TypeFlags::Any | TypeFlags::Unknown);
        let e = channels.e.flags() & (TypeFlags::Any | TypeFlags::Unknown);
        if r.is_empty() && e.is_empty() {
            continue;
        }
        let mut parts = Vec::new();
        if !r.is_empty() {
            parts.push(format!(
                "{} in the requirements channel",
                if r.intersects(TypeFlags::Any) {
                    "any"
                } else {
                    "unknown"
                }
            ));
        }
        if !e.is_empty() {
            parts.push(format!(
                "{} in the error channel",
                if e.intersects(TypeFlags::Any) {
                    "any"
                } else {
                    "unknown"
                }
            ));
        }
        let mut message = format!("This has {} which is not recommended.", parts.join(" and "));
        if !r.is_empty() {
            message
                .push_str("\nOnly service identifiers should appear in the requirements channel.");
        }
        if !e.is_empty() {
            message.push_str("\nHaving an unknown or any error type is not useful. Consider instead using specific error types baked by Data.TaggedError for example.");
        }
        let start = tsrs_scanner::get_token_pos_of_node(node, ctx.file, false);
        let end = node.end().expect_source("source node");
        matches.retain(|m| {
            !(m.start <= start
                && m.end >= end
                && (m.r.is_empty() || r == m.r)
                && (m.e.is_empty() || e == m.e))
        });
        matches.push(Match {
            node,
            message,
            r,
            e,
            start,
            end,
        });
    }
    for m in matches {
        ctx.emit(Rule::AnyUnknownInErrorContext, m.node, 377030, &[m.message]);
    }
}

fn check_lazy_promise(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let call = node.as_call_expression();
    let Some(&arg) = call.arguments().nodes().first() else {
        return;
    };
    if !ctx.is_api(call.expression(), "Effect", "sync") {
        return;
    }
    let ty = ctx.ty(arg);
    for member in ctx.union_members(ty) {
        for &signature in ctx
            .checker
            .get_signatures_of_type(member, SignatureKind::Call)
        {
            let result = ctx.checker.get_return_type_of_signature(signature);
            if ctx.promise_type(result).is_some() {
                ctx.emit(Rule::LazyPromiseInEffectSync, arg, 377082, &[]);
                return;
            }
        }
    }
}

fn contains_promise(ctx: &mut RuleContext<'_>, ty: P<Type>) -> bool {
    ctx.union_members(ty)
        .into_iter()
        .any(|t| ctx.promise_type(t).is_some())
}

fn explicit_promise_type(ctx: &mut RuleContext<'_>, annotation: Option<P<Node>>) -> bool {
    let Some(annotation) = annotation else {
        return false;
    };
    let ty = ctx.ty(annotation);
    ctx.strict_effect_type(ty)
        .is_some_and(|effect| contains_promise(ctx, effect.a))
}

fn explicit_promise_return(ctx: &mut RuleContext<'_>, function: P<Node>) -> bool {
    if explicit_promise_type(ctx, function.type_node()) {
        return true;
    }
    let mut parent = function.parent();
    while parent.is_some_and(|p| p.kind() == Kind::ParenthesizedExpression) {
        parent = parent.unwrap().parent();
    }
    let Some(annotation) = parent.and_then(|p| p.type_node()) else {
        return false;
    };
    let ty = ctx.ty(annotation);
    for member in ctx.union_members(ty) {
        for &signature in ctx
            .checker
            .get_signatures_of_type(member, SignatureKind::Call)
        {
            let result = ctx.checker.get_return_type_of_signature(signature);
            if ctx
                .strict_effect_type(result)
                .is_some_and(|effect| contains_promise(ctx, effect.a))
            {
                return true;
            }
        }
    }
    false
}

fn explicit_promise_context(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let mut current = Some(node);
    while let Some(node) = current {
        current = node.parent();
        match node.kind() {
            Kind::VariableDeclaration | Kind::PropertyDeclaration | Kind::Parameter => {
                return explicit_promise_type(ctx, node.type_node());
            }
            Kind::AsExpression | Kind::SatisfiesExpression => {
                if explicit_promise_type(ctx, node.type_node()) {
                    return true;
                }
            }
            Kind::ArrowFunction
            | Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::MethodDeclaration => {
                return node.kind() == Kind::ArrowFunction
                    && node.body().is_some_and(|b| b.kind() != Kind::Block)
                    && explicit_promise_return(ctx, node);
            }
            Kind::ReturnStatement => {
                return ast::get_containing_function(node)
                    .is_some_and(|f| explicit_promise_return(ctx, f));
            }
            _ => {}
        }
    }
    false
}

fn explicit_promise_arguments(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let Some(flow) = ctx.longest_piping_flow_at(node, true) else {
        return false;
    };
    let Some(last) = flow.transformations.last() else {
        return false;
    };
    let pipe_rooted = matches!(
        last.kind,
        TransformationKind::Pipe | TransformationKind::Pipeable
    );
    for (i, step) in flow.transformations.iter().enumerate() {
        if step.type_arguments.is_empty() {
            continue;
        }
        let mut callee = ast::skip_parentheses(step.callee);
        if callee.kind() == Kind::CallExpression {
            callee = callee.as_call_expression().expression();
        }
        if ["succeed", "as", "map", "zipWith"]
            .iter()
            .any(|name| ctx.is_api(callee, "Effect", name))
            && (pipe_rooted || i + 1 == flow.transformations.len())
        {
            return true;
        }
    }
    false
}

fn check_promise_success(ctx: &mut RuleContext<'_>) {
    let mut stack = vec![(ctx.file.as_node(), false)];
    let mut matched = HashSet::new();
    while let Some((node, visited)) = stack.pop() {
        if !visited {
            if ast::is_type_node(node) {
                continue;
            }
            stack.push((node, true));
            node.for_each_child(&mut |child| {
                stack.push((child, false));
                false
            });
            continue;
        }
        if matched.contains(&node) {
            if !ast::is_function_like(node)
                && let Some(parent) = node.parent()
            {
                matched.insert(parent);
            }
            continue;
        }
        if !ast::is_expression(node)
            || ast::is_declaration_name(node)
            || is_type_equivalent(node)
            || ctx.cannot_be_effect_type(node)
            || !type_candidate(node)
        {
            continue;
        }
        let ty = if node.kind() == Kind::CallExpression {
            let signature = ctx.checker.get_resolved_signature_exported(node);
            ctx.checker.get_return_type_of_signature(signature)
        } else {
            ctx.ty(node)
        };
        let Some(effect) = ctx.strict_effect_type(ty) else {
            continue;
        };
        if !contains_promise(ctx, effect.a) {
            continue;
        }
        if explicit_promise_context(ctx, node)
            || explicit_promise_arguments(ctx, node)
            || (node.kind() == Kind::CallExpression
                && ctx.is_api(node.as_call_expression().expression(), "Effect", "sync"))
        {
            continue;
        }
        ctx.emit(Rule::PromiseInEffectSuccess, node, 377108, &[]);
        if let Some(parent) = node.parent() {
            matched.insert(parent);
        }
    }
}

fn is_vitest_api(ctx: &mut RuleContext<'_>, node: P<Node>, name: &str) -> bool {
    if ctx.is_package_api(node, "@vitest/runner", name) || ctx.is_package_api(node, "vitest", name)
    {
        return true;
    }
    let node_name = match node.kind() {
        Kind::Identifier => node.text(),
        Kind::PropertyAccessExpression => node.as_property_access_expression().name().text(),
        _ => return false,
    };
    if node_name != name {
        return false;
    }
    let Some(symbol) = ctx.reference_symbol(node) else {
        return false;
    };
    symbol.declarations().iter().any(|&declaration| {
        ast::get_source_file_of_node(declaration).is_some_and(|file| {
            ctx.is_source_file_in_package(file, "vitest")
                || ctx.is_source_file_in_package(file, "@vitest/runner")
        })
    })
}

const HOOKS: &[&str] = &["afterAll", "afterEach", "beforeAll", "beforeEach"];

fn vitest_callback_start(ctx: &mut RuleContext<'_>, mut node: P<Node>) -> Option<usize> {
    let mut members = Vec::new();
    loop {
        node = ast::skip_parentheses(node);
        let mut root = None;
        for name in ["it", "test"].into_iter().chain(HOOKS.iter().copied()) {
            if is_vitest_api(ctx, node, name) {
                root = Some((name, false));
                break;
            }
        }
        if root.is_none() && ctx.is_package_api(node, "@effect/vitest", "it") {
            root = Some(("it", true));
        }
        if let Some((name, effect_vitest)) = root {
            members.reverse();
            if HOOKS.contains(&name) {
                return members.is_empty().then_some(0);
            }
            if effect_vitest
                && members
                    .first()
                    .is_some_and(|s| ["effect", "live", "scoped", "scopedLive"].contains(s))
            {
                return None;
            }
            if members.len() == 1 && HOOKS.contains(&members[0]) {
                return Some(0);
            }
            return members
                .iter()
                .all(|s| {
                    [
                        "concurrent",
                        "each",
                        "fails",
                        "for",
                        "only",
                        "prop",
                        "runIf",
                        "sequential",
                        "skip",
                        "skipIf",
                        "todo",
                    ]
                    .contains(s)
                })
                .then_some(1);
        }
        match node.kind() {
            Kind::PropertyAccessExpression => {
                members.push(node.as_property_access_expression().name().text());
                node = node.as_property_access_expression().expression();
            }
            Kind::CallExpression => node = node.as_call_expression().expression(),
            Kind::TaggedTemplateExpression => node = node.as_tagged_template_expression().tag(),
            _ => return None,
        }
    }
}

fn vitest_return_contains_effect(ctx: &mut RuleContext<'_>, ty: P<Type>, depth: u8) -> bool {
    for member in ctx.union_members(ty) {
        if ctx.strict_effect_type(member).is_some() {
            return true;
        }
        if depth == 0 && ctx.promise_type(member).is_some() {
            for &arg in ctx.checker.get_type_arguments(member) {
                if vitest_return_contains_effect(ctx, arg, depth + 1) {
                    return true;
                }
            }
        }
    }
    false
}

fn check_vitest(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let call = node.as_call_expression();
    let Some(start) = vitest_callback_start(ctx, call.expression()) else {
        return;
    };
    for &callback in call.arguments().nodes().iter().skip(start) {
        let ty = ctx.ty(callback);
        let mut found = false;
        for member in ctx.union_members(ty) {
            for &signature in ctx
                .checker
                .get_signatures_of_type(member, SignatureKind::Call)
            {
                let result = ctx.checker.get_return_type_of_signature(signature);
                found |= vitest_return_contains_effect(ctx, result, 0);
            }
        }
        let lazy = ctx.parse_lazy_expression(callback, LAZY_ALLOW_ASYNC);
        if !found && let Some(lazy) = &lazy {
            let ty = ctx.ty(lazy.expression);
            found = vitest_return_contains_effect(ctx, ty, 0);
        }
        if found {
            ctx.emit(
                Rule::FloatingEffectInVitest,
                lazy.map_or(callback, |lazy| lazy.expression),
                377105,
                &[],
            );
            break;
        }
    }
}

fn check_boolean_conditions(ctx: &mut RuleContext<'_>) {
    let mut queue = VecDeque::new();
    let mut conditions = HashSet::new();
    ctx.file.as_node().for_each_child(&mut |child| {
        queue.push_back(child);
        false
    });
    while let Some(node) = queue.pop_front() {
        node.for_each_child(&mut |child| {
            queue.push_back(child);
            false
        });
        let mut check = Vec::new();
        match node.kind() {
            Kind::IfStatement | Kind::WhileStatement => {
                conditions.insert(node);
                if let Some(expr) = node.expression() {
                    check.push(expr);
                }
            }
            Kind::ConditionalExpression => {
                conditions.insert(node);
                check.push(node.as_conditional_expression().condition());
            }
            Kind::PrefixUnaryExpression
                if node.as_prefix_unary_expression().operator() == Kind::ExclamationToken =>
            {
                conditions.insert(node);
                check.push(node.as_prefix_unary_expression().operand());
            }
            Kind::BinaryExpression => {
                let binary = node.as_binary_expression();
                if matches!(
                    binary.operator_token().kind(),
                    Kind::BarBarToken | Kind::AmpersandAmpersandToken
                ) {
                    if node.parent().is_some_and(|p| conditions.contains(&p)) {
                        conditions.insert(node);
                    }
                    check.extend([binary.left(), binary.right()]);
                }
            }
            _ => {}
        }
        for expr in check {
            if !expr.parent().is_some_and(|p| conditions.contains(&p)) {
                continue;
            }
            let ty = ctx.ty(expr);
            let ty = ctx.checker.get_base_constraint_of_type(ty).unwrap_or(ty);
            let mut types = vec![ty];
            let mut names = HashSet::new();
            while let Some(ty) = types.pop() {
                if ty.flags().intersects(TypeFlags::Union) {
                    types.extend(ctx.union_members(ty));
                    continue;
                }
                if ty
                    .flags()
                    .intersects(TypeFlags::Boolean | TypeFlags::BooleanLiteral | TypeFlags::Never)
                {
                    continue;
                }
                let name = ctx.type_string(ty);
                if names.insert(name.clone()) {
                    ctx.emit(Rule::StrictBooleanExpressions, expr, 377029, &[name]);
                }
            }
        }
    }
}

// Retain the original layer graph's two-pass traversal and partial-child
// removal. Related information only needs its deduplicated leaf providers.
#[derive(Clone)]
struct LayerLeaf {
    node: P<Node>,
    display: P<Node>,
    provides: Vec<P<Type>>,
}

fn layer_info(ctx: &mut RuleContext<'_>, node: P<Node>, in_pipe: bool) -> (LayerLeaf, bool) {
    let display = node
        .parent()
        .filter(|p| {
            matches!(
                p.kind(),
                Kind::VariableDeclaration | Kind::PropertyDeclaration
            ) && p.initializer() == Some(node)
        })
        .and_then(|p| p.name())
        .unwrap_or(node);
    let mut info = LayerLeaf {
        node,
        display,
        provides: Vec::new(),
    };
    let ty = if in_pipe && ast::is_expression(node) {
        ctx.checker
            .get_contextual_type(node, ContextFlags::None)
            .and_then(|t| {
                let signatures = ctx.checker.get_signatures_of_type(t, SignatureKind::Call);
                (signatures.len() == 1)
                    .then(|| ctx.checker.get_return_type_of_signature(signatures[0]))
            })
    } else {
        ctx.safe_ty(node)
    };
    let Some(layer) = ty.and_then(|t| ctx.layer_type(t)) else {
        return (info, false);
    };
    info.provides = ctx
        .union_members(layer.a)
        .into_iter()
        .filter(|&t| {
            !t.flags().intersects(TypeFlags::Never)
                && !ctx.checker.is_type_assignable_to(t, layer.r)
        })
        .collect();
    (info, true)
}

fn simple_reference(node: P<Node>) -> bool {
    node.kind() == Kind::Identifier
        || (node.kind() == Kind::PropertyAccessExpression
            && node.as_property_access_expression().name().kind() == Kind::Identifier
            && simple_reference(node.as_property_access_expression().expression()))
}

#[derive(Default)]
struct ProviderGraph {
    nodes: Vec<Option<LayerLeaf>>,
    indexes: HashMap<P<Node>, usize>,
    edges: HashSet<(usize, usize)>,
}

impl ProviderGraph {
    fn add(&mut self, info: LayerLeaf) -> usize {
        let index = self.nodes.len();
        self.indexes.insert(info.node, index);
        self.nodes.push(Some(info));
        index
    }
    fn index(&self, node: P<Node>) -> Option<usize> {
        self.indexes
            .get(&node)
            .copied()
            .filter(|&index| self.nodes[index].is_some())
    }
    fn remove(&mut self, node: P<Node>) {
        if let Some(index) = self.indexes.remove(&node) {
            self.nodes[index] = None;
            self.edges
                .retain(|&(from, to)| from != index && to != index);
        }
    }
}

fn layer_leaves(ctx: &mut RuleContext<'_>, root: P<Node>) -> Vec<LayerLeaf> {
    let mut graph = ProviderGraph::default();
    let mut visited = HashSet::new();
    let mut in_pipe = HashSet::new();
    let mut budget = HashMap::from([(root, 2u8)]);
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        let depth = budget[&node];
        let pipe = ctx.parse_pipe_call(node);
        if pipe.is_some() || node.kind() == Kind::CallExpression {
            let is_pipe = pipe.is_some();
            let children = if let Some(pipe) = pipe {
                in_pipe.extend(pipe.args.iter().copied());
                std::iter::once(pipe.subject)
                    .chain(pipe.args)
                    .collect::<Vec<_>>()
            } else {
                node.as_call_expression().arguments().nodes().to_vec()
            };
            if visited.insert(node) {
                stack.push(node);
                for &child in &children {
                    budget.insert(child, depth);
                    stack.push(child);
                }
                continue;
            }
            let indexes = children
                .iter()
                .filter_map(|&child| graph.index(child))
                .collect::<Vec<_>>();
            if indexes.len() == children.len() {
                let (info, _) = layer_info(ctx, node, in_pipe.contains(&node));
                if is_pipe {
                    for pair in indexes.windows(2) {
                        graph.edges.insert((pair[1], pair[0]));
                    }
                    let index = graph.add(info);
                    if let Some(&last) = indexes.last() {
                        graph.edges.insert((index, last));
                    }
                } else {
                    let index = graph.add(info);
                    for child in indexes {
                        graph.edges.insert((index, child));
                    }
                }
            } else {
                for child in children {
                    graph.remove(child);
                }
                let (info, is_layer) = layer_info(ctx, node, in_pipe.contains(&node));
                if is_layer {
                    graph.add(info);
                }
            }
            continue;
        }
        if depth > 0
            && simple_reference(node)
            && let Some(symbol) = ctx.symbol(node).map(|symbol| ctx.resolve_symbol(symbol))
            && let [declaration] = symbol.declarations()
        {
            let adjusted = match declaration.kind() {
                Kind::VariableDeclaration | Kind::PropertyDeclaration => declaration.initializer(),
                _ if ast::is_expression(*declaration) => Some(*declaration),
                _ => None,
            };
            if let Some(adjusted) = adjusted {
                if visited.insert(node) {
                    stack.push(node);
                    budget.insert(adjusted, depth - 1);
                    stack.push(adjusted);
                    continue;
                }
                if let Some(child) = graph.index(adjusted) {
                    let (info, _) = layer_info(ctx, node, in_pipe.contains(&node));
                    let index = graph.add(info);
                    graph.edges.insert((index, child));
                    continue;
                }
            }
        }
        if ast::is_expression(node) {
            let (info, is_layer) = layer_info(ctx, node, in_pipe.contains(&node));
            if is_layer {
                graph.add(info);
            }
        }
    }
    graph
        .nodes
        .into_iter()
        .enumerate()
        .filter_map(|(index, node)| {
            if graph.edges.iter().any(|&(from, _)| from == index) {
                None
            } else {
                node
            }
        })
        .collect()
}

fn same_type(ctx: &mut RuleContext<'_>, a: P<Type>, b: P<Type>) -> bool {
    a == b || (ctx.checker.is_type_assignable_to(a, b) && ctx.checker.is_type_assignable_to(b, a))
}

fn missing_context_related(
    ctx: &mut RuleContext<'_>,
    error: P<Node>,
    missing: &[P<Type>],
) -> Vec<RelatedDiagnostic> {
    let mut provide = None;
    for flow in ctx.piping_flows(true) {
        if flow.node.pos() > error.pos() || error.end() > flow.node.end() {
            continue;
        }
        let target = ast::skip_parentheses(error);
        let index = flow.transformations.iter().position(|step| {
            let callee = ast::skip_parentheses(step.callee);
            callee == target || (callee.pos() == target.pos() && target.end() >= callee.end())
        });
        let Some(index) = index else {
            continue;
        };
        for step in flow.transformations[..index].iter().rev() {
            if ctx.is_api(step.callee, "Effect", "provide") {
                provide = step.args.first().map(|&layer| (step.callee, layer));
                break;
            }
        }
        if provide.is_some() {
            break;
        }
    }
    let Some((callee, root)) = provide else {
        return Vec::new();
    };
    let root_type = ctx.ty(root);
    let root_provides = ctx
        .layer_type(root_type)
        .map(|layer| ctx.union_members(layer.a))
        .unwrap_or_default();
    let mut leaves = layer_leaves(ctx, root);
    let mut symbols = HashSet::new();
    leaves.retain(|leaf| {
        ctx.symbol(leaf.node)
            .is_none_or(|symbol| symbols.insert(symbol))
    });
    let mut related = Vec::new();
    let mut seen = HashSet::new();
    for &missing in missing {
        if root_provides
            .iter()
            .any(|&provided| same_type(ctx, provided, missing))
        {
            continue;
        }
        let name = ctx.type_string(missing);
        for leaf in &leaves {
            if leaf
                .provides
                .iter()
                .any(|&provided| same_type(ctx, provided, missing))
                && seen.insert((name.clone(), leaf.display.pos()))
            {
                let file = ast::get_source_file_of_node(leaf.display).unwrap_or(ctx.file);
                related.push(ctx.related(file, leaf.display, 377060, std::slice::from_ref(&name)));
            }
        }
    }
    if !related.is_empty() {
        related.insert(0, ctx.related(ctx.file, callee, 377059, &[]));
    }
    related
}
