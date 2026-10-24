//! Error recovery simplifications, preserving the source rules' type and flow guards.
use std::collections::HashSet;

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node};
use tsrs_checker::{LiteralValue, SignatureKind, Type, TypeFlags};
use tsrs_core::P;

use super::{RuleContext, walk};
use crate::Rule;
use crate::semantic::{
    FlowTransformation, LAZY_THUNK, PipingFlow, ReturningDispatch, unwrap_expression,
};

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    let rules = [
        Rule::CatchUnfailableEffect,
        Rule::CatchDieToOrDie,
        Rule::TimeoutCatchTagToTimeoutOrElse,
        Rule::CatchAllToMapError,
        Rule::CatchRefailToTapError,
        Rule::CatchAllTagDispatchToCatchTag,
        Rule::CatchIfTagToCatchTag,
        Rule::CatchConditionalRefailToCatchIf,
        Rule::CatchTagToCatchReason,
        Rule::CatchToOrElseSucceed,
        Rule::CatchToIgnore,
        Rule::CatchChainToFirstSuccessOf,
        Rule::MultipleCatchTag,
    ];
    if !rules.iter().any(|r| ctx.enabled(*r)) {
        return;
    }
    for flow in ctx.piping_flows(true) {
        for (index, step) in flow.transformations.iter().enumerate() {
            check_step(ctx, &flow, index, step);
        }
        if ctx.effect_version == 4 && ctx.enabled(Rule::TimeoutCatchTagToTimeoutOrElse) {
            check_timeout(ctx, &flow);
        }
        if ctx.enabled(Rule::CatchChainToFirstSuccessOf) {
            check_fallback_chain(ctx, &flow);
        }
        if ctx.enabled(Rule::MultipleCatchTag) {
            check_tag_chain(ctx, &flow);
        }
    }
}

fn effect_api(ctx: &mut RuleContext<'_>, node: P<Node>, name: &str) -> bool {
    ctx.is_api(node, "Effect", name)
}
fn catch_method(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<&'static str> {
    if effect_api(ctx, node, "catch") {
        Some("catch")
    } else if effect_api(ctx, node, "catchAll") {
        Some("catchAll")
    } else {
        None
    }
}
fn input_effect(
    ctx: &mut RuleContext<'_>,
    flow: &PipingFlow,
    i: usize,
) -> Option<crate::semantic::Channels> {
    let ty = flow.input_type(ctx, i)?;
    ctx.strict_effect_type(ty)
}
fn plain_parameter(node: P<Node>) -> Option<P<Node>> {
    if node.kind() != Kind::Parameter {
        return None;
    }
    let p = node.as_parameter_declaration();
    (p.name.kind() == Kind::Identifier
        && p.initializer().is_none()
        && p.dot_dot_dot_token().is_none())
    .then_some(p.name)
}
fn unchanged_parameter(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<P<Node>> {
    let name = plain_parameter(node)?;
    let symbol = ctx.symbol(name)?;
    (!ctx.checker.is_symbol_assigned_exported(symbol)).then_some(name)
}
fn same_parameter(ctx: &mut RuleContext<'_>, node: P<Node>, name: P<Node>) -> bool {
    let node = unwrap_expression(node);
    if node.kind() != Kind::Identifier {
        return false;
    }
    match (ctx.symbol(node), ctx.symbol(name)) {
        (Some(a), Some(b)) => ctx.same_symbol(a, b),
        _ => false,
    }
}
fn contains_parameter(ctx: &mut RuleContext<'_>, node: P<Node>, name: P<Node>) -> bool {
    let mut found = false;
    walk(node, &mut |n| {
        if !found && n.kind() == Kind::Identifier && same_parameter(ctx, n, name) {
            found = true;
        }
        if !found
            && n.kind() == Kind::ShorthandPropertyAssignment
            && let (Some(a), Some(b)) = (
                ctx.checker.get_shorthand_assignment_value_symbol(Some(n)),
                ctx.symbol(name),
            )
        {
            found = ctx.same_symbol(a, b);
        }
    });
    found
}
fn call_parts(node: P<Node>) -> Option<(P<Node>, Vec<P<Node>>)> {
    let node = unwrap_expression(node);
    if node.kind() != Kind::CallExpression {
        return None;
    }
    let call = node.as_call_expression();
    Some((call.expression, call.arguments.nodes().to_vec()))
}
fn wraps_api(ctx: &mut RuleContext<'_>, handler: P<Node>, flags: u8, api: &str) -> bool {
    let Some(lazy) = ctx.parse_lazy_expression(handler, flags) else {
        return false;
    };
    // These two source rules require the returned expression itself to be a call.
    if lazy.expression.kind() != Kind::CallExpression {
        return false;
    }
    let call = lazy.expression.as_call_expression();
    !call.arguments.nodes().is_empty() && effect_api(ctx, call.expression, api)
}
fn effect_expression(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let ty = ctx.ty(node);
    ctx.effect_type(ty).is_some()
}
fn signature_return(ctx: &mut RuleContext<'_>, handler: P<Node>) -> Option<P<Type>> {
    let ty = ctx.ty(handler);
    let signatures = ctx.checker.get_signatures_of_type(ty, SignatureKind::Call);
    if signatures.len() != 1 {
        return None;
    }
    let signature = signatures[0];
    Some(ctx.checker.get_return_type_of_signature(signature))
}
fn literal_string(ty: P<Type>) -> Option<String> {
    if !ty.flags().intersects(TypeFlags::StringLiteral) {
        return None;
    }
    match ty.as_literal_type().value() {
        Some(LiteralValue::String(value)) => Some(value.to_owned()),
        _ => None,
    }
}
fn string_node(node: P<Node>) -> Option<String> {
    let node = unwrap_expression(node);
    (node.kind() == Kind::StringLiteral).then(|| node.text().to_owned())
}
fn union_tags(ctx: &mut RuleContext<'_>, ty: P<Type>) -> Option<HashSet<String>> {
    if !ty.flags().intersects(TypeFlags::Union) {
        return None;
    }
    let mut tags = HashSet::new();
    for member in ctx.union_members(ty) {
        let tag = ctx.checker.get_type_of_property_of_type(member, "_tag")?;
        tags.insert(literal_string(tag)?);
    }
    (!tags.is_empty()).then_some(tags)
}
fn refails(ctx: &mut RuleContext<'_>, node: P<Node>, name: P<Node>, method: &str) -> bool {
    let Some((callee, args)) = call_parts(node) else {
        return false;
    };
    args.len() == 1 && effect_api(ctx, callee, method) && same_parameter(ctx, args[0], name)
}
fn conditional_refails(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    name: P<Node>,
    method: &str,
) -> bool {
    let node = ast::skip_parentheses(node);
    if node.kind() != Kind::CallExpression {
        return false;
    }
    let call = node.as_call_expression();
    let args = call.arguments.nodes();
    if args.len() != 1 || !effect_api(ctx, call.expression, method) {
        return false;
    }
    let argument = ast::skip_parentheses(args[0]);
    argument.kind() == Kind::Identifier && same_parameter(ctx, argument, name)
}
fn void_like(ctx: &mut RuleContext<'_>, ty: P<Type>) -> bool {
    ctx.union_members(ty)
        .iter()
        .all(|t| t.flags().intersects(TypeFlags::VoidLike | TypeFlags::Never))
}

fn check_step(
    ctx: &mut RuleContext<'_>,
    flow: &PipingFlow,
    index: usize,
    step: &FlowTransformation,
) {
    if ctx.enabled(Rule::CatchUnfailableEffect)
        && [
            "catch",
            "catchAll",
            "catchIf",
            "catchSome",
            "catchTag",
            "catchTags",
        ]
        .iter()
        .any(|name| effect_api(ctx, step.callee, name))
        && let Some(ty) = flow.input_type(ctx, index)
        && ctx
            .effect_type(ty)
            .is_some_and(|e| e.e.flags().intersects(TypeFlags::Never))
    {
        ctx.emit(Rule::CatchUnfailableEffect, step.callee, 377009, &[]);
    }
    let method = catch_method(ctx, step.callee);
    if let Some(method) = method
        && let Some(&handler) = step.args.first()
    {
        if ctx.enabled(Rule::CatchAllToMapError) && wraps_api(ctx, handler, 0, "fail") {
            ctx.emit(
                Rule::CatchAllToMapError,
                step.callee,
                377010,
                &[callee_name(step.callee, "catch")],
            );
        }
        if ctx.enabled(Rule::CatchToOrElseSucceed) && wraps_api(ctx, handler, LAZY_THUNK, "succeed")
        {
            ctx.emit(
                Rule::CatchToOrElseSucceed,
                step.callee,
                377095,
                &[callee_name(step.callee, "catch")],
            );
        }
        if step.args.len() == 1 {
            if ctx.enabled(Rule::CatchDieToOrDie)
                && method
                    == if ctx.effect_version == 4 {
                        "catch"
                    } else {
                        "catchAll"
                    }
            {
                let target = ctx.unwrap_identity_forwarder(handler).target;
                if effect_api(ctx, target, "die")
                    && input_effect(ctx, flow, index)
                        .is_some_and(|e| !e.e.flags().intersects(TypeFlags::Never))
                {
                    ctx.emit(
                        Rule::CatchDieToOrDie,
                        step.callee,
                        377115,
                        &[method.to_owned()],
                    );
                }
            }
            if ctx.effect_version == 4
                && ctx.enabled(Rule::CatchRefailToTapError)
                && method == "catch"
                && input_effect(ctx, flow, index)
                    .is_some_and(|e| !e.e.flags().intersects(TypeFlags::Never))
                && observation_refail(ctx, handler)
            {
                ctx.emit(Rule::CatchRefailToTapError, step.callee, 377133, &[]);
            }
            if ctx.enabled(Rule::CatchAllTagDispatchToCatchTag)
                && let Some(name) = tag_dispatch(ctx, handler, false)
            {
                ctx.emit(
                    Rule::CatchAllTagDispatchToCatchTag,
                    step.callee,
                    377122,
                    &[name, method.to_owned()],
                );
            }
        }
    }
    if ctx.enabled(Rule::CatchIfTagToCatchTag)
        && step.args.len() == 2
        && effect_api(ctx, step.callee, "catchIf")
        && catch_if_tag(ctx, step.args[0])
    {
        ctx.emit(Rule::CatchIfTagToCatchTag, step.callee, 377131, &[]);
    }
    if ctx.effect_version == 4
        && ctx.enabled(Rule::CatchConditionalRefailToCatchIf)
        && step.args.len() == 1
        && input_effect(ctx, flow, index).is_some()
    {
        let names = if effect_api(ctx, step.callee, "catch") {
            Some(("catch", "fail", "catchIf"))
        } else if effect_api(ctx, step.callee, "catchCause") {
            Some(("catchCause", "failCause", "catchCauseIf"))
        } else {
            None
        };
        if let Some((catch, fail, preferred)) = names
            && conditional_refail(ctx, step.args[0], catch, fail)
        {
            ctx.emit(
                Rule::CatchConditionalRefailToCatchIf,
                step.callee,
                377116,
                &[catch.to_owned(), fail.to_owned(), preferred.to_owned()],
            );
        }
    }
    if ctx.effect_version == 4 && ctx.enabled(Rule::CatchToIgnore) && !step.args.is_empty() {
        let names = if effect_api(ctx, step.callee, "catch") {
            Some(("catch", "ignore"))
        } else if effect_api(ctx, step.callee, "catchCause") {
            Some(("catchCause", "ignoreCause"))
        } else {
            None
        };
        if let Some((catch, ignore)) = names
            && let Some(lazy) = ctx.parse_lazy_expression(step.args[0], 0)
            && effect_api(ctx, unwrap_expression(lazy.expression), "void")
            && let Some(ty) = step.out_type(ctx)
            && let Some(effect) = ctx.strict_effect_type(ty)
            && void_like(ctx, effect.a)
        {
            ctx.emit(
                Rule::CatchToIgnore,
                step.callee,
                377099,
                &[catch.to_owned(), ignore.to_owned()],
            );
        }
    }
    if ctx.enabled(Rule::CatchTagToCatchReason) {
        let candidate = if effect_api(ctx, step.callee, "catchTag")
            && step.args.len() == 2
            && string_node(step.args[0]).is_some()
        {
            tag_dispatch(ctx, step.args[1], true).map(|name| (name, "catchTag"))
        } else if effect_api(ctx, step.callee, "catchTags") && step.args.len() == 1 {
            reason_cases(ctx, step.args[0]).map(|name| (name, "catchTags"))
        } else {
            None
        };
        if let Some((name, method)) = candidate {
            ctx.emit(
                Rule::CatchTagToCatchReason,
                step.callee,
                377110,
                &[name, method.to_owned()],
            );
        }
    }
}
fn callee_name(callee: P<Node>, fallback: &str) -> String {
    if callee.kind() == Kind::PropertyAccessExpression {
        callee
            .as_property_access_expression()
            .name()
            .text()
            .to_owned()
    } else {
        fallback.to_owned()
    }
}
fn observation_refail(ctx: &mut RuleContext<'_>, handler: P<Node>) -> bool {
    let Some(lazy) = ctx.parse_lazy_expression(handler, 0) else {
        return false;
    };
    if lazy.params.len() != 1 {
        return false;
    }
    let Some(name) = unchanged_parameter(ctx, lazy.params[0]) else {
        return false;
    };
    let Some(flow) = ctx.longest_piping_flow_at(lazy.expression, false) else {
        return false;
    };
    let Some(last) = flow.transformations.len().checked_sub(1) else {
        return false;
    };
    let step = &flow.transformations[last];
    if step.args.len() != 1 || input_effect(ctx, &flow, last).is_none() {
        return false;
    }
    let mut result = step.args[0];
    if effect_api(ctx, step.callee, "andThen") {
        if let Some(thunk) = ctx.parse_lazy_expression(result, LAZY_THUNK) {
            result = thunk.expression;
        }
    } else if effect_api(ctx, step.callee, "flatMap") {
        let Some(thunk) = ctx.parse_lazy_expression(result, LAZY_THUNK) else {
            return false;
        };
        result = thunk.expression;
    } else {
        return false;
    }
    let Some(flow) = ctx.longest_piping_flow_at(result, false) else {
        return false;
    };
    flow.transformations.len() == 1
        && flow.transformations[0].args.is_empty()
        && effect_api(ctx, flow.transformations[0].callee, "fail")
        && same_parameter(ctx, flow.subject, name)
}
fn catch_if_tag(ctx: &mut RuleContext<'_>, handler: P<Node>) -> bool {
    let Some(lazy) = ctx.parse_lazy_expression(handler, 0) else {
        return false;
    };
    if lazy.params.len() != 1 {
        return false;
    }
    let Some(name) = unchanged_parameter(ctx, lazy.params[0]) else {
        return false;
    };
    let Some((subject, tag)) = ctx.parse_tag_match(lazy.expression) else {
        return false;
    };
    if !same_parameter(ctx, subject, name) {
        return false;
    }
    let Some(tag) = string_node(tag) else {
        return false;
    };
    let ty = ctx.ty(name);
    union_tags(ctx, ty).is_some_and(|tags| tags.contains(&tag))
}
fn reason_root(ctx: &mut RuleContext<'_>, subject: P<Node>, name: P<Node>) -> Option<P<Node>> {
    let subject = unwrap_expression(subject);
    if subject.kind() != Kind::PropertyAccessExpression {
        return None;
    }
    let access = subject.as_property_access_expression();
    let root = unwrap_expression(access.expression);
    (access.name.text() == "reason" && same_parameter(ctx, root, name)).then_some(root)
}
fn tag_dispatch(ctx: &mut RuleContext<'_>, handler: P<Node>, reason: bool) -> Option<String> {
    let returning = ctx.parse_returning_dispatch(handler)?;
    if returning.params.len() != 1 || returning.dispatch.branches.is_empty() {
        return None;
    }
    let name = returning.params[0].name()?;
    if name.kind() != Kind::Identifier || ctx.symbol(name).is_none() {
        return None;
    }
    let fallback = returning.dispatch.fallback?;
    let mut ty = ctx.ty(name);
    if reason {
        ty = ctx.checker.get_type_of_property_of_type(ty, "reason")?;
    }
    let tags = union_tags(ctx, ty)?;
    let subject = ctx.common_tag_subject(&returning.dispatch)?;
    if reason {
        reason_root(ctx, subject, name)?;
    } else if !same_parameter(ctx, subject, name) {
        return None;
    }
    let mut seen = HashSet::new();
    let mut allowed = HashSet::new();
    for branch in &returning.dispatch.branches {
        let tag = string_node(branch.condition.tag_value?)?;
        if !tags.contains(&tag) || !seen.insert(tag) || !effect_expression(ctx, branch.result) {
            return None;
        }
        if reason {
            allowed.insert(reason_root(ctx, branch.condition.tag_subject?, name)?);
        }
    }
    if !refails(ctx, fallback, name, "fail") {
        return None;
    }
    if reason {
        allowed.insert(unwrap_expression(call_parts(fallback)?.1[0]));
        if !valid_reason_uses(ctx, &returning, name, &allowed) {
            return None;
        }
    }
    Some(name.text().to_owned())
}
fn valid_reason_uses(
    ctx: &mut RuleContext<'_>,
    returning: &ReturningDispatch,
    name: P<Node>,
    allowed: &HashSet<P<Node>>,
) -> bool {
    let mut valid = true;
    walk(returning.body, &mut |node| {
        if valid
            && node.kind() == Kind::Identifier
            && same_parameter(ctx, node, name)
            && !allowed.contains(&node)
        {
            valid = returning
                .dispatch
                .branches
                .iter()
                .any(|b| node.pos() >= b.result.pos() && node.end() <= b.result.end());
        }
    });
    valid
}
fn reason_cases(ctx: &mut RuleContext<'_>, cases: P<Node>) -> Option<String> {
    let cases = unwrap_expression(cases);
    if cases.kind() != Kind::ObjectLiteralExpression {
        return None;
    }
    for property in cases.as_object_literal_expression().properties.nodes() {
        if property.kind() != Kind::PropertyAssignment {
            continue;
        }
        let p = property.as_property_assignment();
        if !matches!(p.name().kind(), Kind::Identifier | Kind::StringLiteral) {
            continue;
        }
        if let Some(name) = tag_dispatch(ctx, p.initializer(), true) {
            return Some(name);
        }
    }
    None
}
fn rooted_tag(ctx: &mut RuleContext<'_>, subject: P<Node>, name: P<Node>) -> bool {
    let mut root = unwrap_expression(subject);
    while root.kind() == Kind::PropertyAccessExpression {
        root = unwrap_expression(root.as_property_access_expression().expression);
    }
    if !same_parameter(ctx, root, name) {
        return false;
    }
    let ty = ctx.ty(subject);
    ctx.union_members(ty).iter().any(|t| {
        ctx.checker
            .get_type_of_property_of_type(*t, "_tag")
            .is_some()
    })
}
fn conditional_refail(
    ctx: &mut RuleContext<'_>,
    handler: P<Node>,
    catch: &str,
    fail: &str,
) -> bool {
    let Some(returning) = ctx.parse_returning_dispatch(handler) else {
        return false;
    };
    if returning.params.len() != 1 || returning.dispatch.branches.len() != 1 {
        return false;
    }
    let Some(name) = unchanged_parameter(ctx, returning.params[0]) else {
        return false;
    };
    let Some(fallback) = returning.dispatch.fallback else {
        return false;
    };
    let branch = &returning.dispatch.branches[0];
    let a = conditional_refails(ctx, branch.result, name, fail);
    let b = conditional_refails(ctx, fallback, name, fail);
    if a == b {
        return false;
    }
    let is_tag = if let Some(subject) = ctx.common_tag_subject(&returning.dispatch) {
        if branch.condition.tag_value.and_then(string_node).is_some()
            && rooted_tag(ctx, subject, name)
        {
            if !a && catch == "catch" && same_parameter(ctx, subject, name) {
                return false;
            }
            true
        } else {
            false
        }
    } else {
        false
    };
    if !is_tag && !conditional_predicate(ctx, branch.condition.subject, name) {
        return false;
    }
    effect_expression(ctx, if a { fallback } else { branch.result })
}
fn conditional_predicate(ctx: &mut RuleContext<'_>, node: P<Node>, name: P<Node>) -> bool {
    let node = unwrap_expression(node);
    match node.kind() {
        Kind::CallExpression
        | Kind::PropertyAccessExpression
        | Kind::ElementAccessExpression
        | Kind::TypeOfExpression => contains_parameter(ctx, node, name),
        Kind::PrefixUnaryExpression => {
            let p = node.as_prefix_unary_expression();
            p.operator == Kind::ExclamationToken && conditional_predicate(ctx, p.operand, name)
        }
        Kind::BinaryExpression => {
            let b = node.as_binary_expression();
            match b.operator_token.kind() {
                Kind::AmpersandAmpersandToken | Kind::BarBarToken => {
                    conditional_predicate(ctx, b.left, name)
                        || conditional_predicate(ctx, b.right(), name)
                }
                Kind::InstanceOfKeyword => contains_parameter(ctx, b.left, name),
                Kind::InKeyword => contains_parameter(ctx, b.right(), name),
                Kind::EqualsEqualsToken
                | Kind::EqualsEqualsEqualsToken
                | Kind::ExclamationEqualsToken
                | Kind::ExclamationEqualsEqualsToken
                | Kind::LessThanToken
                | Kind::LessThanEqualsToken
                | Kind::GreaterThanToken
                | Kind::GreaterThanEqualsToken => contains_parameter(ctx, node, name),
                _ => false,
            }
        }
        _ => false,
    }
}

fn check_timeout(ctx: &mut RuleContext<'_>, flow: &PipingFlow) {
    let steps = &flow.transformations;
    for (i, timeout) in steps.iter().enumerate() {
        if timeout.args.len() != 1 || !effect_api(ctx, timeout.callee, "timeout") {
            continue;
        }
        let Some(next) = steps.get(i + 1) else {
            continue;
        };
        let option = (next.args.is_empty() && effect_api(ctx, next.callee, "asSome"))
            || (next.args.len() == 1
                && effect_api(ctx, next.callee, "map")
                && ctx.is_api(next.args[0], "Option", "some"));
        let end = i + if option { 2 } else { 1 };
        let Some(catch) = steps.get(end) else {
            continue;
        };
        if catch.args.len() != 2
            || !effect_api(ctx, catch.callee, "catchTag")
            || ast::skip_parentheses(catch.args[0]).kind() != Kind::StringLiteral
            || ast::skip_parentheses(catch.args[0]).text() != "TimeoutError"
            || steps[i..=end].iter().any(|s| !s.type_arguments.is_empty())
            || !timeout_ignores_error(ctx, catch.args[1])
            || option && !timeout_returns_none(ctx, catch.args[1])
        {
            continue;
        }
        let Some(input) = input_effect(ctx, flow, i) else {
            continue;
        };
        if timeout_excluded(ctx, input.e) {
            ctx.emit(
                Rule::TimeoutCatchTagToTimeoutOrElse,
                catch.callee,
                377127,
                &[if option {
                    "timeoutOption"
                } else {
                    "timeoutOrElse"
                }
                .to_owned()],
            );
        }
    }
}
fn timeout_ignores_error(ctx: &mut RuleContext<'_>, handler: P<Node>) -> bool {
    let handler = ast::skip_parentheses(handler);
    if handler.kind() != Kind::ArrowFunction
        || ast::get_combined_modifier_flags(handler).intersects(ModifierFlags::Async)
    {
        return false;
    }
    let Some(data) = handler.function_like_data() else {
        return false;
    };
    if data
        .type_parameters
        .get()
        .is_some_and(|p| !p.nodes().is_empty())
    {
        return false;
    }
    let params = handler.parameters();
    if params.is_empty() {
        return true;
    }
    if params.len() != 1 {
        return false;
    }
    let Some(name) = plain_parameter(params[0]) else {
        return false;
    };
    if ctx.symbol(name).is_none() {
        return false;
    }
    if handler
        .body()
        .is_some_and(|body| contains_parameter(ctx, body, name))
    {
        return false;
    }
    !handler
        .type_node()
        .is_some_and(|ty| contains_parameter(ctx, ty, name))
}
fn timeout_excluded(ctx: &mut RuleContext<'_>, error: P<Type>) -> bool {
    if error.flags().intersects(TypeFlags::Never) {
        return true;
    }
    for member in ctx.union_members(error) {
        let Some(tag) = ctx.checker.get_type_of_property_of_type(member, "_tag") else {
            return false;
        };
        for value in ctx.union_members(tag) {
            let Some(text) = literal_string(value) else {
                return false;
            };
            if text == "TimeoutError" {
                return false;
            }
        }
    }
    true
}
fn timeout_returns_none(ctx: &mut RuleContext<'_>, handler: P<Node>) -> bool {
    let Some(lazy) = ctx.parse_lazy_expression(handler, 0) else {
        return false;
    };
    let Some(flow) = ctx.longest_piping_flow_at(lazy.expression, false) else {
        return false;
    };
    if flow.transformations.is_empty() {
        return effect_api(ctx, flow.subject, "succeedNone");
    }
    if flow.transformations.len() != 1 {
        return false;
    }
    let step = &flow.transformations[0];
    if !step.args.is_empty()
        || !step.type_arguments.is_empty()
        || !effect_api(ctx, step.callee, "succeed")
    {
        return false;
    }
    let Some((callee, args)) = call_parts(flow.subject) else {
        return false;
    };
    let call = unwrap_expression(flow.subject).as_call_expression();
    args.is_empty()
        && call
            .type_arguments()
            .is_none_or(|args| args.nodes().is_empty())
        && ctx.is_api(callee, "Option", "none")
}
fn check_fallback_chain(ctx: &mut RuleContext<'_>, flow: &PipingFlow) {
    let mut chain: Vec<(P<Node>, P<Type>)> = Vec::new();
    let mut initial = None;
    let mut output = None;
    for (i, step) in flow.transformations.iter().enumerate() {
        let candidate = fallback_error(ctx, step);
        let Some(error) = candidate else {
            flush_fallback(ctx, &chain, initial, output);
            chain.clear();
            initial = None;
            output = None;
            continue;
        };
        if chain.is_empty() {
            initial = input_effect(ctx, flow, i).map(|e| e.e);
            if initial.is_none() {
                continue;
            }
        }
        let next = step.out_type(ctx).and_then(|ty| ctx.strict_effect_type(ty));
        let Some(next) = next else {
            flush_fallback(ctx, &chain, initial, output);
            chain.clear();
            initial = None;
            output = None;
            continue;
        };
        chain.push((step.callee, error));
        output = Some(next.e);
    }
    flush_fallback(ctx, &chain, initial, output);
}
fn fallback_error(ctx: &mut RuleContext<'_>, step: &FlowTransformation) -> Option<P<Type>> {
    if step.args.len() != 1 || !effect_api(ctx, step.callee, "catch") {
        return None;
    }
    ctx.parse_lazy_expression(step.args[0], LAZY_THUNK)?;
    let ty = signature_return(ctx, step.args[0])?;
    Some(ctx.strict_effect_type(ty)?.e)
}
fn flush_fallback(
    ctx: &mut RuleContext<'_>,
    chain: &[(P<Node>, P<Type>)],
    initial: Option<P<Type>>,
    output: Option<P<Type>>,
) {
    if chain.len() < 2 {
        return;
    }
    let (Some(initial), Some(output)) = (initial, output) else {
        return;
    };
    let (callee, last) = *chain.last().unwrap();
    if [initial, output, last]
        .iter()
        .any(|t| t.flags().intersects(TypeFlags::Any))
        || !ctx.checker.is_type_assignable_to(last, output)
        || !ctx.checker.is_type_assignable_to(output, last)
        || !ctx.checker.is_type_assignable_to(initial, output)
    {
        return;
    }
    for (_, error) in &chain[..chain.len() - 1] {
        if error.flags().intersects(TypeFlags::Any)
            || !ctx.checker.is_type_assignable_to(*error, output)
        {
            return;
        }
    }
    ctx.emit(Rule::CatchChainToFirstSuccessOf, callee, 377107, &[]);
}
fn check_tag_chain(ctx: &mut RuleContext<'_>, flow: &PipingFlow) {
    let mut chain = Vec::new();
    let mut introduced = Vec::new();
    for step in &flow.transformations {
        let Some((handled, added)) = tag_candidate(ctx, step) else {
            flush_tags(ctx, &chain);
            chain.clear();
            introduced.clear();
            continue;
        };
        let overlap = introduced.iter().copied().any(|prior| {
            ctx.checker.is_type_assignable_to(handled, prior)
                && ctx.checker.is_type_assignable_to(prior, handled)
        });
        if overlap {
            flush_tags(ctx, &chain);
            chain.clear();
            introduced.clear();
        }
        chain.push(step.callee);
        introduced.extend(added);
    }
    flush_tags(ctx, &chain);
}
fn tag_candidate(
    ctx: &mut RuleContext<'_>,
    step: &FlowTransformation,
) -> Option<(P<Type>, Vec<P<Type>>)> {
    if step.args.len() != 2 || !ctx.is_package_api(step.callee, "effect", "catchTag") {
        return None;
    }
    let tag = unwrap_expression(step.args[0]);
    if tag.kind() != Kind::StringLiteral {
        return None;
    }
    let handled = ctx.ty(tag);
    let ty = signature_return(ctx, step.args[1])?;
    let error = ctx.effect_type(ty).or_else(|| ctx.stream_type(ty))?.e;
    let mut added = Vec::new();
    for member in ctx.union_members(error) {
        if member.flags().intersects(TypeFlags::Never) {
            continue;
        }
        if let Some(tag) = ctx.checker.get_type_of_property_of_type(member, "_tag") {
            added.push(tag);
        }
    }
    Some((handled, added))
}
fn flush_tags(ctx: &mut RuleContext<'_>, chain: &[P<Node>]) {
    if chain.len() < 2 {
        return;
    }
    let index = ctx.emit(
        Rule::MultipleCatchTag,
        chain[0],
        377092,
        &[chain.len().to_string()],
    );
    for node in &chain[1..] {
        let related = ctx.related(ctx.file, *node, 377093, &[]);
        ctx.diagnostics[index].related.push(related);
    }
}
