use std::collections::{HashMap, HashSet};

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node, NodeFlags, Symbol, SymbolFlags};
use tsrs_checker::{ContextFlags, SignatureKind, Type, TypeFlags, TypeFormatFlags};
use tsrs_core::{P, TextRange};

use super::{RuleContext, walk};
use crate::{
    Rule,
    semantic::{TransformationKind, unwrap_expression},
};

#[derive(Clone)]
struct FunctionCall {
    function: P<Node>,
    options: Option<P<Node>>,
    module: Option<P<Node>>,
    variant: &'static str,
    trace: Option<P<Node>>,
    pipes: Vec<P<Node>>,
}

fn parse_function_call(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    is_gen: bool,
) -> Option<FunctionCall> {
    if node.kind() != Kind::CallExpression {
        return None;
    }
    let args = node.arguments();
    let first = *args.first()?;
    let options =
        (!matches!(first.kind(), Kind::ArrowFunction | Kind::FunctionExpression)).then_some(first);
    let start = usize::from(options.is_some());
    let index = (start..args.len()).find(|&i| {
        matches!(
            args[i].kind(),
            Kind::ArrowFunction | Kind::FunctionExpression
        )
    })?;
    let function = args[index];
    let mut callee = node.as_call_expression().expression();
    let mut trace = None;
    if !is_gen && callee.kind() == Kind::CallExpression {
        trace = callee.arguments().first().copied();
        callee = callee.as_call_expression().expression();
    }
    let variants: &[&'static str] = if is_gen {
        &["gen"]
    } else {
        &["fn", "fnUntraced", "fnUntracedEager"]
    };
    let variant = variants
        .iter()
        .copied()
        .find(|v| ctx.is_api(callee, "Effect", v))?;
    if trace.is_some() && variant != "fn" {
        return None;
    }
    if is_gen
        && (function.kind() != Kind::FunctionExpression
            || function.as_function_expression().asterisk_token().is_none())
    {
        return None;
    }
    Some(FunctionCall {
        function,
        options,
        module: (callee.kind() == Kind::PropertyAccessExpression)
            .then(|| callee.as_property_access_expression().expression()),
        variant,
        trace,
        pipes: args[index + 1..].to_vec(),
    })
}

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::MissingReturnYieldStar,
        Rule::MissingStarInYieldEffectGen,
        Rule::TryCatchInEffectGen,
        Rule::ReturnEffectInGen,
        Rule::EffectFnIife,
        Rule::UnnecessaryEffectGen,
        Rule::EffectGenUsesAdapter,
        Rule::EffectFnImplicitAny,
        Rule::NestedEffectGenYield,
        Rule::EffectFnOpportunity,
        Rule::RunEffectInsideEffect,
        Rule::RedundantMapError,
        Rule::RedundantOrDie,
        Rule::UnnecessaryArrowBlock,
        Rule::UnnecessaryTypeofType,
        Rule::MissingPipeableSignature,
        Rule::MissedPipeableOpportunity,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    let mut nodes = Vec::new();
    walk(ctx.file.as_node(), &mut |n| nodes.push(n));
    for node in nodes.iter().copied() {
        match node.kind() {
            Kind::ExpressionStatement if ctx.enabled(Rule::MissingReturnYieldStar) => {
                let value = unwrap_expression(node.as_expression_statement().expression());
                if value.kind() == Kind::YieldExpression
                    && value.as_yield_expression().asterisk_token.is_some()
                    && ctx.effect_context(node) & 1 != 0
                    && let Some(expr) = value.as_yield_expression().expression
                {
                    let ty = ctx.ty(expr);
                    if ctx
                        .effect_yieldable_type(ty)
                        .is_some_and(|t| t.a.flags().intersects(TypeFlags::Never))
                    {
                        ctx.emit(Rule::MissingReturnYieldStar, value, 377006, &[]);
                    }
                }
            }
            Kind::YieldExpression => {
                let y = node.as_yield_expression();
                if let Some(expression) = y.expression
                    && ctx.effect_context(node) & 1 != 0
                {
                    if y.asterisk_token.is_none()
                        && ctx.enabled(Rule::MissingStarInYieldEffectGen)
                        && let Some(generator) = ctx.yield_generator(node)
                    {
                        let related = ctx.related(ctx.file, generator, 377007, &[]);
                        let i = ctx.emit(Rule::MissingStarInYieldEffectGen, node, 377008, &[]);
                        ctx.diagnostics[i].related.push(related);
                    }
                    if y.asterisk_token.is_some()
                        && ctx.enabled(Rule::NestedEffectGenYield)
                        && parse_function_call(ctx, expression, true).is_some()
                    {
                        ctx.emit(Rule::NestedEffectGenYield, expression, 377083, &[]);
                    }
                }
            }
            Kind::TryStatement if ctx.enabled(Rule::TryCatchInEffectGen) => {
                if node.as_try_statement().catch_clause.is_some()
                    && ctx.effect_context(node) & 1 != 0
                {
                    ctx.emit(Rule::TryCatchInEffectGen, node, 377012, &[]);
                }
            }
            Kind::ReturnStatement if ctx.enabled(Rule::ReturnEffectInGen) => {
                if let Some(expression) = node.as_return_statement().expression()
                    && expression.kind() != Kind::YieldExpression
                    && ctx.effect_context(node) & 1 != 0
                {
                    let ty = ctx.ty(expression);
                    if ctx.strict_effect_type(ty).is_some() {
                        ctx.emit(Rule::ReturnEffectInGen, node, 377014, &[]);
                    }
                }
            }
            Kind::CallExpression => check_call(ctx, node),
            Kind::ArrowFunction if ctx.enabled(Rule::UnnecessaryArrowBlock) => {
                if let Some(body) = node.body()
                    && single_return(body).is_some()
                {
                    ctx.emit(Rule::UnnecessaryArrowBlock, body, 377084, &[]);
                }
            }
            Kind::TypeQuery if ctx.enabled(Rule::UnnecessaryTypeofType) => check_typeof(ctx, node),
            _ => {}
        }
        if ctx.enabled(Rule::EffectFnOpportunity)
            && matches!(
                node.kind(),
                Kind::ArrowFunction | Kind::FunctionExpression | Kind::FunctionDeclaration
            )
        {
            check_opportunity(ctx, node);
        }
    }
    if ctx.enabled(Rule::RedundantMapError) {
        check_redundant(ctx, &nodes, true);
    }
    if ctx.enabled(Rule::RedundantOrDie) {
        check_redundant(ctx, &nodes, false);
    }
    if ctx.enabled(Rule::MissedPipeableOpportunity) {
        check_missed_pipeable(ctx);
    }
    if ctx.enabled(Rule::MissingPipeableSignature) {
        check_missing_pipeable(ctx);
    }
}

fn check_call(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if ctx.enabled(Rule::EffectFnIife) {
        let inner = node.as_call_expression().expression();
        if let Some(parsed) = parse_function_call(ctx, inner, false) {
            let module = parsed
                .module
                .filter(|m| m.kind() == Kind::Identifier)
                .map(|m| ctx.text(m))
                .unwrap_or_else(|| "Effect".into());
            let hint = parsed
                .trace
                .map(|t| {
                    format!(
                        " with Effect.withSpan({}) piped in the end to maintain tracing spans",
                        raw_text(ctx, t)
                    )
                })
                .unwrap_or_default();
            ctx.emit(
                Rule::EffectFnIife,
                node,
                377011,
                &[module, parsed.variant.into(), hint],
            );
        }
    }
    if (ctx.enabled(Rule::UnnecessaryEffectGen) || ctx.enabled(Rule::EffectGenUsesAdapter))
        && let Some(parsed) = parse_function_call(ctx, node, true)
    {
        if ctx.enabled(Rule::EffectGenUsesAdapter)
            && let Some(param) = parsed.function.parameters().first()
        {
            ctx.emit(Rule::EffectGenUsesAdapter, *param, 377027, &[]);
        }
        if ctx.enabled(Rule::UnnecessaryEffectGen)
            && node.arguments().len() == 1
            && let Some(body) = parsed.function.body()
            && body.kind() == Kind::Block
            && body.statements().len() == 1
        {
            let stmt = body.statements()[0];
            let expression = match stmt.kind() {
                Kind::ReturnStatement => stmt.as_return_statement().expression(),
                Kind::ExpressionStatement => Some(stmt.as_expression_statement().expression()),
                _ => None,
            };
            if let Some(expression) = expression
                && expression.kind() == Kind::YieldExpression
                && expression.as_yield_expression().asterisk_token.is_some()
                && let Some(value) = expression.as_yield_expression().expression
                && !contains_yield_star(value)
            {
                ctx.emit(Rule::UnnecessaryEffectGen, node, 377017, &[]);
            }
        }
    }
    if ctx.enabled(Rule::EffectFnImplicitAny)
        && let Some(parsed) = parse_function_call(ctx, node, false)
    {
        let contextual = ctx
            .checker
            .get_contextual_type_exported(node, ContextFlags::None);
        let has_context = contextual.is_some_and(|ty| {
            ctx.union_members(ty).iter().any(|t| {
                !ctx.checker
                    .get_signatures_of_type(*t, SignatureKind::Call)
                    .is_empty()
            })
        });
        if !has_context {
            for param in parsed.function.parameters() {
                if param.type_node().is_none()
                    && param.as_parameter_declaration().initializer().is_none()
                    && let Some(name) = param.name()
                {
                    ctx.emit(Rule::EffectFnImplicitAny, name, 377062, &[ctx.text(name)]);
                }
            }
        }
    }
    if ctx.enabled(Rule::RunEffectInsideEffect) && !node.arguments().is_empty() {
        let callee = node.as_call_expression().expression();
        if let Some(method) = [
            "runSync",
            "runSyncExit",
            "runPromise",
            "runPromiseExit",
            "runFork",
            "runCallback",
        ]
        .iter()
        .copied()
        .find(|name| ctx.is_api(callee, "Effect", name))
        {
            let mut current = Some(node);
            let mut generator = None;
            while let Some(n) = current {
                if ctx.effect_context(n) & 1 != 0 {
                    generator = ctx.yield_generator(n);
                    if generator.is_some() {
                        break;
                    }
                }
                current = n.parent();
            }
            if let Some(generator) = generator
                && generator
                    .body()
                    .is_some_and(|b| b.kind() == Kind::Block && !b.statements().is_empty())
            {
                let nested = ast::get_containing_function(node) != Some(generator);
                let code = if !nested {
                    377024
                } else if ctx.effect_version == 4 {
                    377074
                } else {
                    377025
                };
                ctx.emit(
                    Rule::RunEffectInsideEffect,
                    callee,
                    code,
                    &[ctx.text(callee), method.into()],
                );
            }
        }
    }
}

fn single_return(body: P<Node>) -> Option<P<Node>> {
    if body.kind() != Kind::Block || body.statements().len() != 1 {
        return None;
    }
    let stmt = body.statements()[0];
    if stmt.kind() == Kind::ReturnStatement {
        stmt.as_return_statement().expression()
    } else {
        None
    }
}
fn contains_yield_star(node: P<Node>) -> bool {
    if ast::is_function_like(node) {
        return false;
    }
    if node.kind() == Kind::YieldExpression && node.as_yield_expression().asterisk_token.is_some() {
        return true;
    }
    node.iter_children().into_iter().any(contains_yield_star)
}
fn raw_text(ctx: &RuleContext<'_>, node: P<Node>) -> String {
    let start = node.pos().expect_source("source") as usize;
    let end = node.end().expect_source("source") as usize;
    ctx.file.text()[start..end].into()
}

fn check_typeof(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let query = node.as_type_query_node();
    if !node.type_arguments().is_empty() {
        return;
    }
    let expr = query.expr_name;
    if expr.kind() != Kind::QualifiedName {
        return;
    }
    let q = expr.as_qualified_name();
    if q.right.text() != "Type" {
        return;
    }
    let Some(symbol) = resolve_type_entity(ctx, q.left, node) else {
        return;
    };
    let mut parent = node.parent();
    while let Some(p) = parent {
        if p.kind() == Kind::TypeAliasDeclaration && symbol.declarations().contains(&p) {
            return;
        }
        parent = p.parent();
    }
    let inner = if symbol.flags().intersects(SymbolFlags::Type) {
        Some(ctx.checker.get_declared_type_of_symbol(symbol))
    } else {
        ctx.checker
            .get_type_of_symbol_at_location(symbol, Some(node))
    };
    if let Some(inner) = inner {
        let query_ty = ctx.ty(node);
        if ctx.checker.is_type_assignable_to(query_ty, inner)
            && ctx.checker.is_type_assignable_to(inner, query_ty)
        {
            ctx.emit(
                Rule::UnnecessaryTypeofType,
                node,
                377090,
                &[ctx.text(q.left)],
            );
        }
    }
}
fn resolve_type_entity(
    ctx: &mut RuleContext<'_>,
    entity: P<Node>,
    location: P<Node>,
) -> Option<P<Symbol>> {
    let mut symbol = if entity.kind() == Kind::Identifier {
        ctx.checker.resolve_name_exported(
            entity.text(),
            location,
            SymbolFlags::Type | SymbolFlags::Namespace,
            false,
        )?
    } else if entity.kind() == Kind::QualifiedName {
        let q = entity.as_qualified_name();
        let left = resolve_type_entity(ctx, q.left, location)?;
        if let Some(member) = ctx
            .checker
            .try_get_member_in_module_exports_and_properties(q.right.text(), left)
        {
            member
        } else {
            let ty = ctx.checker.get_declared_type_of_symbol(left);
            ctx.checker.get_property_of_type(ty, q.right.text())?
        }
    } else {
        return None;
    };
    let mut seen = HashSet::new();
    while symbol.flags().intersects(SymbolFlags::Alias) && seen.insert(symbol) {
        symbol = ctx.checker.get_aliased_symbol(symbol);
    }
    Some(symbol)
}

type YieldCandidates = HashMap<P<Node>, (P<Node>, Option<P<Node>>)>;

fn check_redundant(ctx: &mut RuleContext<'_>, nodes: &[P<Node>], map: bool) {
    let mut candidates: HashMap<P<Node>, YieldCandidates> = HashMap::new();
    for flow in ctx.piping_flows(true) {
        let Some(step) = flow.transformations.last() else {
            continue;
        };
        if !ctx.is_api(
            step.callee,
            "Effect",
            if map { "mapError" } else { "orDie" },
        ) {
            continue;
        }
        let mut parent = flow.node.parent();
        let mut yield_node = None;
        while let Some(n) = parent {
            if n.kind() == Kind::YieldExpression {
                yield_node = Some(n);
                break;
            }
            parent = n.parent();
        }
        let Some(y) = yield_node else {
            continue;
        };
        if y.as_yield_expression().expression != Some(flow.node)
            || y.as_yield_expression().asterisk_token.is_none()
            || ctx.effect_context(y) & 1 == 0
        {
            continue;
        }
        let Some(generator) = ctx.yield_generator(y) else {
            continue;
        };
        let mapper = if map {
            let Some(m) = step.args.first() else {
                continue;
            };
            Some(unwrap_expression(*m))
        } else {
            None
        };
        candidates
            .entry(generator)
            .or_default()
            .insert(y, (step.callee, mapper));
    }
    for (generator, entries) in candidates {
        if entries.len() < 2 {
            continue;
        }
        let Some(call) = enclosing_call(generator) else {
            continue;
        };
        let mut yields = Vec::new();
        for node in nodes.iter().copied() {
            if node.kind() == Kind::YieldExpression
                && node.as_yield_expression().asterisk_token.is_some()
                && node.as_yield_expression().expression.is_some()
                && ctx.yield_generator(node) == Some(generator)
                && ctx.effect_context(node) & 1 != 0
            {
                yields.push(node);
            }
        }
        if yields.len() != entries.len() || yields.iter().any(|y| !entries.contains_key(y)) {
            continue;
        }
        let mut text = None;
        let mut valid = true;
        for y in &yields {
            if let Some(mapper) = entries[y].1 {
                let value = ctx.text(mapper);
                if text.as_ref().is_some_and(|t| *t != value)
                    || !mapper_can_hoist(ctx, mapper, generator, call)
                {
                    valid = false;
                    break;
                }
                text = Some(value);
            }
        }
        if !valid {
            continue;
        }
        let rule = if map {
            Rule::RedundantMapError
        } else {
            Rule::RedundantOrDie
        };
        let code = if map { 377088 } else { 377096 };
        let related_code = if map { 377089 } else { 377097 };
        let range = generator
            .as_function_expression()
            .asterisk_token()
            .map(|star| {
                TextRange::new(
                    tsrs_scanner::get_token_pos_of_node(generator, ctx.file, false),
                    star.end().expect_source("source"),
                )
            })
            .unwrap_or_else(|| tsrs_scanner::get_error_range_for_node(ctx.file, generator));
        let index = ctx.emit_range(rule, ctx.file, range, code, &[]);
        for y in yields {
            let related = ctx.related(ctx.file, entries[&y].0, related_code, &[]);
            ctx.diagnostics[index].related.push(related);
        }
    }
}
fn enclosing_call(node: P<Node>) -> Option<P<Node>> {
    let mut current = node.parent();
    while let Some(n) = current {
        if n.kind() == Kind::CallExpression {
            return Some(n);
        }
        current = n.parent();
    }
    None
}
fn mapper_can_hoist(
    ctx: &mut RuleContext<'_>,
    mapper: P<Node>,
    generator: P<Node>,
    location: P<Node>,
) -> bool {
    let mut nodes = Vec::new();
    walk(mapper, &mut |n| nodes.push(n));
    for n in nodes {
        if n.kind() != Kind::Identifier
            || ast::is_declaration_name_or_import_property_name(n)
            || ast::is_valid_type_only_alias_use_site(n)
        {
            continue;
        }
        if n.parent().is_some_and(|p| match p.kind() {
            Kind::PropertyAccessExpression => p.as_property_access_expression().name() == n,
            Kind::QualifiedName => p.as_qualified_name().right == n,
            Kind::PropertyAssignment => p.name() == Some(n),
            _ => false,
        }) {
            continue;
        }
        let symbol = if n
            .parent()
            .is_some_and(|p| p.kind() == Kind::ShorthandPropertyAssignment)
        {
            ctx.checker
                .get_shorthand_assignment_value_symbol(n.parent())
        } else {
            ctx.symbol(n)
        };
        if let Some(symbol) = symbol {
            if !symbol.declarations().is_empty()
                && symbol
                    .declarations()
                    .iter()
                    .all(|d| ast::is_node_descendant_of(*d, mapper))
            {
                continue;
            }
            if symbol
                .declarations()
                .iter()
                .any(|d| ast::is_node_descendant_of(*d, generator))
            {
                return false;
            }
            if !ctx
                .checker
                .is_past_last_assignment_exported(symbol, location)
            {
                return false;
            }
        }
    }
    true
}

fn check_opportunity(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if node.type_node().is_some()
        || (node.kind() == Kind::FunctionExpression
            && (node.as_function_expression().asterisk_token().is_some() || node.name().is_some()))
        || (node.kind() == Kind::FunctionDeclaration
            && node.as_function_declaration().asterisk_token().is_some())
    {
        return;
    }
    let name = ast::get_name_of_declaration(node).or_else(|| {
        node.parent()
            .filter(|p| {
                matches!(
                    p.kind(),
                    Kind::VariableDeclaration
                        | Kind::PropertyDeclaration
                        | Kind::PropertyAssignment
                )
            })
            .and_then(|p| p.name())
    });
    let Some(name) = name.filter(|n| matches!(n.kind(), Kind::Identifier | Kind::StringLiteral))
    else {
        return;
    };
    if node.parent().is_some_and(|p| {
        p.kind() == Kind::CallExpression
            && p.arguments().first() == Some(&node)
            && parse_function_call(ctx, p, false).is_some()
    }) {
        return;
    }
    let ty = ctx.ty(node);
    let signatures = ctx.checker.get_signatures_of_type(ty, SignatureKind::Call);
    if signatures.len() != 1 {
        return;
    }
    let return_type = ctx.checker.get_return_type_of_signature(signatures[0]);
    if ctx
        .union_members(return_type)
        .into_iter()
        .any(|t| ctx.strict_effect_type(t).is_none())
    {
        return;
    }
    if node.kind() == Kind::FunctionDeclaration && used_before_declaration(ctx, node, name) {
        return;
    }
    let suggested = ctx.text(name);
    let inferred = inferred_name(ctx, node, &suggested);
    let layer_member = !inferred.is_empty() && inferred != suggested;
    let Some(body) = node.body() else {
        return;
    };
    let expression = if body.kind() == Kind::Block {
        single_return(body)
    } else {
        Some(body)
    };
    let mut parsed = None;
    if let Some(expression) = expression {
        let pipe = ctx.parse_pipe_call(expression);
        let subject = pipe.as_ref().map_or(expression, |p| p.subject);
        if let Some(mut p) = parse_function_call(ctx, subject, true)
            && p.options.is_none()
        {
            if let Some(pipe) = pipe {
                p.pipes.extend(pipe.args);
            }
            if !p.pipes.iter().any(|n| n.kind() == Kind::SpreadElement)
                && !parameters_referenced(ctx, node, &p.pipes)
            {
                parsed = Some(p);
            } else {
                return;
            }
        }
    }
    if parsed.is_none()
        && !(layer_member || (body.kind() == Kind::Block && body.statements().len() > 5))
    {
        return;
    }
    let mut trace = None;
    if let Some(parsed) = &parsed
        && let Some(last) = parsed.pipes.last()
        && last.kind() == Kind::CallExpression
        && !last.arguments().is_empty()
        && ctx.is_api(last.as_call_expression().expression(), "Effect", "withSpan")
    {
        trace = Some(last.arguments()[0]);
    }
    let configured: Vec<&str> = ctx
        .options
        .get("effectFn")
        .and_then(|v| v.as_array())
        .map(|vs| vs.iter().filter_map(|v| v.as_str()).collect())
        .filter(|vs: &Vec<&str>| !vs.is_empty())
        .unwrap_or_else(|| vec!["span"]);
    let mode = if configured.contains(&"span") && trace.is_some() {
        "span"
    } else if configured.contains(&"untraced") && parsed.is_some() {
        "untraced"
    } else if configured.contains(&"no-span") {
        "no-span"
    } else if trace.is_none() && configured.contains(&"inferred-span") && !inferred.is_empty() {
        "inferred-span"
    } else if trace.is_none()
        && configured.contains(&"suggested-span")
        && !suggested.is_empty()
        && (!configured.contains(&"inferred-span") || suggested != inferred)
    {
        "suggested-span"
    } else {
        return;
    };
    let module = parsed
        .as_ref()
        .and_then(|p| p.module)
        .filter(|m| m.kind() == Kind::Identifier)
        .map(|m| ctx.text(m))
        .unwrap_or_else(|| "Effect".into());
    let params = node
        .parameters()
        .iter()
        .map(|p| {
            p.name()
                .filter(|n| n.kind() == Kind::Identifier)
                .map(|n| ctx.text(n))
                .unwrap_or_else(|| "_".into())
        })
        .collect::<Vec<_>>()
        .join(", ");
    let type_params = node
        .type_parameters()
        .iter()
        .filter_map(|p| p.name())
        .map(|n| ctx.text(n))
        .collect::<Vec<_>>();
    let types = if type_params.is_empty() {
        String::new()
    } else {
        format!("<{}>", type_params.join(", "))
    };
    let function = if parsed.is_some() {
        format!("function*{types}({params}) {{ ... }}")
    } else if node.kind() == Kind::ArrowFunction {
        format!("{types}({params}) => {{ ... }}")
    } else {
        format!("function{types}({params}) {{ ... }}")
    };
    let pipe_count = parsed.as_ref().map_or(0, |p| p.pipes.len());
    let suffix = if pipe_count > usize::from(mode == "span") {
        ", ...pipeTransformations"
    } else {
        ""
    };
    let expected = match mode {
        "span" => format!(
            "{module}.fn({})({function}{suffix})",
            raw_text(ctx, trace.unwrap()).trim()
        ),
        "untraced" => format!("{module}.fnUntraced({function}{suffix})"),
        "inferred-span" => format!("{module}.fn(\"{inferred}\")({function}{suffix})"),
        "suggested-span" => format!("{module}.fn(\"{suggested}\")({function}{suffix})"),
        _ => format!("{module}.fn({function}{suffix})"),
    };
    ctx.emit(Rule::EffectFnOpportunity, name, 377047, &[expected]);
}
fn used_before_declaration(ctx: &mut RuleContext<'_>, node: P<Node>, name: P<Node>) -> bool {
    let Some(symbol) = ctx.symbol(name) else {
        return false;
    };
    let Some(mut scope) = node.parent() else {
        return false;
    };
    if matches!(scope.kind(), Kind::CaseClause | Kind::DefaultClause) {
        scope = scope.parent().unwrap_or(scope);
    }
    let mut stack = scope.iter_children();
    while let Some(n) = stack.pop() {
        if n.pos() >= node.pos() || ast::is_type_node(n) || n.kind() == Kind::ExportDeclaration {
            continue;
        }
        if n.kind() == Kind::ShorthandPropertyAssignment
            && ctx.checker.get_shorthand_assignment_value_symbol(Some(n)) == Some(symbol)
        {
            return true;
        }
        if n.kind() == Kind::Identifier && n.text() == name.text() && ctx.symbol(n) == Some(symbol)
        {
            return true;
        }
        stack.extend(n.iter_children());
    }
    false
}
fn parameters_referenced(ctx: &mut RuleContext<'_>, node: P<Node>, nodes: &[P<Node>]) -> bool {
    let Some(first) = node.parameters().first() else {
        return false;
    };
    let last = node.parameters().last().unwrap();
    let mut stack = nodes.to_vec();
    while let Some(n) = stack.pop() {
        let symbol = if n.kind() == Kind::Identifier {
            ctx.symbol(n)
        } else if n.kind() == Kind::ShorthandPropertyAssignment {
            ctx.checker.get_shorthand_assignment_value_symbol(Some(n))
        } else {
            None
        };
        if symbol.is_some_and(|s| {
            s.declarations()
                .iter()
                .any(|d| d.pos() >= first.pos() && d.end() <= last.end())
        }) {
            return true;
        }
        stack.extend(n.iter_children());
    }
    false
}
fn inferred_name(ctx: &mut RuleContext<'_>, node: P<Node>, suggested: &str) -> String {
    if let Some(p) = node
        .parent()
        .filter(|p| p.kind() == Kind::PropertyAssignment)
        && let Some(object) = p
            .parent()
            .filter(|p| p.kind() == Kind::ObjectLiteralExpression)
        && let Some(service) = object_service(ctx, object)
    {
        return format!("{service}.{suggested}");
    }
    if node.kind() == Kind::FunctionDeclaration
        && ast::get_combined_modifier_flags(node).intersects(ModifierFlags::Export)
    {
        return suggested.into();
    }
    if let Some(p) = node
        .parent()
        .filter(|p| p.kind() == Kind::VariableDeclaration)
        && let Some(list) = p.parent().filter(|p| {
            p.kind() == Kind::VariableDeclarationList && p.flags().intersects(NodeFlags::Const)
        })
        && list.parent().is_some_and(|p| {
            p.kind() == Kind::VariableStatement
                && ast::get_combined_modifier_flags(p).intersects(ModifierFlags::Export)
        })
    {
        return suggested.into();
    }
    String::new()
}
fn service_text(ctx: &RuleContext<'_>, node: P<Node>) -> String {
    if node.kind() == Kind::ThisKeyword {
        let mut p = node.parent();
        while let Some(n) = p {
            if n.kind() == Kind::ClassDeclaration
                && let Some(name) = n.name()
            {
                return ctx.text(name);
            }
            p = n.parent();
        }
    }
    ctx.text(node)
}
fn layer_service(
    ctx: &mut RuleContext<'_>,
    call: P<Node>,
    implementation: P<Node>,
    method: &str,
) -> Option<String> {
    if call.kind() != Kind::CallExpression {
        return None;
    }
    let callee = call.as_call_expression().expression();
    if call.arguments().len() >= 2
        && call.arguments()[1] == implementation
        && ctx.is_api(callee, "Layer", method)
    {
        return Some(service_text(ctx, call.arguments()[0]));
    }
    if callee.kind() == Kind::CallExpression
        && !callee.arguments().is_empty()
        && call.arguments().first() == Some(&implementation)
        && ctx.is_api(callee.as_call_expression().expression(), "Layer", method)
    {
        return Some(service_text(ctx, callee.arguments()[0]));
    }
    None
}
fn object_service(ctx: &mut RuleContext<'_>, object: P<Node>) -> Option<String> {
    let parent = object.parent()?;
    if parent.kind() == Kind::CallExpression {
        if let Some(service) = layer_service(ctx, parent, object, "succeed") {
            return Some(service);
        }
        let callee = parent.as_call_expression().expression();
        if parent.arguments().first() == Some(&object)
            && callee.kind() == Kind::PropertyAccessExpression
            && callee.as_property_access_expression().name().text() == "of"
        {
            let service = callee.as_property_access_expression().expression();
            let ty = ctx.ty(service);
            if ctx.is_context_tag(ty) || ctx.is_service_type(ty) {
                return Some(service_text(ctx, service));
            }
        }
    }
    if parent.kind() != Kind::ReturnStatement {
        return None;
    }
    let block = parent.parent()?;
    if block.kind() != Kind::Block {
        return None;
    }
    let function = block.parent()?;
    if !matches!(
        function.kind(),
        Kind::FunctionExpression | Kind::ArrowFunction
    ) {
        return None;
    }
    let call = function.parent()?;
    if let Some(service) = layer_service(ctx, call, function, "sync") {
        return Some(service);
    }
    let parsed = parse_function_call(ctx, call, true)?;
    if parsed.function != function {
        return None;
    }
    let outer = call.parent()?;
    if let Some(service) = layer_service(ctx, outer, call, "effect") {
        return Some(service);
    }
    if outer.kind() == Kind::PropertyAssignment && outer.name().is_some_and(|n| n.text() == "make")
    {
        let mut p = outer.parent();
        while let Some(n) = p {
            if n.kind() == Kind::ClassDeclaration {
                // Verify the class constructor inherits an actual Context.Service API call.
                let mut heritage = Vec::new();
                for child in n.iter_children() {
                    if child.kind() == Kind::HeritageClause {
                        walk(child, &mut |v| heritage.push(v));
                    }
                }
                if heritage.into_iter().any(|h| {
                    h.kind() == Kind::CallExpression
                        && ctx.is_api(h.as_call_expression().expression(), "Context", "Service")
                }) {
                    return n.name().map(|name| ctx.text(name));
                }
                return None;
            }
            p = n.parent();
        }
    }
    None
}

fn is_pipeable(ctx: &mut RuleContext<'_>, ty: P<Type>) -> bool {
    ctx.checker
        .get_type_of_property_of_type(ty, "pipe")
        .is_some_and(|t| {
            !ctx.checker
                .get_signatures_of_type(t, SignatureKind::Call)
                .is_empty()
        })
}
fn safely_pipeable(ctx: &mut RuleContext<'_>, callee: P<Node>) -> bool {
    match callee.kind() {
        Kind::CallExpression | Kind::ArrowFunction | Kind::FunctionExpression => true,
        Kind::ParenthesizedExpression => {
            safely_pipeable(ctx, callee.as_parenthesized_expression().expression())
        }
        Kind::Identifier | Kind::PropertyAccessExpression => {
            let subject = if callee.kind() == Kind::Identifier {
                callee
            } else {
                callee.as_property_access_expression().expression()
            };
            let Some(symbol) = ctx.symbol(subject) else {
                return false;
            };
            if symbol
                .flags()
                .intersects(SymbolFlags::Module | SymbolFlags::Namespace | SymbolFlags::ValueModule)
            {
                return true;
            }
            symbol.declarations().first().is_some_and(|d| {
                if callee.kind() == Kind::Identifier {
                    matches!(
                        d.kind(),
                        Kind::FunctionDeclaration
                            | Kind::VariableDeclaration
                            | Kind::ImportSpecifier
                            | Kind::ImportClause
                            | Kind::NamespaceImport
                    )
                } else {
                    matches!(
                        d.kind(),
                        Kind::NamespaceImport | Kind::SourceFile | Kind::ModuleDeclaration
                    )
                }
            })
        }
        _ => false,
    }
}
fn check_missed_pipeable(ctx: &mut RuleContext<'_>) {
    let min = ctx
        .options
        .get("pipeableMinArgCount")
        .and_then(|v| v.as_u64())
        .unwrap_or(2) as usize;
    for flow in ctx.piping_flows(false) {
        if flow.transformations.len() < min {
            continue;
        }
        if flow
            .transformations
            .last()
            .and_then(|s| s.out_type(ctx))
            .is_some_and(|ty| {
                !ctx.checker
                    .get_signatures_of_type(ty, SignatureKind::Call)
                    .is_empty()
            })
        {
            continue;
        }
        let count = flow.transformations.len();
        let mut runs = vec![(0usize, 0usize); count + 1];
        for i in (0..count).rev() {
            let step = &flow.transformations[i];
            if safely_pipeable(ctx, step.callee) {
                runs[i] = (
                    runs[i + 1].0 + 1,
                    runs[i + 1].1 + usize::from(step.kind == TransformationKind::Call),
                );
            }
        }
        for (i, run) in runs.iter().enumerate().take(count) {
            if run.1 < min {
                continue;
            }
            let ty = flow.input_type(ctx, i);
            if !ty.is_some_and(|t| is_pipeable(ctx, t)) {
                continue;
            }
            let mut current = flow.node;
            let mut valid = true;
            if i == 0 {
                current = flow.subject;
            } else {
                for j in (i..count).rev() {
                    if flow.transformations[j].kind != TransformationKind::Call
                        || current.kind() != Kind::CallExpression
                        || current.arguments().is_empty()
                    {
                        valid = false;
                        break;
                    }
                    current = current.arguments()[0];
                }
            }
            let text = if valid {
                ctx.text(current).trim().to_string()
            } else {
                String::new()
            };
            ctx.emit(Rule::MissedPipeableOpportunity, flow.node, 377050, &[text]);
            break;
        }
    }
}

fn check_missing_pipeable(ctx: &mut RuleContext<'_>) {
    let Some(module) = ctx
        .checker
        .get_symbol_of_declaration_exported(ctx.file.as_node())
    else {
        return;
    };
    for exported in ctx.checker.get_exports_of_module_exported(module) {
        let target = if exported.flags().intersects(SymbolFlags::Alias) {
            ctx.checker.get_aliased_symbol(exported)
        } else {
            exported
        };
        let Some(declaration) = target
            .declarations()
            .iter()
            .copied()
            .find(|d| ast::get_source_file_of_node(*d) == Some(ctx.file))
        else {
            continue;
        };
        let location = target
            .value_declaration()
            .and_then(ast::get_name_of_declaration)
            .or_else(|| ast::get_name_of_declaration(declaration))
            .unwrap_or(declaration);
        let Some(ty) = ctx
            .checker
            .get_type_of_symbol_at_location(target, Some(location))
        else {
            continue;
        };
        let signatures = ctx
            .checker
            .get_signatures_of_type(ty, SignatureKind::Call)
            .to_vec();
        let mut has = HashSet::new();
        let mut pipeable = HashSet::new();
        for &data in &signatures {
            if data.has_rest_parameter() || data.parameters().len() < 2 {
                continue;
            }
            for index in [0, data.parameters().len() - 1] {
                for &candidate in &signatures {
                    if data != candidate && ctx.pipeable_shapes_match(data, candidate, index) {
                        has.insert(data);
                        pipeable.insert(candidate);
                    }
                }
            }
        }
        for signature in signatures {
            if signature.has_rest_parameter()
                || signature.parameters().len() < 2
                || has.contains(&signature)
                || pipeable.contains(&signature)
            {
                continue;
            }
            let text = ctx.checker.signature_to_string_ex_exported(
                signature,
                Some(location),
                TypeFormatFlags::WriteArrowStyleSignature,
                None,
            );
            ctx.emit(
                Rule::MissingPipeableSignature,
                location,
                377101,
                &[exported.name().into(), text],
            );
        }
    }
}
