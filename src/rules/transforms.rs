//! Semantics-preserving simplifications of Effect constructors and piping flows.
use std::collections::HashSet;

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node, SymbolFlags};
use tsrs_checker::{SignatureKind, TypeFlags};
use tsrs_core::P;

use crate::{
    Rule,
    rules::{RuleContext, walk},
    semantic::{DispatchConditionKind, FlowTransformation, PipingFlow, TransformationKind},
};

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::UnnecessaryPipeChain,
        Rule::EffectSucceedWithVoid,
        Rule::PreferSucceedSomeOrNone,
        Rule::EffectMapVoid,
        Rule::UnnecessaryFailYieldableError,
        Rule::EffectDoNotation,
        Rule::EffectMapFlatten,
        Rule::AllOfMapToForEach,
        Rule::MapSomeToAsSome,
        Rule::FlatMapToMap,
        Rule::FlatMapToTap,
        Rule::FlatMapIgnoredParamToAndThen,
        Rule::MatchEffectToMatch,
        Rule::MatchEffectToMapBoth,
        Rule::FlatMapConditionalToFilterOrFail,
        Rule::OptionMatchToFromOption,
        Rule::SyncToSucceed,
        Rule::EffectSleepZeroToYieldNow,
        Rule::AcquireReleaseDisposable,
        Rule::RaceFirstWithSleepToTimeout,
        Rule::RunOfExitToRunExit,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    let root = ctx.file.as_node();
    let mut nodes = Vec::new();
    walk(root, &mut |n| nodes.push(n));
    let mut run_exit_seen = HashSet::new();
    for &node in &nodes {
        if ctx.enabled(Rule::UnnecessaryPipeChain) {
            pipe_chain(ctx, node);
        }
        if node.kind() == Kind::YieldExpression && ctx.enabled(Rule::UnnecessaryFailYieldableError)
        {
            let y = node.as_yield_expression();
            if y.asterisk_token.is_some()
                && let Some(expression) = y.expression
                && let Some(args) = effect_call(ctx, expression, "fail", false)
                && let Some(&arg) = args.first()
            {
                let t = ctx.ty(arg);
                if ctx.is_yieldable_error_type(t) {
                    ctx.emit(Rule::UnnecessaryFailYieldableError, node, 377019, &[]);
                }
            }
        }
        if node.kind() == Kind::ConditionalExpression && ctx.enabled(Rule::OptionMatchToFromOption)
        {
            option_conditional(ctx, node);
        }
        if node.kind() != Kind::CallExpression {
            continue;
        }
        let call = node.as_call_expression();
        let args = call.arguments.nodes();
        if ctx.enabled(Rule::EffectSucceedWithVoid)
            && !args.is_empty()
            && void_expression(ctx, args[0])
            && ctx.is_api(call.expression, "Effect", "succeed")
        {
            ctx.emit(Rule::EffectSucceedWithVoid, node, 377016, &[]);
        }
        if ctx.enabled(Rule::SyncToSucceed)
            && args.len() == 1
            && ctx.is_api(call.expression, "Effect", "sync")
            && let Some(lazy) = ctx.parse_lazy_expression(args[0], 1)
            && ctx.is_expression_value_stable_at_location(lazy.expression, node)
        {
            ctx.emit(Rule::SyncToSucceed, call.expression, 377103, &[]);
        }
        if ctx.enabled(Rule::EffectSleepZeroToYieldNow)
            && matches!(ctx.detected_effect_version, 3 | 4)
            && ordinary_call(node, 1)
            && !ast::is_optional_chain(zero_expression(call.expression))
            && ctx.is_api(zero_expression(call.expression), "Effect", "sleep")
            && zero_duration(ctx, args[0])
        {
            ctx.emit(
                Rule::EffectSleepZeroToYieldNow,
                call.expression,
                377142,
                &[],
            );
        }
        if ctx.enabled(Rule::AllOfMapToForEach)
            && (1..=2).contains(&args.len())
            && !spread(args)
            && ctx.is_api(call.expression, "Effect", "all")
            && all_map_receiver(ctx, args[0], args.get(1).copied())
        {
            ctx.emit(Rule::AllOfMapToForEach, call.expression, 377113, &[]);
        }
        if ctx.enabled(Rule::AcquireReleaseDisposable) {
            acquire_disposable(ctx, node);
        }
        if ctx.enabled(Rule::RunOfExitToRunExit)
            && !args.is_empty()
            && let Some((target, name, replacement)) = runner(ctx, call.expression)
            && let Some(flow) = ctx.longest_piping_flow_at(args[0], false)
            && flow
                .transformations
                .last()
                .is_some_and(|s| s.args.is_empty() && ctx.is_api(s.callee, "Effect", "exit"))
            && run_exit_seen.insert(call.expression)
        {
            ctx.emit(
                Rule::RunOfExitToRunExit,
                location_runner(call.expression, target),
                377123,
                &[name.into(), replacement.into()],
            );
        }
    }
    if ctx.enabled(Rule::EffectDoNotation) {
        do_notation(ctx, root);
    }

    if ![
        Rule::PreferSucceedSomeOrNone,
        Rule::EffectMapVoid,
        Rule::EffectMapFlatten,
        Rule::AllOfMapToForEach,
        Rule::MapSomeToAsSome,
        Rule::FlatMapToMap,
        Rule::FlatMapToTap,
        Rule::FlatMapIgnoredParamToAndThen,
        Rule::MatchEffectToMatch,
        Rule::MatchEffectToMapBoth,
        Rule::FlatMapConditionalToFilterOrFail,
        Rule::OptionMatchToFromOption,
        Rule::RaceFirstWithSleepToTimeout,
        Rule::RunOfExitToRunExit,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }

    let flows = ctx.piping_flows(true);
    for flow in &flows {
        for (i, step) in flow.transformations.iter().enumerate() {
            let callee = step.callee;
            if ctx.enabled(Rule::PreferSucceedSomeOrNone)
                && step.args.is_empty()
                && step.type_arguments.is_empty()
                && ctx.is_api(callee, "Effect", "succeed")
            {
                let none = i == 0 && option_none(ctx, flow.subject);
                let some = i > 0
                    && flow.transformations[i - 1].args.is_empty()
                    && ctx.is_api(flow.transformations[i - 1].callee, "Option", "some");
                if none || some {
                    ctx.emit(
                        Rule::PreferSucceedSomeOrNone,
                        callee,
                        377117,
                        &[if none { "succeedNone" } else { "succeedSome" }.into()],
                    );
                }
            }
            if ctx.enabled(Rule::AllOfMapToForEach)
                && i > 0
                && step.args.is_empty()
                && matches!(
                    step.kind,
                    TransformationKind::Pipe | TransformationKind::Pipeable
                )
                && ctx.is_api(callee, "Effect", "all")
            {
                let prior = flow.transformations[i - 1].callee;
                if let Some(parent) = prior.parent()
                    && parent.kind() == Kind::CallExpression
                    && parent.as_call_expression().expression == prior
                    && all_map_receiver(ctx, parent, None)
                {
                    ctx.emit(Rule::AllOfMapToForEach, callee, 377113, &[]);
                }
            }
            if ctx.enabled(Rule::FlatMapToMap)
                && !step.args.is_empty()
                && ctx.is_api(callee, "Effect", "flatMap")
                && let Some(lazy) = ctx.parse_lazy_expression(step.args[0], 0)
                && effect_call(ctx, lazy.expression, "succeed", false).is_some_and(|a| a.len() == 1)
            {
                ctx.emit(Rule::FlatMapToMap, callee, 377100, &[]);
            }
            if step.args.len() == 1 {
                let arg = step.args[0];
                if ctx.is_api(callee, "Effect", "map") {
                    if ctx.enabled(Rule::EffectMapVoid) && void_callback(ctx, arg) {
                        ctx.emit(Rule::EffectMapVoid, callee, 377018, &[]);
                    }
                    if ctx.enabled(Rule::MapSomeToAsSome)
                        && step.type_arguments.is_empty()
                        && some_mapper(ctx, arg)
                    {
                        ctx.emit(Rule::MapSomeToAsSome, callee, 377114, &[]);
                    }
                }
                if ctx.is_api(callee, "Effect", "flatMap") {
                    if ctx.enabled(Rule::FlatMapIgnoredParamToAndThen)
                        && let Some(lazy) = ctx.parse_lazy_expression(arg, 1)
                        && ctx.is_expression_value_stable_at_location(lazy.expression, callee)
                    {
                        let t = ctx.ty(lazy.expression);
                        if ctx.effect_type(t).is_some() {
                            ctx.emit(Rule::FlatMapIgnoredParamToAndThen, callee, 377132, &[]);
                        }
                    }
                    if ctx.enabled(Rule::FlatMapConditionalToFilterOrFail) {
                        conditional_filter(ctx, callee, arg);
                    }
                }
                if ctx.enabled(Rule::MatchEffectToMatch) || ctx.enabled(Rule::MatchEffectToMapBoth)
                {
                    match_effect(ctx, callee, arg);
                }
                if ctx.enabled(Rule::OptionMatchToFromOption)
                    && ctx.effect_version == 4
                    && ctx.is_api(callee, "Option", "match")
                    && option_handlers(ctx, arg)
                {
                    ctx.emit(Rule::OptionMatchToFromOption, callee, 377118, &[]);
                }
            }
            if ctx.enabled(Rule::FlatMapToTap) {
                flat_map_tap(ctx, flow, i, step);
            }
            if ctx.enabled(Rule::RaceFirstWithSleepToTimeout) {
                race_timeout(ctx, flow, i, step);
            }
        }
    }
    for flow in ctx.piping_flows(false) {
        for pair in flow.transformations.windows(2) {
            let first = &pair[0];
            let second = &pair[1];
            if ctx.enabled(Rule::EffectMapFlatten)
                && !first.args.is_empty()
                && second.args.is_empty()
                && matches!(
                    first.kind,
                    TransformationKind::Pipe | TransformationKind::Pipeable
                )
                && first.kind == second.kind
                && ctx.is_api(first.callee, "Effect", "map")
                && ctx.is_api(second.callee, "Effect", "flatten")
            {
                ctx.emit(Rule::EffectMapFlatten, second.callee, 377086, &[]);
            }
            if ctx.enabled(Rule::RunOfExitToRunExit)
                && first.args.is_empty()
                && ctx.is_api(first.callee, "Effect", "exit")
                && let Some((target, name, replacement)) = runner(ctx, second.callee)
                && run_exit_seen.insert(second.callee)
            {
                ctx.emit(
                    Rule::RunOfExitToRunExit,
                    location_runner(second.callee, target),
                    377123,
                    &[name.into(), replacement.into()],
                );
            }
        }
    }
}

fn spread(args: &[P<Node>]) -> bool {
    args.iter().any(|n| n.kind() == Kind::SpreadElement)
}
fn ordinary_call(node: P<Node>, n: usize) -> bool {
    if node.kind() != Kind::CallExpression || ast::is_optional_chain(node) {
        return false;
    }
    let call = node.as_call_expression();
    call.arguments.nodes().len() == n
        && call.type_arguments().is_none()
        && !spread(call.arguments.nodes())
}
fn effect_call(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    name: &str,
    no_types: bool,
) -> Option<Vec<P<Node>>> {
    let node = ast::skip_parentheses(node);
    if node.kind() != Kind::CallExpression {
        return None;
    }
    let call = node.as_call_expression();
    if no_types && call.type_arguments().is_some_and(|n| !n.nodes().is_empty()) {
        return None;
    }
    ctx.is_api(call.expression, "Effect", name)
        .then(|| call.arguments.nodes().to_vec())
}
fn plain_parameter(node: P<Node>, no_optional: bool) -> bool {
    if node.kind() != Kind::Parameter {
        return false;
    }
    let p = node.as_parameter_declaration();
    p.name().kind() == Kind::Identifier
        && p.initializer().is_none()
        && p.dot_dot_dot_token().is_none()
        && (!no_optional || p.question_token().is_none())
}
fn pipe_chain(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if node.kind() != Kind::CallExpression {
        return;
    }
    let Some(outer) = ctx.parse_pipe_call(node) else {
        return;
    };
    let Some(inner) = ctx.parse_pipe_call(outer.subject) else {
        return;
    };
    if spread(&inner.args) || spread(&outer.args) {
        return;
    }
    let count =
        inner.args.len() + outer.args.len() + usize::from(inner.kind == TransformationKind::Pipe);
    let ty = ctx.ty(inner.node.as_call_expression().expression);
    if ctx
        .checker
        .get_signatures_of_type(ty, SignatureKind::Call)
        .iter()
        .any(|s| {
            count >= s.min_argument_count()
                && (s.has_rest_parameter() || count <= s.parameters().len())
        })
    {
        ctx.emit(Rule::UnnecessaryPipeChain, outer.node, 377015, &[]);
    }
}
fn void_expression(ctx: &RuleContext<'_>, node: P<Node>) -> bool {
    let node = ast::skip_parentheses(node);
    if node.kind() == Kind::Identifier && ctx.text(node) == "undefined" {
        return true;
    }
    node.kind() == Kind::VoidExpression
        && node
            .expression()
            .is_some_and(|n| n.kind() == Kind::NumericLiteral && ctx.text(n) == "0")
}
fn void_callback(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    if let Some(lazy) = ctx.parse_lazy_expression(node, 1) {
        return void_expression(ctx, lazy.expression);
    }
    if !matches!(node.kind(), Kind::ArrowFunction | Kind::FunctionExpression) {
        return false;
    }
    let no_generics = node.type_parameters().is_empty();
    let no_params = node.parameters().is_empty();
    no_generics
        && no_params
        && node
            .body()
            .is_some_and(|b| b.kind() == Kind::Block && b.as_block().statements.nodes().is_empty())
}
fn option_none(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    node.kind() == Kind::CallExpression
        && node.as_call_expression().arguments.nodes().is_empty()
        && node
            .as_call_expression()
            .type_arguments()
            .is_none_or(|t| t.nodes().is_empty())
        && ctx.is_api(node.as_call_expression().expression, "Option", "none")
}
fn some_mapper(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let mapper = ctx.unwrap_identity_forwarder(node);
    if !mapper.type_arguments.is_empty() {
        return false;
    }
    if mapper.parameter.is_some_and(|p| {
        p.as_parameter_declaration().question_token().is_some()
            || p.as_parameter_declaration().type_().is_some()
    }) {
        return false;
    }
    ctx.is_api(mapper.target, "Option", "some")
}
fn do_notation(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if ctx.is_api(node, "Effect", "Do") {
        ctx.emit(Rule::EffectDoNotation, node, 377085, &[]);
        return;
    }
    node.for_each_child(&mut |child| {
        do_notation(ctx, child);
        false
    });
}
fn all_map_receiver(ctx: &mut RuleContext<'_>, node: P<Node>, options: Option<P<Node>>) -> bool {
    let node = ast::skip_parentheses(node);
    if node.kind() != Kind::CallExpression {
        return false;
    }
    let call = node.as_call_expression();
    if call.arguments.nodes().len() != 1
        || spread(call.arguments.nodes())
        || call.expression.kind() != Kind::PropertyAccessExpression
    {
        return false;
    }
    let property = call.expression.as_property_access_expression();
    if property.name().text() != "map" {
        return false;
    }
    let receiver = ctx.ty(property.expression);
    if !ctx.checker.is_array_type(receiver) {
        return false;
    }
    let result = ctx.ty(node);
    let Some(item) = ctx.checker.get_number_index_type(result) else {
        return false;
    };
    if ctx.effect_type(item).is_none() {
        return false;
    }
    if let Some(options) = options {
        let ty = ctx.ty(options);
        if ctx.checker.get_property_of_type(ty, "mode").is_some() {
            return false;
        }
    }
    true
}
fn object_property(node: P<Node>, name: &str) -> Option<P<Node>> {
    let node = ast::skip_parentheses(node);
    if node.kind() != Kind::ObjectLiteralExpression {
        return None;
    }
    for &prop in node.as_object_literal_expression().properties.nodes() {
        if prop.kind() == Kind::PropertyAssignment
            && prop.name().is_some_and(|n| {
                matches!(n.kind(), Kind::Identifier | Kind::StringLiteral) && n.text() == name
            })
        {
            return Some(prop.as_property_assignment().initializer());
        }
    }
    None
}
fn constructor_handler(ctx: &mut RuleContext<'_>, node: P<Node>, name: &str) -> bool {
    let Some(lazy) = ctx.parse_lazy_expression(node, 0) else {
        return false;
    };
    let Some(flow) = ctx.longest_piping_flow_at(lazy.expression, false) else {
        return false;
    };
    let Some(last) = flow.transformations.last() else {
        return false;
    };
    ctx.is_api(last.callee, "Effect", name)
        && flow.input_node(flow.transformations.len() - 1).is_some()
}
fn match_effect(ctx: &mut RuleContext<'_>, callee: P<Node>, handlers: P<Node>) {
    let is_match = ctx.is_api(callee, "Effect", "matchEffect");
    let is_cause = ctx.is_api(callee, "Effect", "matchCauseEffect");
    if !is_match && !is_cause {
        return;
    }
    let (Some(failure), Some(success)) = (
        object_property(handlers, "onFailure"),
        object_property(handlers, "onSuccess"),
    ) else {
        return;
    };
    if !constructor_handler(ctx, success, "succeed") {
        return;
    }
    if ctx.enabled(Rule::MatchEffectToMatch) && constructor_handler(ctx, failure, "succeed") {
        ctx.emit(
            Rule::MatchEffectToMatch,
            callee,
            377125,
            &[
                if is_match { "match" } else { "matchCause" }.into(),
                if is_match {
                    "matchEffect"
                } else {
                    "matchCauseEffect"
                }
                .into(),
            ],
        );
    }
    if ctx.enabled(Rule::MatchEffectToMapBoth)
        && is_match
        && constructor_handler(ctx, failure, "fail")
    {
        ctx.emit(Rule::MatchEffectToMapBoth, callee, 377126, &[]);
    }
}
fn synchronous(node: P<Node>) -> bool {
    matches!(node.kind(), Kind::ArrowFunction | Kind::FunctionExpression)
        && !ast::get_combined_modifier_flags(node).intersects(ModifierFlags::Async)
        && (node.kind() != Kind::FunctionExpression
            || node.as_function_expression().asterisk_token().is_none())
}
fn identity_succeed(ctx: &mut RuleContext<'_>, expression: P<Node>, name: P<Node>) -> bool {
    effect_call(ctx, expression, "succeed", true).is_some_and(|args| {
        args.len() == 1
            && ast::skip_parentheses(args[0]).kind() == Kind::Identifier
            && ctx.same_reference(ast::skip_parentheses(args[0]), name)
    })
}
fn conditional_filter(ctx: &mut RuleContext<'_>, callee: P<Node>, callback: P<Node>) {
    let Some(parsed) = ctx.parse_returning_dispatch(callback) else {
        return;
    };
    if parsed.params.len() != 1 || parsed.dispatch.branches.len() != 1 || !synchronous(parsed.node)
    {
        return;
    }
    let Some(fallback) = parsed.dispatch.fallback else {
        return;
    };
    let branch = &parsed.dispatch.branches[0];
    if branch.condition.kind != DispatchConditionKind::Predicate
        || !plain_parameter(parsed.params[0], false)
    {
        return;
    }
    let name = parsed.params[0].as_parameter_declaration().name();
    let Some(symbol) = ctx.symbol(name) else {
        return;
    };
    if ctx.checker.is_symbol_assigned_exported(symbol) {
        return;
    }
    let a = identity_succeed(ctx, branch.result, name);
    let b = identity_succeed(ctx, fallback, name);
    if a == b {
        return;
    }
    let other = if a { fallback } else { branch.result };
    let method = if effect_call(ctx, other, "fail", true).is_some_and(|a| a.len() == 1) {
        "filterOrFail"
    } else {
        let ty = ctx.ty(other);
        if ctx.effect_type(ty).is_none() {
            return;
        }
        "filterOrElse"
    };
    ctx.emit(
        Rule::FlatMapConditionalToFilterOrFail,
        callee,
        377120,
        &[method.into()],
    );
}
fn flat_map_tap(
    ctx: &mut RuleContext<'_>,
    flow: &PipingFlow,
    index: usize,
    step: &FlowTransformation,
) {
    let mut callee = step.callee;
    let mut args = step.args.clone();
    if step.kind == TransformationKind::Call && callee.kind() == Kind::CallExpression {
        let factory = callee.as_call_expression();
        if factory.arguments.nodes().len() == 1
            && factory.type_arguments().is_none()
            && ctx.is_api(factory.expression, "Effect", "andThen")
        {
            callee = factory.expression;
            args = factory.arguments.nodes().to_vec();
        }
    }
    if args.len() != 1 || !step.type_arguments.is_empty() || ast::is_optional_chain(callee) {
        return;
    }
    let name = if ctx.is_api(callee, "Effect", "flatMap") {
        "flatMap"
    } else if ctx.is_api(callee, "Effect", "andThen") {
        "andThen"
    } else {
        return;
    };
    let Some(callback) = ctx.parse_lazy_expression(args[0], 8) else {
        return;
    };
    if callback.params.len() != 1
        || callback.node.type_node().is_some()
        || !plain_parameter(callback.params[0], false)
    {
        return;
    }
    let parameter = callback.params[0].as_parameter_declaration();
    if step.kind == TransformationKind::Call && parameter.type_().is_some() {
        return;
    }
    let Some(input) = flow
        .input_type(ctx, index)
        .and_then(|t| ctx.strict_effect_type(t))
    else {
        return;
    };
    let Some(output) = step.out_type(ctx).and_then(|t| ctx.strict_effect_type(t)) else {
        return;
    };
    if input.a != output.a {
        return;
    }
    let Some(symbol) = ctx.symbol(parameter.name()) else {
        return;
    };
    if symbol.declarations().len() != 1 || ctx.checker.is_symbol_assigned_exported(symbol) {
        return;
    }
    let Some(returned) = ctx.longest_piping_flow_at(callback.expression, false) else {
        return;
    };
    let Some(last) = returned.transformations.last() else {
        return;
    };
    if ast::is_optional_chain(last.callee) || last.args.len() != 1 {
        return;
    }
    if returned
        .input_type(ctx, returned.transformations.len() - 1)
        .and_then(|t| ctx.strict_effect_type(t))
        .is_none()
    {
        return;
    }
    let mut reference = last.args[0];
    if ctx.is_api(last.callee, "Effect", "map") {
        let Some(mapper) = ctx.parse_lazy_expression(reference, 0) else {
            return;
        };
        if mapper.params.len() > 1
            || mapper
                .params
                .first()
                .is_some_and(|p| !plain_parameter(*p, false))
        {
            return;
        }
        reference = mapper.expression;
    } else if !ctx.is_api(last.callee, "Effect", "as") {
        return;
    }
    reference = ast::skip_parentheses(reference);
    if reference.kind() == Kind::Identifier && ctx.symbol(reference) == Some(symbol) {
        ctx.emit(Rule::FlatMapToTap, callee, 377144, &[name.into()]);
    }
}
fn option_handlers(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let node = ast::skip_parentheses(node);
    if node.kind() != Kind::ObjectLiteralExpression
        || node.as_object_literal_expression().properties.nodes().len() != 2
    {
        return false;
    }
    let mut on_none = None;
    let mut on_some = None;
    for &p in node.as_object_literal_expression().properties.nodes() {
        if p.kind() != Kind::PropertyAssignment {
            return false;
        }
        let prop = p.as_property_assignment();
        let name = prop.name();
        if name.kind() != Kind::Identifier {
            return false;
        }
        match name.text() {
            "onNone" if on_none.is_none() => on_none = Some(prop.initializer()),
            "onSome" if on_some.is_none() => on_some = Some(prop.initializer()),
            _ => return false,
        }
    }
    let (Some(on_none), Some(on_some)) = (on_none, on_some) else {
        return false;
    };
    let forward = ctx.unwrap_identity_forwarder(on_some);
    if !forward.type_arguments.is_empty() || !ctx.is_api(forward.target, "Effect", "succeed") {
        return false;
    }
    let Some(lazy) = ctx.parse_lazy_expression(on_none, 1) else {
        return false;
    };
    effect_call(ctx, lazy.expression, "fail", true).is_some_and(|a| a.len() == 1)
}
fn option_conditional(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if ctx.effect_version != 4 {
        return;
    }
    let Some(dispatch) = ctx.parse_result_dispatch(node) else {
        return;
    };
    if dispatch.branches.len() != 1 {
        return;
    }
    let Some(fallback) = dispatch.fallback else {
        return;
    };
    let branch = &dispatch.branches[0];
    if branch.condition.kind != DispatchConditionKind::Predicate || branch.condition.value.is_some()
    {
        return;
    }
    let condition = ast::skip_parentheses(branch.condition.subject);
    if condition.kind() != Kind::CallExpression {
        return;
    }
    let call = condition.as_call_expression();
    if call.arguments.nodes().len() != 1
        || call.type_arguments().is_some_and(|t| !t.nodes().is_empty())
    {
        return;
    }
    let option = ast::skip_parentheses(call.arguments.nodes()[0]);
    if option.kind() != Kind::Identifier {
        return;
    }
    let some = ctx.is_api(call.expression, "Option", "isSome");
    let none = ctx.is_api(call.expression, "Option", "isNone");
    if some == none {
        return;
    }
    let (success, failure) = if some {
        (branch.result, fallback)
    } else {
        (fallback, branch.result)
    };
    let Some(success) = effect_call(ctx, success, "succeed", true) else {
        return;
    };
    if success.len() != 1 {
        return;
    }
    let value = ast::skip_parentheses(success[0]);
    if value.kind() != Kind::PropertyAccessExpression || ast::is_optional_chain(value) {
        return;
    }
    let access = value.as_property_access_expression();
    let receiver = ast::skip_parentheses(access.expression);
    if access.name().text() != "value"
        || receiver.kind() != Kind::Identifier
        || !ctx.same_reference(option, receiver)
    {
        return;
    }
    if effect_call(ctx, failure, "fail", true).is_some_and(|a| a.len() == 1) {
        ctx.emit(Rule::OptionMatchToFromOption, call.expression, 377118, &[]);
    }
}
fn zero_expression(mut node: P<Node>) -> P<Node> {
    while matches!(
        node.kind(),
        Kind::ParenthesizedExpression
            | Kind::AsExpression
            | Kind::TypeAssertionExpression
            | Kind::SatisfiesExpression
    ) {
        let Some(inner) = node.expression() else {
            break;
        };
        node = inner;
    }
    node
}
fn imported_receiver(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let node = zero_expression(node);
    if node.kind() == Kind::PropertyAccessExpression && !ast::is_optional_chain(node) {
        let root = zero_expression(node.as_property_access_expression().expression);
        if root.kind() != Kind::Identifier {
            return false;
        }
        return ctx.symbol(root).is_some_and(|s| {
            s.declarations().len() == 1 && s.declarations()[0].kind() == Kind::NamespaceImport
        });
    }
    node.kind() == Kind::Identifier
        && ctx.symbol(node).is_some_and(|s| {
            s.declarations().len() == 1
                && matches!(
                    s.declarations()[0].kind(),
                    Kind::ImportSpecifier | Kind::NamespaceImport
                )
        })
}
fn zero_number(node: P<Node>, bigint: bool) -> bool {
    let mut node = zero_expression(node);
    if node.kind() == Kind::PrefixUnaryExpression {
        let p = node.as_prefix_unary_expression();
        if p.operator != Kind::MinusToken && (bigint || p.operator != Kind::PlusToken) {
            return false;
        }
        node = zero_expression(p.operand);
    }
    if bigint {
        if node.kind() != Kind::BigIntLiteral {
            return false;
        }
        let raw = node.text().trim_end_matches('n').replace('_', "");
        let digits = if raw.starts_with("0x")
            || raw.starts_with("0X")
            || raw.starts_with("0o")
            || raw.starts_with("0O")
            || raw.starts_with("0b")
            || raw.starts_with("0B")
        {
            &raw[2..]
        } else {
            &raw
        };
        !digits.is_empty() && digits.chars().all(|c| c == '0')
    } else {
        node.kind() == Kind::NumericLiteral && node.text().parse::<f64>().is_ok_and(|n| n == 0.0)
    }
}
fn zero_duration_string(s: &str, version: u8) -> bool {
    let Some(split) = s.find([' ', '\t']) else {
        return false;
    };
    let (number, tail) = s.split_at(split);
    let units = tail.trim_start_matches([' ', '\t']);
    let number = number.strip_prefix('-').unwrap_or(number);
    if number.is_empty() || number.split('.').count() > 2 {
        return false;
    }
    if !number
        .split('.')
        .all(|part| !part.is_empty() && part.chars().all(|c| c == '0'))
    {
        return false;
    }
    if ![
        "nano", "nanos", "micro", "micros", "milli", "millis", "second", "seconds", "minute",
        "minutes", "hour", "hours", "day", "days", "week", "weeks",
    ]
    .contains(&units)
    {
        return false;
    }
    version != 3
        || !number.contains('.')
        || !(units.starts_with("nano") || units.starts_with("micro"))
}
fn zero_duration(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let node = zero_expression(node);
    if zero_number(node, false) || zero_number(node, true) {
        return true;
    }
    match node.kind() {
        Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral => {
            zero_duration_string(node.text(), ctx.detected_effect_version)
        }
        Kind::ArrayLiteralExpression => {
            let e = node.as_array_literal_expression().elements.nodes();
            e.len() == 2 && zero_number(e[0], false) && zero_number(e[1], false)
        }
        Kind::PropertyAccessExpression => {
            !ast::is_optional_chain(node)
                && imported_receiver(ctx, node.as_property_access_expression().expression)
                && ctx.is_api(node, "Duration", "zero")
        }
        Kind::CallExpression => {
            if !ordinary_call(node, 1) {
                return false;
            }
            let c = node.as_call_expression();
            let callee = zero_expression(c.expression);
            if callee.kind() != Kind::PropertyAccessExpression || ast::is_optional_chain(callee) {
                return false;
            }
            let p = callee.as_property_access_expression();
            if !imported_receiver(ctx, p.expression) {
                return false;
            }
            let unit = p.name().text();
            let big = matches!(unit, "nanos" | "micros");
            if !big
                && !matches!(
                    unit,
                    "millis" | "seconds" | "minutes" | "hours" | "days" | "weeks"
                )
            {
                return false;
            }
            zero_number(c.arguments.nodes()[0], big) && ctx.is_api(callee, "Duration", unit)
        }
        _ => false,
    }
}
fn acquire_disposable(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if ctx.effect_version != 4 {
        return;
    }
    if node.kind() != Kind::CallExpression
        || node.as_call_expression().question_dot_token().is_some()
    {
        return;
    }
    let call = node.as_call_expression();
    let args = call.arguments.nodes();
    if args.len() != 2 || spread(args) || !ctx.is_api(call.expression, "Effect", "acquireRelease") {
        return;
    }
    let t = ctx.ty(node);
    let Some(channels) = ctx.strict_effect_type(t) else {
        return;
    };
    if ctx.union_members(channels.a).iter().any(|t| {
        t.flags()
            .intersects(TypeFlags::Any | TypeFlags::Unknown | TypeFlags::Never)
    }) {
        return;
    }
    let mut targets = Vec::new();
    for name in ["Disposable", "AsyncDisposable"] {
        if let Some(symbol) =
            ctx.checker
                .resolve_name_exported(name, None, SymbolFlags::Type, false)
        {
            targets.push(ctx.checker.get_declared_type_of_symbol(symbol));
        }
    }
    if targets.is_empty() {
        return;
    }
    let target = ctx.checker.get_union_type(&targets);
    if !ctx.checker.is_type_assignable_to(channels.a, target) {
        return;
    }
    let Some(release) = ctx.parse_lazy_expression(args[1], 0) else {
        return;
    };
    if !(1..=2).contains(&release.params.len())
        || release.params.iter().any(|p| !plain_parameter(*p, true))
    {
        return;
    }
    let name = release.params[0].as_parameter_declaration().name();
    let expression = ast::skip_parentheses(release.expression);
    if expression.kind() != Kind::CallExpression
        || expression
            .as_call_expression()
            .question_dot_token()
            .is_some()
    {
        return;
    }
    let wrapper = expression.as_call_expression();
    if wrapper.arguments.nodes().len() != 1 || spread(wrapper.arguments.nodes()) {
        return;
    }
    let sync = ctx.is_api(wrapper.expression, "Effect", "sync");
    let promise = ctx.is_api(wrapper.expression, "Effect", "promise");
    if !sync && !promise {
        return;
    }
    let Some(thunk) =
        ctx.parse_lazy_expression(wrapper.arguments.nodes()[0], if promise { 3 } else { 1 })
    else {
        return;
    };
    let expression = ast::skip_parentheses(thunk.expression);
    if expression.kind() != Kind::CallExpression
        || expression
            .as_call_expression()
            .question_dot_token()
            .is_some()
    {
        return;
    }
    let disposal = expression.as_call_expression();
    if !disposal.arguments.nodes().is_empty()
        || disposal
            .type_arguments()
            .is_some_and(|a| !a.nodes().is_empty())
        || disposal.expression.kind() != Kind::ElementAccessExpression
        || disposal
            .expression
            .as_element_access_expression()
            .question_dot_token()
            .is_some()
    {
        return;
    }
    let element = disposal.expression.as_element_access_expression();
    if !ctx.same_reference(ast::skip_parentheses(element.expression), name) {
        return;
    }
    let key = ast::skip_parentheses(element.argument_expression);
    if key.kind() != Kind::PropertyAccessExpression
        || key
            .as_property_access_expression()
            .question_dot_token()
            .is_some()
    {
        return;
    }
    let key = key.as_property_access_expression();
    let protocol = key.name().text();
    if !ctx.is_global(key.expression, "Symbol")
        || !((protocol == "dispose" && sync) || (protocol == "asyncDispose" && promise))
    {
        return;
    }
    ctx.emit(Rule::AcquireReleaseDisposable, call.expression, 377119, &[]);
}
fn timer_flow(ctx: &mut RuleContext<'_>, flow: Option<&PipingFlow>) -> bool {
    let Some(flow) = flow else {
        return false;
    };
    for (i, step) in flow.transformations.iter().enumerate() {
        let sleep = ctx.is_api(step.callee, "Effect", "sleep");
        if sleep || ctx.is_api(step.callee, "Effect", "delay") {
            return (!sleep || i == 0)
                && flow.transformations[i + 1..].iter().all(|s| {
                    ["flatMap", "andThen", "as", "map"]
                        .iter()
                        .any(|name| ctx.is_api(s.callee, "Effect", name))
                });
        }
    }
    false
}
fn race_timeout(
    ctx: &mut RuleContext<'_>,
    flow: &PipingFlow,
    index: usize,
    step: &FlowTransformation,
) {
    if ctx.effect_version != 4 {
        return;
    }
    let (left, right) = if ctx.is_api(step.callee, "Effect", "raceFirst") {
        if step.args.len() != 1 {
            return;
        }
        (
            flow.copy_prefix(index),
            ctx.longest_piping_flow_at(step.args[0], true),
        )
    } else if ctx.is_api(step.callee, "Effect", "raceAllFirst") {
        let array = ast::skip_parentheses(flow.subject);
        if array.kind() != Kind::ArrayLiteralExpression {
            return;
        }
        let elements = array.as_array_literal_expression().elements.nodes();
        if elements.len() != 2 {
            return;
        }
        (
            ctx.longest_piping_flow_at(elements[0], true),
            ctx.longest_piping_flow_at(elements[1], true),
        )
    } else {
        return;
    };
    if timer_flow(ctx, left.as_ref()) != timer_flow(ctx, right.as_ref()) {
        ctx.emit(Rule::RaceFirstWithSleepToTimeout, step.callee, 377121, &[]);
    }
}
fn runner(
    ctx: &mut RuleContext<'_>,
    callee: P<Node>,
) -> Option<(P<Node>, &'static str, &'static str)> {
    let target = if callee.kind() == Kind::CallExpression {
        callee.as_call_expression().expression
    } else {
        callee
    };
    for (name, replacement) in [
        ("runPromise", "runPromiseExit"),
        ("runPromiseWith", "runPromiseExitWith"),
    ] {
        if ctx.is_api(target, "Effect", name) {
            return Some((target, name, replacement));
        }
    }
    None
}
fn location_runner(callee: P<Node>, target: P<Node>) -> P<Node> {
    if target.kind() == Kind::PropertyAccessExpression {
        target
    } else {
        callee
    }
}
