use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node, NodeFlags, Symbol};
use tsrs_checker::{Signature, SignatureKind, Type, TypeFlags};
use tsrs_core::P;

use super::schema_classes::{data_error_heritage, double_call_heritage, extends_elements};
use super::{RuleContext, walk};
use crate::Rule;

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::ScopeInLayerEffect,
        Rule::StrictEffectProvide,
        Rule::MultipleEffectProvide,
        Rule::ProvideLayerSucceedToProvideService,
        Rule::LayerMergeAllWithDependencies,
        Rule::MissingEffectServiceDependency,
        Rule::LeakingRequirements,
        Rule::LazyEffect,
        Rule::GenericEffectServices,
        Rule::NonObjectEffectServiceType,
        Rule::DeterministicKeys,
        Rule::ServiceNotAsClass,
        Rule::PreferUnsafeConstructor,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    let mut nodes = Vec::new();
    walk(ctx.file.as_node(), &mut |node| nodes.push(node));
    for &node in &nodes {
        if node.kind() == Kind::CallExpression {
            if ctx.enabled(Rule::StrictEffectProvide) {
                strict_provide(ctx, node);
            }
            if ctx.enabled(Rule::LayerMergeAllWithDependencies) {
                layer_merge(ctx, node);
            }
            if ctx.enabled(Rule::PreferUnsafeConstructor) {
                unsafe_constructor(ctx, node);
            }
        }
        if node.kind() == Kind::ClassDeclaration && ctx.enabled(Rule::DeterministicKeys) {
            deterministic_keys(ctx, node);
        }
        if node.kind() == Kind::VariableDeclaration
            && ctx.effect_version == 4
            && ctx.enabled(Rule::ServiceNotAsClass)
        {
            service_not_class(ctx, node);
        }
    }
    for (rule, check) in [
        (
            Rule::GenericEffectServices,
            generic_services as fn(&mut RuleContext<'_>, P<Node>),
        ),
        (Rule::MissingEffectServiceDependency, missing_dependencies),
        (Rule::NonObjectEffectServiceType, non_object_service),
    ] {
        if ctx.effect_version == 3 && ctx.enabled(rule) {
            class_check_walk(ctx, ctx.file.as_node(), check);
        }
    }
    if ctx.effect_version == 3 && ctx.enabled(Rule::ScopeInLayerEffect) {
        scope_walk(ctx, ctx.file.as_node());
    }
    if ctx.enabled(Rule::LeakingRequirements) {
        leaking_walk(ctx, ctx.file.as_node());
    }
    if ctx
        .effect_version_string
        .is_some_and(|version| version.starts_with("4."))
        && ctx.enabled(Rule::LazyEffect)
    {
        for &stmt in ctx.file.statements().nodes() {
            lazy_statement(ctx, stmt);
        }
    }
    if ctx.enabled(Rule::MultipleEffectProvide)
        || (ctx.effect_version == 4 && ctx.enabled(Rule::ProvideLayerSucceedToProvideService))
    {
        provide_flows(ctx);
    }
}

fn class_check_walk(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    check: fn(&mut RuleContext<'_>, P<Node>),
) {
    if node.kind() == Kind::ClassDeclaration {
        let before = ctx.diagnostics.len();
        check(ctx, node);
        if ctx.diagnostics.len() != before {
            return;
        }
    }
    node.for_each_child(&mut |child| {
        class_check_walk(ctx, child, check);
        false
    });
}

fn layer_at(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<crate::semantic::Channels> {
    if ctx.cannot_be_effect_type(node) {
        return None;
    }
    let ty = ctx.ty(node);
    ctx.layer_type(ty)
}

fn has_scope(ctx: &mut RuleContext<'_>, ty: P<Type>) -> bool {
    ctx.union_members(ty)
        .into_iter()
        .any(|t| ctx.is_scope_type(t))
}

fn class_type(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<P<Type>> {
    let sym = ctx.symbol(node.name()?)?;
    ctx.checker.get_type_of_symbol_at_location(sym, Some(node))
}

fn scope_walk(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let matched = if node.kind() == Kind::CallExpression {
        let callee = node.as_call_expression().expression();
        ["effect", "effectDiscard", "effectContext"]
            .iter()
            .any(|name| ctx.is_api(callee, "Layer", name))
            && layer_at(ctx, node).is_some_and(|layer| has_scope(ctx, layer.r))
    } else if node.kind() == Kind::ClassDeclaration
        && node.as_class_declaration().heritage_clauses().is_some()
    {
        class_type(ctx, node)
            .and_then(|ty| ctx.checker.get_type_of_property_of_type(ty, "Default"))
            .and_then(|ty| ctx.layer_type(ty))
            .is_some_and(|layer| has_scope(ctx, layer.r))
    } else {
        false
    };
    if matched {
        ctx.emit(Rule::ScopeInLayerEffect, node, 377031, &[]);
    } else {
        node.for_each_child(&mut |child| {
            scope_walk(ctx, child);
            false
        });
    }
}

fn strict_provide(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let call = node.as_call_expression();
    if ctx.is_api(call.expression(), "Effect", "provide")
        && call
            .arguments()
            .nodes()
            .iter()
            .any(|arg| layer_at(ctx, *arg).is_some())
    {
        ctx.emit(Rule::StrictEffectProvide, node, 377032, &[]);
    }
}

fn local_option(node: P<Node>) -> bool {
    node.kind() == Kind::ObjectLiteralExpression
        && node
            .as_object_literal_expression()
            .properties()
            .nodes()
            .iter()
            .any(|prop| {
                prop.kind() == Kind::PropertyAssignment
                    && prop.name().is_some_and(|name| {
                        name.kind() == Kind::Identifier && name.text() == "local"
                    })
                    && prop.as_property_assignment().initializer().kind() == Kind::TrueKeyword
            })
}

fn provide_flows(ctx: &mut RuleContext<'_>) {
    for flow in ctx.piping_flows(true) {
        let mut chunk = Vec::new();
        for step in &flow.transformations {
            if ctx.enabled(Rule::MultipleEffectProvide) {
                let is_provide = ctx.is_api(step.callee, "Effect", "provide")
                    && !step.args.is_empty()
                    && !(ctx.effect_version == 4
                        && step.args.get(1).is_some_and(|n| local_option(*n)))
                    && layer_at(ctx, step.args[0]).is_some();
                let mut call = Some(step.callee);
                while call.is_some_and(|n| n.kind() != Kind::CallExpression) {
                    call = call.unwrap().parent();
                }
                if is_provide && let Some(call) = call {
                    chunk.push(call);
                } else {
                    emit_provide_chunk(ctx, &mut chunk);
                }
            }
            if ctx.effect_version == 4
                && ctx.enabled(Rule::ProvideLayerSucceedToProvideService)
                && step.args.len() == 1
                && ctx.is_api(step.callee, "Effect", "provide")
            {
                let inline = ast::skip_parentheses(step.args[0]);
                if let Some(inner) = ctx.longest_piping_flow_at(inline, false)
                    && inner.node == inline
                    && inner.transformations.len() == 1
                {
                    let single = &inner.transformations[0];
                    if single.args.len() == 1 && single.type_arguments.is_empty() {
                        let method = if ctx.is_api(single.callee, "Layer", "succeed") {
                            "provideService"
                        } else if ctx.is_api(single.callee, "Layer", "effect") {
                            "provideServiceEffect"
                        } else {
                            ""
                        };
                        if !method.is_empty() && !ctx.cannot_be_effect_type(single.args[0]) {
                            let ty = ctx.ty(single.args[0]);
                            if ctx.is_service_type(ty) || ctx.is_context_tag(ty) {
                                ctx.emit(
                                    Rule::ProvideLayerSucceedToProvideService,
                                    step.callee,
                                    377124,
                                    &[method.into()],
                                );
                            }
                        }
                    }
                }
            }
        }
        emit_provide_chunk(ctx, &mut chunk);
    }
}

fn emit_provide_chunk(ctx: &mut RuleContext<'_>, chunk: &mut Vec<P<Node>>) {
    if chunk.len() >= 2 {
        ctx.emit(Rule::MultipleEffectProvide, chunk[0], 377033, &[]);
    }
    chunk.clear();
}

fn layer_merge(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let call = node.as_call_expression();
    let args = call.arguments().nodes();
    if args.len() < 2 || !ctx.is_api(call.expression(), "Layer", "mergeAll") {
        return;
    }
    let mut layers = Vec::new();
    let mut provided = HashMap::new();
    for &arg in args {
        if let Some(layer) = layer_at(ctx, arg) {
            for ty in ctx.union_members(layer.a) {
                if !ty.flags().intersects(TypeFlags::Never)
                    && !ctx.checker.is_type_assignable_to(ty, layer.r)
                {
                    provided.insert(ty, arg);
                }
            }
            layers.push((arg, layer.r));
        }
    }
    let mut consumers: HashMap<P<Node>, Vec<P<Type>>> = HashMap::new();
    for (arg, requirements) in layers {
        for (&ty, &provider) in &provided {
            if arg != provider && ctx.checker.is_type_assignable_to(ty, requirements) {
                consumers.entry(provider).or_default().push(ty);
            }
        }
    }
    for &arg in args {
        if let Some(types) = consumers.get(&arg) {
            let mut names: Vec<_> = types.iter().map(|ty| ctx.type_string(*ty)).collect();
            names.sort();
            names.dedup();
            ctx.emit(
                Rule::LayerMergeAllWithDependencies,
                arg,
                377035,
                &[names.join(", ")],
            );
        }
    }
}

fn equivalent(ctx: &mut RuleContext<'_>, left: P<Type>, right: P<Type>) -> bool {
    ctx.checker.is_type_assignable_to(left, right) && ctx.checker.is_type_assignable_to(right, left)
}

// Source order is intentionally reversed: AppendToUniqueTypesMap uses a stack.
fn unique_types(
    ctx: &mut RuleContext<'_>,
    memory: &mut Vec<P<Type>>,
    ty: P<Type>,
    exclude_scope: bool,
) -> Vec<usize> {
    let mut result = Vec::new();
    for ty in ctx.union_members(ty).into_iter().rev() {
        if ty.flags().intersects(TypeFlags::Never) || (exclude_scope && ctx.is_scope_type(ty)) {
            continue;
        }
        let index = memory
            .iter()
            .position(|known| equivalent(ctx, *known, ty))
            .unwrap_or_else(|| {
                memory.push(ty);
                memory.len() - 1
            });
        result.push(index);
    }
    result
}

fn missing_dependencies(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let Some(service) = double_call_heritage(ctx, node, "Effect", "Service") else {
        return;
    };
    let Some(ty) = class_type(ctx, node) else {
        return;
    };
    let default = ctx
        .checker
        .get_type_of_property_of_type(ty, "DefaultWithoutDependencies")
        .or_else(|| ctx.checker.get_type_of_property_of_type(ty, "Default"));
    let Some(layer) = default.and_then(|ty| ctx.layer_type(ty)) else {
        return;
    };
    let mut memory = Vec::new();
    let required = unique_types(ctx, &mut memory, layer.r, false);
    if required.is_empty() {
        return;
    }
    let mut provided = HashSet::new();
    if let Some(&options) = service
        .outer
        .as_call_expression()
        .arguments()
        .nodes()
        .get(1)
    {
        let ty = ctx.ty(options);
        if let Some(dependencies) = ctx.checker.get_type_of_property_of_type(ty, "dependencies")
            && let Some(elements) = ctx.checker.get_number_index_type(dependencies)
        {
            for dep in ctx.union_members(elements) {
                if let Some(layer) = ctx.layer_type(dep) {
                    provided.extend(unique_types(ctx, &mut memory, layer.a, false));
                }
            }
        }
    }
    let names: Vec<_> = required
        .into_iter()
        .filter(|id| !provided.contains(id))
        .map(|id| ctx.type_string(memory[id]))
        .collect();
    if names.len() == 1 {
        ctx.emit(
            Rule::MissingEffectServiceDependency,
            service.class_name,
            377039,
            &[names[0].clone()],
        );
    } else if !names.is_empty() {
        ctx.emit(
            Rule::MissingEffectServiceDependency,
            service.class_name,
            377040,
            &[names
                .into_iter()
                .map(|name| format!("'{name}'"))
                .collect::<Vec<_>>()
                .join(", ")],
        );
    }
}

fn generic_services(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if node.name().is_some()
        && !node.type_parameters().is_empty()
        && node.as_class_declaration().heritage_clauses().is_some()
        && class_type(ctx, node).is_some_and(|ty| ctx.is_context_tag(ty))
    {
        ctx.emit(
            Rule::GenericEffectServices,
            node.name().unwrap(),
            377043,
            &[],
        );
    }
}

fn primitive(ctx: &mut RuleContext<'_>, ty: P<Type>) -> bool {
    let flags = TypeFlags::String
        | TypeFlags::Number
        | TypeFlags::Boolean
        | TypeFlags::StringLiteral
        | TypeFlags::NumberLiteral
        | TypeFlags::BooleanLiteral
        | TypeFlags::Undefined
        | TypeFlags::Null;
    ctx.union_members(ty)
        .iter()
        .any(|ty| ty.flags().intersects(flags))
}

fn non_object_service(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let Some(service) = double_call_heritage(ctx, node, "Effect", "Service") else {
        return;
    };
    let Some(&options) = service
        .outer
        .as_call_expression()
        .arguments()
        .nodes()
        .get(1)
    else {
        return;
    };
    if options.kind() != Kind::ObjectLiteralExpression {
        return;
    }
    for &prop in options.as_object_literal_expression().properties().nodes() {
        if prop.kind() != Kind::PropertyAssignment {
            continue;
        }
        let Some(name) = prop.name().filter(|name| name.kind() == Kind::Identifier) else {
            continue;
        };
        let value = prop.as_property_assignment().initializer();
        let ty = ctx.ty(value);
        let bad = match name.text() {
            "succeed" => primitive(ctx, ty),
            "sync" => {
                let signatures = ctx
                    .checker
                    .get_signatures_of_type(ty, SignatureKind::Call)
                    .to_vec();
                signatures.iter().any(|signature| {
                    let ret = ctx.checker.get_return_type_of_signature(*signature);
                    primitive(ctx, ret)
                })
            }
            "effect" | "scoped" => {
                if let Some(effect) = ctx.effect_type(ty) {
                    primitive(ctx, effect.a)
                } else {
                    let signatures = ctx
                        .checker
                        .get_signatures_of_type(ty, SignatureKind::Call)
                        .to_vec();
                    signatures.iter().any(|signature| {
                        let ret = ctx.checker.get_return_type_of_signature(*signature);
                        ctx.effect_type(ret)
                            .is_some_and(|effect| primitive(ctx, effect.a))
                    })
                }
            }
            _ => false,
        };
        if bad {
            ctx.emit(Rule::NonObjectEffectServiceType, name, 377048, &[]);
        }
    }
}

fn service_not_class(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let Some(init) = node
        .as_variable_declaration()
        .initializer()
        .filter(|n| n.kind() == Kind::CallExpression)
    else {
        return;
    };
    if !node.parent().is_some_and(|p| {
        p.kind() == Kind::VariableDeclarationList && p.flags().intersects(NodeFlags::Const)
    }) {
        return;
    }
    let call = init.as_call_expression();
    let types = init.type_arguments();
    if types.is_empty() || !ctx.is_api(call.expression(), "Context", "Service") {
        return;
    }
    let Some(name) = node.name() else {
        return;
    };
    let name = ctx.text(name);
    let types = types
        .iter()
        .map(|n| ctx.text(*n))
        .collect::<Vec<_>>()
        .join(", ");
    let args = call
        .arguments()
        .nodes()
        .iter()
        .map(|n| ctx.text(*n))
        .collect::<Vec<_>>()
        .join(", ");
    let suggestion = if args.is_empty() {
        format!("class {name} extends Context.Service<{name}, {types}>() {{}}")
    } else {
        format!("class {name} extends Context.Service<{name}, {types}>()({args}) {{}}")
    };
    ctx.emit(Rule::ServiceNotAsClass, init, 377056, &[suggestion]);
}

fn lazy_type(ctx: &mut RuleContext<'_>, ty: P<Type>) -> Option<&'static str> {
    let signatures = ctx.checker.get_signatures_of_type(ty, SignatureKind::Call);
    let [signature] = signatures else {
        return None;
    };
    if !signature.parameters().is_empty() || !signature.type_parameters().is_empty() {
        return None;
    }
    let ret = ctx.checker.get_return_type_of_signature(*signature);
    if ctx.strict_effect_type(ret).is_some() {
        Some("Effect")
    } else if ctx.layer_type(ret).is_some() {
        Some("Layer")
    } else if ctx.stream_type(ret).is_some() {
        Some("Stream")
    } else {
        None
    }
}

fn lazy_emit(ctx: &mut RuleContext<'_>, node: P<Node>, subject: String, ty: P<Type>) {
    if let Some(kind) = lazy_type(ctx, ty) {
        ctx.emit(Rule::LazyEffect, node, 377091, &[subject, kind.into()]);
    }
}

fn lazy_statement(ctx: &mut RuleContext<'_>, stmt: P<Node>) {
    if ast::get_combined_modifier_flags(stmt).intersects(ModifierFlags::Export) {
        if stmt.kind() == Kind::FunctionDeclaration && stmt.body().is_some() {
            if let Some(name) = stmt.name().filter(|name| name.kind() == Kind::Identifier) {
                let ty = ctx.ty(name);
                lazy_emit(
                    ctx,
                    name,
                    format!("Exported declaration '{}'", ctx.text(name)),
                    ty,
                );
            }
        } else if stmt.kind() == Kind::VariableStatement {
            for &decl in stmt
                .as_variable_statement()
                .declaration_list()
                .as_variable_declaration_list()
                .declarations()
                .nodes()
            {
                if let Some(name) = decl.name().filter(|name| name.kind() == Kind::Identifier) {
                    let ty = ctx.ty(name);
                    lazy_emit(
                        ctx,
                        name,
                        format!("Exported declaration '{}'", ctx.text(name)),
                        ty,
                    );
                }
            }
        } else if stmt.kind() == Kind::InterfaceDeclaration
            && let Some(name) = stmt.name()
        {
            for &member in stmt.as_interface_declaration().members().nodes() {
                if matches!(
                    member.kind(),
                    Kind::PropertySignature | Kind::MethodSignature
                ) && let Some(member_name) = member.name()
                {
                    let ty = ctx.ty(member_name);
                    lazy_emit(
                        ctx,
                        member_name,
                        format!(
                            "Interface '{}' member '{}'",
                            ctx.text(name),
                            ctx.text(member_name)
                        ),
                        ty,
                    );
                }
            }
        }
    }
    if stmt.kind() == Kind::ClassDeclaration
        && double_call_heritage(ctx, stmt, "Context", "Service").is_some()
        && let (Some(name), Some(ty)) = (stmt.name(), class_type(ctx, stmt))
        && let Some((_, shape)) = ctx.service_type(ty)
    {
        let props = ctx.checker.get_properties_of_type(shape).to_vec();
        for prop in props {
            if let Some(ty) = ctx.checker.get_type_of_symbol_at_location(prop, Some(name)) {
                lazy_emit(
                    ctx,
                    name,
                    format!("Service '{}' member '{}'", ctx.text(name), prop.name()),
                    ty,
                );
            }
        }
    }
}

fn leaking_walk(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let candidate = match node.kind() {
        Kind::ClassDeclaration if node.as_class_declaration().heritage_clauses().is_some() => {
            class_type(ctx, node).zip(node.name())
        }
        Kind::CallExpression => {
            let expr = node.as_call_expression().expression();
            if expr.kind() == Kind::PropertyAccessExpression
                && matches!(
                    expr.as_property_access_expression().name().text(),
                    "GenericTag" | "Service"
                )
            {
                Some((ctx.ty(node), node))
            } else {
                None
            }
        }
        _ => None,
    };
    if let Some((ty, report)) = candidate
        && let Some((_, shape)) = ctx.context_tag(ty).or_else(|| ctx.service_type(ty))
    {
        let mut names: Vec<_> = leaked_requirements(ctx, shape, node)
            .into_iter()
            .filter_map(|ty| {
                let name = ctx.type_string(ty);
                (!expected_leaking(ctx, report, &name)).then_some(name)
            })
            .collect();
        names.sort();
        if !names.is_empty() {
            ctx.emit(
                Rule::LeakingRequirements,
                report,
                377041,
                &[names.join(" | ")],
            );
        }
        return;
    }
    node.for_each_child(&mut |child| {
        leaking_walk(ctx, child);
        false
    });
}

fn leaked_requirements(
    ctx: &mut RuleContext<'_>,
    shape: P<Type>,
    location: P<Node>,
) -> Vec<P<Type>> {
    let properties = ctx.checker.get_properties_of_type(shape).to_vec();
    let mut memory = Vec::new();
    let mut shared: Option<Vec<usize>> = None;
    let mut count = 0;
    for prop in properties {
        let Some(ty) = ctx
            .checker
            .get_type_of_symbol_at_location(prop, Some(location))
        else {
            continue;
        };
        let effect = if let Some(effect) = ctx.effect_type(ty) {
            Some(effect)
        } else {
            let sigs = ctx
                .checker
                .get_signatures_of_type(ty, SignatureKind::Call)
                .to_vec();
            if let [sig] = sigs.as_slice() {
                let ret = ctx.checker.get_return_type_of_signature(*sig);
                ctx.effect_type(ret)
            } else {
                None
            }
        };
        if let Some(effect) = effect {
            count += 1;
            let ids = unique_types(ctx, &mut memory, effect.r, true);
            if let Some(shared) = &mut shared {
                shared.retain(|id| ids.contains(id));
            } else {
                shared = Some(ids);
            }
            if shared.as_ref().is_some_and(Vec::is_empty) {
                return Vec::new();
            }
        }
    }
    if count < 2 {
        return Vec::new();
    }
    shared
        .unwrap_or_default()
        .into_iter()
        .map(|id| memory[id])
        .filter(|ty| !leakable(ctx, *ty))
        .collect()
}

fn declaration_text(node: P<Node>) -> Option<&'static str> {
    let file = ast::get_source_file_of_node(node)?;
    let start = node.pos().expect_source("source declaration") as usize;
    let end = node.end().expect_source("source declaration") as usize;
    file.text().get(start..end)
}

fn leakable(ctx: &mut RuleContext<'_>, ty: P<Type>) -> bool {
    ty.symbol().is_some_and(|sym| {
        let sym = ctx.resolve_symbol(sym);
        sym.declarations().iter().any(|decl| {
            declaration_text(*decl)
                .is_some_and(|text| text.to_lowercase().contains("@effect-leakable-service"))
        })
    })
}

fn expected_leaking(ctx: &RuleContext<'_>, mut node: P<Node>, name: &str) -> bool {
    loop {
        let pos = node.pos().expect_source("source node");
        for comment in tsrs_scanner::get_leading_comment_ranges(ctx.file.text(), pos) {
            let text = &ctx.file.text()[comment.pos() as usize..comment.end() as usize];
            if text.lines().any(|line| {
                line.split_once("@effect-expect-leaking")
                    .is_some_and(|(_, suffix)| suffix.contains(name))
            }) {
                return true;
            }
        }
        if ast::is_statement(node) {
            return false;
        }
        let Some(parent) = node.parent() else {
            return false;
        };
        node = parent;
    }
}

fn deterministic_keys(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let Some(name) = node.name() else {
        return;
    };
    let mut found = None;
    for (module, member) in [
        ("Effect", "Service"),
        ("Context", "Tag"),
        ("Effect", "Tag"),
        ("Context", "Service"),
    ] {
        if let Some(h) = double_call_heritage(ctx, node, module, member) {
            let Some(key) = h.key else {
                return;
            };
            found = Some((key, "service"));
            break;
        }
    }
    if found.is_none() {
        if let Some(h) = data_error_heritage(ctx, node, true) {
            let Some(key) = h.key else {
                return;
            };
            found = Some((key, "error"));
        } else if let Some(h) = double_call_heritage(ctx, node, "Schema", "TaggedError") {
            let Some(key) = h.key else {
                return;
            };
            found = Some((key, "error"));
        }
    }
    if found.is_none() && ctx.option_bool("extendedKeyDetection", false) {
        found = custom_key(ctx, node).map(|key| (key, "custom"));
    }
    let Some((key, target)) = found.filter(|(key, _)| key.kind() == Kind::StringLiteral) else {
        return;
    };
    let expected = build_key(ctx, &ctx.text(name), target);
    if !expected.is_empty() && key.text() != expected {
        ctx.emit(Rule::DeterministicKeys, key, 377049, &[expected]);
    }
}

fn custom_key(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<P<Node>> {
    let mut queue: VecDeque<_> = extends_elements(node).into();
    while let Some(node) = queue.pop_front() {
        if node.kind() == Kind::CallExpression {
            let sig = ctx.checker.get_resolved_signature_exported(node);
            for (&arg, &param) in node
                .as_call_expression()
                .arguments()
                .nodes()
                .iter()
                .zip(sig.parameters())
            {
                if arg.kind() == Kind::StringLiteral
                    && param.declarations().iter().any(|decl| {
                        declaration_text(*decl)
                            .is_some_and(|text| text.to_lowercase().contains("@effect-identifier"))
                    })
                {
                    return Some(arg);
                }
            }
        }
        node.for_each_child(&mut |child| {
            queue.push_back(child);
            false
        });
    }
    None
}

fn package(path: &Path) -> Option<(PathBuf, String)> {
    for dir in path.parent()?.ancestors() {
        match std::fs::read(dir.join("package.json")) {
            Ok(data) => {
                let json: serde_json::Value = serde_json::from_slice(&data).ok()?;
                return Some((
                    dir.to_path_buf(),
                    json.get("name")
                        .and_then(serde_json::Value::as_str)
                        .unwrap_or("")
                        .to_owned(),
                ));
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return None,
        }
    }
    None
}

fn build_key(ctx: &RuleContext<'_>, name: &str, target: &str) -> String {
    let file = Path::new(ctx.file.file_name());
    let package_name = package(file).map(|(_, name)| name).unwrap_or_default();
    let metadata = ctx.program.get_source_file_meta_data(ctx.file.path());
    let root = if !metadata.package_json_directory.is_empty() {
        PathBuf::from(&metadata.package_json_directory)
    } else {
        let config = &ctx.program.options().config_file_path;
        if !config.is_empty() {
            Path::new(config)
                .parent()
                .unwrap_or(Path::new(""))
                .to_path_buf()
        } else {
            PathBuf::from(ctx.program.common_source_directory())
        }
    };
    let mut filename = file.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    if filename.eq_ignore_ascii_case("index") {
        filename = "";
    }
    let Some(mut subdir) = file
        .parent()
        .and_then(|dir| dir.to_str())
        .and_then(|dir| dir.strip_prefix(root.to_str().unwrap_or("")))
        .map(str::to_owned)
    else {
        return String::new();
    };
    if !subdir.ends_with('/') {
        subdir.push('/');
    }
    subdir = subdir.strip_prefix('/').unwrap_or(&subdir).to_owned();
    let configured = ctx
        .options
        .get("keyPatterns")
        .and_then(serde_json::Value::as_array)
        .map(|patterns| {
            patterns
                .iter()
                .filter(|p| p.is_object())
                .cloned()
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let patterns = if configured.is_empty() {
        vec![
            serde_json::json!({"target":"service"}),
            serde_json::json!({"target":"custom"}),
        ]
    } else {
        configured
    };
    for pattern in patterns {
        if pattern
            .get("target")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("service")
            != target
        {
            continue;
        }
        let skips = pattern
            .get("skipLeadingPath")
            .and_then(serde_json::Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(serde_json::Value::as_str)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_else(|| vec!["src/"]);
        for skip in skips {
            if let Some(stripped) = subdir.strip_prefix(skip) {
                subdir = stripped.to_owned();
                break;
            }
        }
        let formula = pattern
            .get("pattern")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("default");
        let mut parts = if formula == "identifier" {
            vec![name]
        } else if formula == "package-identifier" {
            vec![package_name.as_str(), filename]
        } else {
            vec![package_name.as_str(), &subdir, filename]
        };
        if formula != "identifier" && !filename.eq_ignore_ascii_case(name) {
            parts.push(name);
        }
        let key = parts
            .into_iter()
            .map(|part| part.strip_prefix('/').unwrap_or(part))
            .map(|part| part.strip_suffix('/').unwrap_or(part))
            .filter(|part| !part.trim().is_empty())
            .collect::<Vec<_>>()
            .join("/");
        return if formula == "default-hashed" {
            cyrb53(&key)
        } else {
            key
        };
    }
    String::new()
}

fn cyrb53(text: &str) -> String {
    let mut h1 = 0xdeadbeefu32;
    let mut h2 = 0x41c6ce57u32;
    for byte in text.bytes() {
        h1 = (h1 ^ byte as u32).wrapping_mul(2654435761);
        h2 = (h2 ^ byte as u32).wrapping_mul(1597334677);
    }
    h1 = (h1 ^ (h1 >> 16)).wrapping_mul(2246822507) ^ (h2 ^ (h2 >> 13)).wrapping_mul(3266489909);
    h2 = (h2 ^ (h2 >> 16)).wrapping_mul(2246822507) ^ (h1 ^ (h1 >> 13)).wrapping_mul(3266489909);
    format!("{h2:08x}{h1:08x}")
}

fn unsafe_constructor(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let outer = node.as_call_expression();
    let [arg] = outer.arguments().nodes() else {
        return;
    };
    let inner = ast::skip_parentheses(*arg);
    if inner.kind() != Kind::CallExpression {
        return;
    }
    let call = inner.as_call_expression();
    let callee = call.expression();
    let name_node = match callee.kind() {
        Kind::Identifier => callee,
        Kind::PropertyAccessExpression => callee.as_property_access_expression().name(),
        _ => return,
    };
    if name_node.kind() != Kind::Identifier
        || call
            .arguments()
            .nodes()
            .iter()
            .any(|arg| arg.kind() == Kind::SpreadElement)
        || !ctx.is_api(outer.expression(), "Effect", "runSync")
    {
        return;
    }
    let ty = ctx.ty(inner);
    let Some(effect) = ctx.effect_type(ty) else {
        return;
    };
    if !effect.e.flags().intersects(TypeFlags::Never)
        || !effect.r.flags().intersects(TypeFlags::Never)
    {
        return;
    }
    let Some(symbol) = ctx.reference_symbol(callee) else {
        return;
    };
    let name = symbol.name();
    if name.is_empty() || name.ends_with("Unsafe") {
        return;
    }
    let unsafe_name = format!("{name}Unsafe");
    for &decl in symbol.declarations() {
        let Some(file) = ast::get_source_file_of_node(decl) else {
            continue;
        };
        if !file.is_declaration_file() || !ctx.is_source_file_in_package(file, "effect") {
            continue;
        }
        let Some(module) = ctx
            .checker
            .get_symbol_of_declaration_exported(file.as_node())
        else {
            continue;
        };
        let Some(export) = ctx
            .checker
            .try_get_member_in_module_exports_and_properties(name, module)
        else {
            continue;
        };
        if !ctx.same_symbol(export, symbol) {
            continue;
        }
        let Some(sibling) = ctx
            .checker
            .try_get_member_in_module_exports_and_properties(&unsafe_name, module)
            .map(|s| ctx.resolve_symbol(s))
        else {
            continue;
        };
        if !unsafe_sibling_matches(ctx, inner, sibling, effect.a) {
            continue;
        }
        let replacement = if callee.kind() == Kind::PropertyAccessExpression {
            let text = ctx.text(callee);
            format!(
                "{}{unsafe_name}",
                text.strip_suffix(name_node.text()).unwrap_or(&text)
            )
        } else {
            unsafe_name.clone()
        };
        let original = format!(
            "{}({}(...))",
            ctx.text(outer.expression()),
            ctx.text(callee)
        );
        ctx.emit(
            Rule::PreferUnsafeConstructor,
            node,
            377109,
            &[original, format!("{replacement}(...)")],
        );
        return;
    }
}

fn accepts_argument(ctx: &mut RuleContext<'_>, arg: P<Type>, param: P<Type>) -> bool {
    if param.flags().intersects(TypeFlags::TypeParameter) {
        ctx.checker
            .get_constraint_of_type_parameter(param)
            .is_none_or(|constraint| accepts_argument(ctx, arg, constraint))
    } else {
        ctx.checker.is_type_assignable_to(arg, param)
    }
}

fn accepts_arguments(ctx: &mut RuleContext<'_>, signature: P<Signature>, args: &[P<Node>]) -> bool {
    let params = signature.parameters();
    if args.len() < signature.min_argument_count()
        || (args.len() > params.len() && !signature.has_rest_parameter())
    {
        return false;
    }
    for (i, &arg) in args.iter().enumerate() {
        if signature.has_rest_parameter() && i >= params.len().saturating_sub(1) {
            break;
        }
        let Some(&param) = params.get(i) else {
            return false;
        };
        let arg_type = ctx.ty(arg);
        let param_type = ctx.checker.get_type_of_symbol(param);
        if !accepts_argument(ctx, arg_type, param_type) {
            return false;
        }
    }
    true
}

fn unsafe_sibling_matches(
    ctx: &mut RuleContext<'_>,
    call: P<Node>,
    sibling: P<Symbol>,
    success: P<Type>,
) -> bool {
    let ty = ctx.checker.get_type_of_symbol(sibling);
    let signatures = ctx
        .checker
        .get_signatures_of_type(ty, SignatureKind::Call)
        .to_vec();
    let resolved = ctx.checker.get_resolved_signature_exported(call);
    for sig in signatures {
        if !accepts_arguments(ctx, sig, call.as_call_expression().arguments().nodes()) {
            continue;
        }
        let ret = ctx.checker.get_return_type_of_signature(sig);
        let actual = ctx.checker.new_function_type_exported(
            sig.type_parameters(),
            sig.this_parameter(),
            sig.parameters(),
            ret,
        );
        let expected =
            ctx.checker
                .new_function_type_exported(&[], None, resolved.parameters(), success);
        if !ctx.checker.is_type_assignable_to(actual, expected) {
            continue;
        }
        if !sig.type_parameters().is_empty() || equivalent(ctx, ret, success) {
            return true;
        }
    }
    false
}
