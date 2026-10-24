use std::collections::HashSet;

use tsrs_ast::{self as ast, Kind, Node, SymbolFlags};
use tsrs_checker::{
    CheckMode, LiteralValue, ObjectFlags, SignatureKind, Type, TypeFlags, evaluator,
};
use tsrs_core::{P, jsnum};

use crate::Rule;
use crate::rules::{RuleContext, walk};

const SYNC_METHODS: &[(&str, &str, &str)] = &[
    ("decodeSync", "decode", "decodeEffect"),
    ("decodeUnknownSync", "decodeUnknown", "decodeUnknownEffect"),
    ("encodeSync", "encode", "encodeEffect"),
    ("encodeUnknownSync", "encodeUnknown", "encodeUnknownEffect"),
];
const DECODERS: &[(&str, &str)] = &[
    ("decodeUnknownEffect", "decodeEffect"),
    ("decodeUnknownSync", "decodeSync"),
    ("decodeUnknownExit", "decodeExit"),
    ("decodeUnknownOption", "decodeOption"),
    ("decodeUnknownResult", "decodeResult"),
    ("decodeUnknownPromise", "decodePromise"),
];

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::SchemaStructWithTag,
        Rule::SchemaSync,
        Rule::SchemaSyncInEffect,
        Rule::SchemaNumber,
        Rule::SchemaLiteralNonFinite,
        Rule::SchemaUnionOfLiterals,
        Rule::NewSchemaClass,
        Rule::PreferSchemaTypeProperty,
        Rule::InstanceOfSchema,
        Rule::PreferTypedSchemaDecoder,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    let mut nodes = Vec::new();
    walk(ctx.file.as_node(), &mut |node| nodes.push(node));
    for &node in &nodes {
        match node.kind() {
            Kind::CallExpression => {
                if ctx.enabled(Rule::SchemaStructWithTag) {
                    struct_with_tag(ctx, node);
                }
                if ctx.enabled(Rule::SchemaSync) || ctx.enabled(Rule::SchemaSyncInEffect) {
                    sync(ctx, node);
                }
                if ctx.enabled(Rule::SchemaLiteralNonFinite) {
                    literal_non_finite(ctx, node);
                }
                if ctx.enabled(Rule::SchemaUnionOfLiterals) {
                    union_of_literals(ctx, node);
                }
            }
            Kind::NewExpression if ctx.effect_version == 4 && ctx.enabled(Rule::NewSchemaClass) => {
                let expr = node.as_new_expression().expression();
                if !ctx.cannot_be_effect_type(expr) {
                    let ty = ctx.ty(expr);
                    if ctx.is_schema_type(ty)
                        && !ctx
                            .checker
                            .get_signatures_of_type(ty, SignatureKind::Construct)
                            .is_empty()
                        && ctx.has_property(ty, "make")
                    {
                        let text = ctx.text(expr);
                        ctx.emit(Rule::NewSchemaClass, expr, 377094, &[text]);
                    }
                }
            }
            Kind::TypeReference if ctx.enabled(Rule::PreferSchemaTypeProperty) => {
                prefer_type_property(ctx, node)
            }
            Kind::BinaryExpression if ctx.enabled(Rule::InstanceOfSchema) => {
                let binary = node.as_binary_expression();
                if binary.operator_token().kind() == Kind::InstanceOfKeyword {
                    let ty = ctx.ty(binary.right());
                    if ctx.is_schema_type(ty) {
                        ctx.emit(Rule::InstanceOfSchema, node, 377042, &[]);
                    }
                }
            }
            _ => {}
        }
    }
    if ctx.enabled(Rule::SchemaNumber) {
        schema_numbers(ctx);
    }
    if ctx.enabled(Rule::PreferTypedSchemaDecoder) {
        typed_decoders(ctx, &nodes);
    }
}

fn struct_with_tag(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let call = node.as_call_expression();
    let args = call.arguments().nodes();
    if args.len() != 1
        || args[0].kind() != Kind::ObjectLiteralExpression
        || !ctx.is_api(call.expression(), "Schema", "Struct")
    {
        return;
    }
    for &prop in args[0].as_object_literal_expression().properties().nodes() {
        if prop.kind() != Kind::PropertyAssignment {
            continue;
        }
        let pa = prop.as_property_assignment();
        let Some(name) = prop.name() else {
            continue;
        };
        if name.kind() != Kind::Identifier || name.text() != "_tag" {
            continue;
        }
        let init = pa.initializer();
        if init.kind() != Kind::CallExpression {
            return;
        }
        let tag = init.as_call_expression();
        let values = tag.arguments().nodes();
        if values.len() == 1
            && values[0].kind() == Kind::StringLiteral
            && ctx.is_api(tag.expression(), "Schema", "Literal")
        {
            ctx.emit(Rule::SchemaStructWithTag, node, 377036, &[]);
        }
        return;
    }
}

fn sync(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let callee = node.as_call_expression().expression();
    let mut reference = ast::skip_parentheses(callee);
    if reference.kind() == Kind::ElementAccessExpression {
        reference = reference
            .as_element_access_expression()
            .argument_expression();
    }
    if ctx.enabled(Rule::SchemaSync) {
        for &(name, v3, v4) in SYNC_METHODS {
            if ctx.is_api(reference, "Schema", name)
                || ctx.is_api(reference, "ParseResult", name)
                || ctx.is_api(reference, "SchemaParser", name)
            {
                let replacement = if ctx.effect_version == 4 { v4 } else { v3 };
                let text = ctx.text(callee);
                ctx.emit(
                    Rule::SchemaSync,
                    callee,
                    377130,
                    &[text, replacement.into()],
                );
                break;
            }
        }
    }
    if ctx.enabled(Rule::SchemaSyncInEffect) {
        for &(name, v3, v4) in SYNC_METHODS {
            if (ctx.is_api(callee, "ParseResult", name) || ctx.is_api(callee, "SchemaParser", name))
                && ctx.effect_context(node) != 0
            {
                let replacement = if ctx.effect_version == 4 { v4 } else { v3 };
                let text = ctx.text(callee);
                ctx.emit(
                    Rule::SchemaSyncInEffect,
                    callee,
                    377037,
                    &[text, replacement.into()],
                );
                break;
            }
        }
    }
}

fn union_of_literals(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if ctx.effect_version == 4 {
        return;
    }
    let call = node.as_call_expression();
    let args = call.arguments().nodes();
    if args.len() < 2 || !ctx.is_api(call.expression(), "Schema", "Union") {
        return;
    }
    if args.iter().all(|arg| {
        arg.kind() == Kind::CallExpression
            && ctx.is_api(arg.as_call_expression().expression(), "Schema", "Literal")
    }) {
        ctx.emit(Rule::SchemaUnionOfLiterals, node, 377038, &[]);
    }
}

fn prefer_type_property(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let reference = node.as_type_reference_node();
    let args = node.type_arguments();
    let name = reference.type_name();
    if args.len() != 1 || args[0].kind() != Kind::TypeQuery || name.kind() != Kind::QualifiedName {
        return;
    }
    let outer = name.as_qualified_name();
    if outer.right().text() != "Type" || outer.left().kind() != Kind::QualifiedName {
        return;
    }
    let query = args[0].as_type_query_node();
    if query
        .type_arguments()
        .is_some_and(|args| !args.nodes().is_empty())
    {
        return;
    }
    if ctx.is_api(outer.left().as_qualified_name().right(), "Schema", "Schema") {
        ctx.emit(Rule::PreferSchemaTypeProperty, node, 377104, &[]);
    }
}

fn literal_non_finite(ctx: &mut RuleContext<'_>, node: P<Node>) {
    let call = node.as_call_expression();
    let args = call.arguments().nodes();
    if args.is_empty() {
        return;
    }
    let values = if ctx.is_api(call.expression(), "Schema", "Literals") {
        if args[0].kind() != Kind::ArrayLiteralExpression {
            return;
        }
        args[0].as_array_literal_expression().elements().nodes()
    } else if ctx.is_api(call.expression(), "Schema", "Literal")
        || ctx.is_api(call.expression(), "Schema", "tag")
    {
        &args[..1]
    } else {
        return;
    };
    for &value in values {
        let result = evaluator::evaluate(
            ctx,
            constant_entity,
            ast::OuterExpressionKinds::Parentheses,
            value,
            value,
        );
        if let Some(LiteralValue::Number(number)) = result.value
            && !number.0.is_finite()
        {
            let text = ctx.text(value);
            ctx.emit(Rule::SchemaLiteralNonFinite, value, 377106, &[text]);
        }
    }
}

fn constant_entity(
    ctx: &mut RuleContext<'_>,
    entity: P<Node>,
    location: P<Node>,
) -> evaluator::Result {
    let member = match entity.kind() {
        Kind::PropertyAccessExpression => Some((
            entity.as_property_access_expression().expression(),
            entity.as_property_access_expression().name().text(),
        )),
        Kind::ElementAccessExpression => {
            let access = entity.as_element_access_expression();
            ast::is_string_literal_like(access.argument_expression())
                .then(|| (access.expression(), access.argument_expression().text()))
        }
        _ => None,
    };
    if let Some((receiver, property)) = member
        && ctx.symbol(receiver).is_some_and(|symbol| {
            ctx.checker
                .resolve_name_exported("Number", None, SymbolFlags::Value, false)
                == Some(symbol)
        })
    {
        let value = match property {
            "POSITIVE_INFINITY" => Some(f64::INFINITY),
            "NEGATIVE_INFINITY" => Some(f64::NEG_INFINITY),
            "NaN" => Some(f64::NAN),
            _ => None,
        };
        if let Some(value) = value {
            return evaluator::new_result(
                Some(LiteralValue::Number(jsnum::Number(value))),
                false,
                false,
                false,
            );
        }
    }
    let result = ctx.checker.evaluate_entity_exported(entity, Some(location));
    if result.value.is_some() || entity.kind() != Kind::Identifier {
        return result;
    }
    let Some(symbol) = ctx.symbol(entity) else {
        return result;
    };
    if !ctx.checker.is_constant_variable_exported(symbol) {
        return result;
    }
    let Some(declaration) = symbol.value_declaration() else {
        return result;
    };
    if declaration.kind() != Kind::VariableDeclaration
        || declaration.type_node().is_some()
        || declaration == location
        || !ctx
            .checker
            .is_block_scoped_name_declared_before_use_exported(declaration, location)
    {
        return result;
    }
    let Some(init) = declaration.initializer() else {
        return result;
    };
    let constant = evaluator::evaluate(
        ctx,
        constant_entity,
        ast::OuterExpressionKinds::Parentheses,
        init,
        declaration,
    );
    evaluator::new_result(
        constant.value,
        constant.is_syntactically_string,
        constant.resolved_other_files
            || ast::get_source_file_of_node(location) != ast::get_source_file_of_node(declaration),
        true,
    )
}

fn schema_numbers(ctx: &mut RuleContext<'_>) {
    if ctx.effect_version != 4 {
        return;
    }
    fn visit(ctx: &mut RuleContext<'_>, node: P<Node>, out: &mut Vec<(P<Node>, &'static str)>) {
        if matches!(
            node.kind(),
            Kind::ImportDeclaration | Kind::ImportEqualsDeclaration
        ) {
            return;
        }
        if matches!(
            node.kind(),
            Kind::PropertyAccessExpression | Kind::Identifier
        ) {
            for (api, replacement) in [
                ("Number", "Schema.Finite"),
                ("NumberFromString", "Schema.FiniteFromString"),
            ] {
                if ctx.is_api(node, "Schema", api) {
                    let reference = if node.kind() == Kind::PropertyAccessExpression {
                        node.as_property_access_expression().name()
                    } else {
                        node
                    };
                    out.push((reference, replacement));
                    if node.kind() == Kind::PropertyAccessExpression {
                        return;
                    }
                    break;
                }
            }
        }
        node.for_each_child(&mut |child| {
            visit(ctx, child, out);
            false
        });
    }
    let mut matches = Vec::new();
    visit(ctx, ctx.file.as_node(), &mut matches);
    let flows = ctx.piping_flows(false);
    for (reference, replacement) in matches {
        let piped = flows.iter().any(|flow| {
            contains(flow.subject, reference)
                && flow.transformations.iter().any(|step| {
                    ctx.is_api(step.callee, "Schema", "check") && finite_predicate(ctx, &step.args)
                })
        });
        if !piped && !finite_method(ctx, reference) {
            ctx.emit(Rule::SchemaNumber, reference, 377098, &[replacement.into()]);
        }
    }
}

fn contains(ancestor: P<Node>, node: P<Node>) -> bool {
    ancestor.pos() <= node.pos() && node.end() <= ancestor.end()
}

fn finite_predicate(ctx: &mut RuleContext<'_>, args: &[P<Node>]) -> bool {
    args.iter().any(|&arg| {
        let arg = ast::skip_parentheses(arg);
        if arg.kind() != Kind::CallExpression {
            return false;
        }
        let callee = arg.as_call_expression().expression();
        ctx.is_api(callee, "Schema", "isFinite") || ctx.is_api(callee, "Schema", "isInt")
    })
}

fn finite_method(ctx: &mut RuleContext<'_>, reference: P<Node>) -> bool {
    let mut expression = reference;
    if expression.kind() == Kind::Identifier
        && expression.parent().is_some_and(|parent| {
            parent.kind() == Kind::PropertyAccessExpression && parent.name() == Some(expression)
        })
    {
        expression = expression.parent().unwrap();
    }
    while let Some(parent) = expression
        .parent()
        .filter(|node| node.kind() == Kind::PropertyAccessExpression)
    {
        let access = parent.as_property_access_expression();
        let Some(call) = parent
            .parent()
            .filter(|node| node.kind() == Kind::CallExpression)
        else {
            return false;
        };
        if access.expression() != expression || call.as_call_expression().expression() != parent {
            return false;
        }
        match access.name().text() {
            "annotate" => expression = call,
            "check" => return finite_predicate(ctx, call.as_call_expression().arguments().nodes()),
            _ => return false,
        }
    }
    false
}

fn typed_decoders(ctx: &mut RuleContext<'_>, nodes: &[P<Node>]) {
    if ctx.effect_version != 4 {
        return;
    }
    let mut handled = HashSet::new();
    let mut matches = Vec::new();
    for flow in ctx.piping_flows(false) {
        for (i, step) in flow.transformations.iter().enumerate() {
            let Some(&schema) = step.args.first() else {
                continue;
            };
            let input_node = (i == 0).then_some(flow.subject);
            let input_type = flow.input_type(ctx, i);
            if let Some(found) = typed_decoder(ctx, step.callee, schema, input_node, input_type)
                && handled.insert(found.0)
            {
                matches.push(found);
            }
        }
    }
    for &node in nodes {
        if node.kind() != Kind::CallExpression {
            continue;
        }
        let call = node.as_call_expression();
        if call.expression().kind() != Kind::CallExpression {
            continue;
        }
        let factory = call.expression().as_call_expression();
        let (Some(&input), Some(&schema)) = (
            call.arguments().nodes().first(),
            factory.arguments().nodes().first(),
        ) else {
            continue;
        };
        if let Some(found) = typed_decoder(ctx, factory.expression(), schema, Some(input), None)
            && handled.insert(found.0)
        {
            matches.push(found);
        }
    }
    matches.sort_by_key(|found| found.0.pos());
    for (name, unknown, typed) in matches {
        ctx.emit(
            Rule::PreferTypedSchemaDecoder,
            name,
            377112,
            &[typed.into(), unknown.into()],
        );
    }
}

fn typed_decoder(
    ctx: &mut RuleContext<'_>,
    callee: P<Node>,
    schema: P<Node>,
    input_node: Option<P<Node>>,
    input_type: Option<P<Type>>,
) -> Option<(P<Node>, &'static str, &'static str)> {
    let name = match callee.kind() {
        Kind::PropertyAccessExpression => callee.as_property_access_expression().name(),
        Kind::Identifier => callee,
        _ => return None,
    };
    if ctx.cannot_be_effect_type(schema) {
        return None;
    }
    let &(unknown, typed) = DECODERS.iter().find(|&&(unknown, _)| {
        ctx.is_api(callee, "Schema", unknown) || ctx.is_api(callee, "SchemaParser", unknown)
    })?;
    let schema_ty = ctx.ty(schema);
    let (_, encoded) = ctx.schema_types(schema_ty)?;
    let input_ty = input_type.or_else(|| input_node.map(|node| ctx.ty(node)))?;
    if input_ty
        .flags()
        .intersects(TypeFlags::Any | TypeFlags::Unknown)
        || unresolved_type(ctx, input_ty, &mut HashSet::new())
    {
        return None;
    }
    let assignable = if let Some(input) = input_node.map(ast::skip_parentheses)
        && matches!(
            input.kind(),
            Kind::ObjectLiteralExpression | Kind::ArrayLiteralExpression
        ) {
        ctx.checker.check_expression_with_contextual_type_exported(
            input,
            encoded,
            None,
            CheckMode::TypeOnly,
        )
    } else {
        input_ty
    };
    ctx.checker
        .is_type_assignable_to(assignable, encoded)
        .then_some((name, unknown, typed))
}

fn unresolved_type(ctx: &mut RuleContext<'_>, ty: P<Type>, seen: &mut HashSet<P<Type>>) -> bool {
    if !seen.insert(ty) {
        return false;
    }
    if ty.flags().intersects(TypeFlags::TypeVariable) {
        return true;
    }
    if ty.flags().intersects(TypeFlags::UnionOrIntersection)
        && ty
            .types()
            .iter()
            .any(|&member| unresolved_type(ctx, member, seen))
    {
        return true;
    }
    if ty.object_flags().intersects(ObjectFlags::Reference)
        && ctx
            .checker
            .get_type_arguments(ty)
            .iter()
            .any(|&arg| unresolved_type(ctx, arg, seen))
    {
        return true;
    }
    for &property in ctx.checker.get_properties_of_type(ty) {
        let property_ty = ctx.checker.get_type_of_symbol(property);
        if unresolved_type(ctx, property_ty, seen) {
            return true;
        }
    }
    ctx.checker
        .get_index_infos_of_type(ty)
        .iter()
        .any(|info| unresolved_type(ctx, info.value_type(), seen))
}
