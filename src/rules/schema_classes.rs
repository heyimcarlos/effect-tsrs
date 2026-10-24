use std::collections::HashMap;

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node, NodeFlags, Symbol, SymbolFlags};
use tsrs_checker::{ContextFlags, ObjectFlags, SignatureKind, Type, TypeFlags};
use tsrs_core::P;

use super::{RuleContext, walk};
use crate::Rule;

pub(super) struct Heritage {
    pub class_name: P<Node>,
    pub self_type: Option<P<Node>>,
    pub inner: P<Node>,
    pub outer: P<Node>,
    pub key: Option<P<Node>>,
    pub fields: Option<P<Node>>,
}

pub(super) fn extends_elements(node: P<Node>) -> Vec<P<Node>> {
    ast::get_extends_heritage_clause_elements(node).to_vec()
}

fn string_literal(node: Option<P<Node>>) -> Option<P<Node>> {
    node.filter(|node| node.kind() == Kind::StringLiteral)
}

/// Match the precise curried heritage form, checking the API's exported symbol.
pub(super) fn double_call_heritage(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    module: &str,
    member: &str,
) -> Option<Heritage> {
    let class_name = node.name()?;
    if module == "Effect" && member == "Service" && ctx.effect_version == 4 {
        return None;
    }
    for element in extends_elements(node) {
        if element.kind() != Kind::ExpressionWithTypeArguments {
            continue;
        }
        let outer = element.as_expression_with_type_arguments().expression();
        if outer.kind() != Kind::CallExpression {
            continue;
        }
        let inner = outer.as_call_expression().expression();
        if inner.kind() != Kind::CallExpression {
            continue;
        }
        let is_tag = (module == "Context" || module == "Effect") && member == "Tag";
        let types = if is_tag {
            outer.type_arguments()
        } else {
            inner.type_arguments()
        };
        let Some(&self_type) = types.first() else {
            continue;
        };
        if !ctx.is_api(inner.as_call_expression().expression(), module, member) {
            continue;
        }
        let schema_tagged = module == "Schema" && member.starts_with("Tagged");
        let key = if module == "Schema" || is_tag {
            string_literal(inner.arguments().first().copied())
        } else {
            string_literal(outer.arguments().first().copied())
        };
        return Some(Heritage {
            class_name,
            self_type: Some(self_type),
            inner,
            outer,
            key,
            fields: outer.arguments().get(usize::from(schema_tagged)).copied(),
        });
    }
    None
}

pub(super) struct DataHeritage {
    pub class_name: Option<P<Node>>,
    pub call: P<Node>,
    pub key: Option<P<Node>>,
    pub fields: Option<P<Node>>,
}

pub(super) fn data_error_heritage(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    tagged: bool,
) -> Option<DataHeritage> {
    for element in extends_elements(node) {
        if element.kind() != Kind::ExpressionWithTypeArguments {
            continue;
        }
        let call = element.as_expression_with_type_arguments().expression();
        let api = if tagged {
            if call.kind() != Kind::CallExpression {
                continue;
            }
            call.as_call_expression().expression()
        } else {
            call
        };
        if !ctx.is_api(api, "Data", if tagged { "TaggedError" } else { "Error" }) {
            continue;
        }
        // Heritage entity-name lookup can resolve the imported namespace even
        // when a local value shadows it. Check the value binding as the source
        // parser does before accepting an uncalled Data.Error reference.
        if !tagged && ast::is_entity_name_expression(api) {
            let root = ast::get_first_identifier(api);
            if root.kind() == Kind::Identifier {
                let value = ctx.checker.get_resolved_symbol(root);
                let mut value = ctx.resolve_symbol(value);
                if let Some(declaration) = value.value_declaration()
                    && declaration.kind() == Kind::VariableDeclaration
                    && declaration.parent().is_some_and(|parent| {
                        parent.kind() == Kind::VariableDeclarationList
                            && parent.flags().intersects(NodeFlags::Const)
                    })
                    && let Some(initializer) = declaration.as_variable_declaration().initializer()
                    && let Some(reference) =
                        ctx.reference_symbol(ast::skip_parentheses(initializer))
                {
                    value = reference;
                }
                if ctx
                    .reference_symbol(root)
                    .is_none_or(|reference| !ctx.same_symbol(value, reference))
                {
                    continue;
                }
            }
        }
        return Some(DataHeritage {
            class_name: node.name(),
            call,
            key: if tagged {
                string_literal(call.arguments().first().copied())
            } else {
                None
            },
            fields: element.type_arguments().first().copied(),
        });
    }
    None
}

fn schema_instance(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<Heritage> {
    ["Class", "TaggedClass", "Error", "TaggedError"]
        .into_iter()
        .find_map(|member| double_call_heritage(ctx, node, "Schema", member))
}

fn opaque(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<(P<Node>, Option<P<Node>>)> {
    for element in extends_elements(node) {
        if element.kind() != Kind::ExpressionWithTypeArguments {
            continue;
        }
        let outer = element.as_expression_with_type_arguments().expression();
        if outer.kind() != Kind::CallExpression {
            continue;
        }
        let inner = outer.as_call_expression().expression();
        if inner.kind() != Kind::CallExpression {
            continue;
        }
        let types = inner.type_arguments();
        if types.is_empty() || types.len() > 2 {
            continue;
        }
        if ctx.is_api(inner.as_call_expression().expression(), "Schema", "Opaque") {
            return Some((types[0], types.get(1).copied()));
        }
    }
    None
}

fn self_and_brand(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<(P<Node>, Option<P<Node>>)> {
    let result = schema_instance(ctx, node)?;
    Some((
        result.self_type?,
        result.inner.type_arguments().get(1).copied(),
    ))
}

fn allowed_constructor(node: P<Node>) -> bool {
    let Some(body) = node.body() else {
        return false;
    };
    if body.kind() != Kind::Block || body.statements().len() != 1 {
        return false;
    }
    let statement = body.statements()[0];
    if statement.kind() != Kind::ExpressionStatement {
        return false;
    }
    let call = statement.as_expression_statement().expression();
    if call.kind() != Kind::CallExpression
        || call.as_call_expression().expression().kind() != Kind::SuperKeyword
    {
        return false;
    }
    let params = node.parameters();
    let args = call.arguments();
    params.len() == 2
        && args.len() == 2
        && params.iter().zip(args).all(|(parameter, argument)| {
            parameter.name().is_some_and(|name| {
                name.kind() == Kind::Identifier
                    && argument.kind() == Kind::Identifier
                    && name.text() == argument.text()
            })
        })
}

fn same_payload_name(
    ctx: &mut RuleContext<'_>,
    member: P<Node>,
    error_name: Option<P<Node>>,
) -> bool {
    let Some(error_name) = error_name.filter(|node| node.kind() == Kind::StringLiteral) else {
        return false;
    };
    let literal = match member.kind() {
        Kind::PropertySignature => member
            .as_property_signature_declaration()
            .type_()
            .filter(|node| node.kind() == Kind::LiteralType)
            .map(|node| node.as_literal_type_node().literal()),
        Kind::PropertyAssignment => {
            let init = member.as_property_assignment().initializer();
            if init.kind() != Kind::CallExpression || init.arguments().len() != 1 {
                return false;
            }
            let expression = init.as_call_expression().expression();
            if !["Literal", "tag", "tagDefaultOmit"]
                .into_iter()
                .any(|name| ctx.is_api(expression, "Schema", name))
            {
                return false;
            }
            init.arguments().first().copied()
        }
        _ => None,
    };
    literal.is_some_and(|literal| {
        literal.kind() == Kind::StringLiteral && literal.text() == error_name.text()
    })
}

type ErrorPayload = (Option<P<Node>>, Option<P<Node>>);

fn payload(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<ErrorPayload> {
    if let Some(result) = data_error_heritage(ctx, node, true) {
        return Some((result.fields, result.key));
    }
    if let Some(result) = data_error_heritage(ctx, node, false) {
        return Some((result.fields, None));
    }
    if let Some(result) = double_call_heritage(ctx, node, "Schema", "TaggedError") {
        let tag = string_literal(result.outer.arguments().first().copied());
        return Some((
            result.fields,
            if ctx.effect_version == 4 {
                result.key.or(tag)
            } else {
                tag
            },
        ));
    }
    double_call_heritage(ctx, node, "Schema", "Error").map(|result| (result.fields, result.key))
}

fn schema_class_type(
    ctx: &mut RuleContext<'_>,
    ty: P<Type>,
    classes: &mut HashMap<P<Symbol>, bool>,
) -> bool {
    if !ty
        .object_flags()
        .intersects(ObjectFlags::Class | ObjectFlags::Reference)
    {
        return false;
    }
    let Some(symbol) = ty
        .symbol()
        .filter(|symbol| symbol.flags().intersects(SymbolFlags::Class))
    else {
        return false;
    };
    if let Some(&result) = classes.get(&symbol) {
        return result;
    }
    classes.insert(symbol, false);
    let direct = symbol.declarations().iter().any(|&node| {
        matches!(node.kind(), Kind::ClassDeclaration | Kind::ClassExpression)
            && self_and_brand(ctx, node).is_some()
    });
    let result = direct || {
        let declared = ctx.checker.get_declared_type_of_symbol(symbol);
        ctx.checker
            .get_base_types(declared)
            .to_vec()
            .into_iter()
            .any(|base| schema_class_type(ctx, base, classes))
    };
    classes.insert(symbol, result);
    result
}

fn in_v4_constructor(ctx: &mut RuleContext<'_>, mut node: P<Node>) -> bool {
    if ctx.effect_version != 4 {
        return false;
    }
    while let Some(parent) = node.parent() {
        match parent.kind() {
            Kind::ObjectLiteralExpression
            | Kind::PropertyAssignment
            | Kind::ArrayLiteralExpression
            | Kind::ParenthesizedExpression => {}
            Kind::CallExpression | Kind::NewExpression => {
                if !parent.arguments().contains(&node) {
                    return false;
                }
                let mut expression = parent.expression().unwrap();
                if parent.kind() == Kind::CallExpression {
                    if expression.kind() != Kind::PropertyAccessExpression {
                        return false;
                    }
                    let access = expression.as_property_access_expression();
                    if !["make", "makeOption", "makeEffect"].contains(&access.name().text()) {
                        return false;
                    }
                    expression = access.expression();
                }
                let ty = ctx.ty(expression);
                return ctx.is_schema_type(ty);
            }
            _ => return false,
        }
        node = parent;
    }
    false
}

fn native_error(ctx: &mut RuleContext<'_>, node: P<Node>, error: P<Symbol>) -> Option<P<Node>> {
    for element in extends_elements(node) {
        if element.kind() != Kind::ExpressionWithTypeArguments {
            continue;
        }
        let expression = element.as_expression_with_type_arguments().expression();
        let Some(symbol) = ctx.symbol(expression) else {
            continue;
        };
        let symbol = ctx.resolve_symbol(symbol);
        let matches = symbol == error || {
            let ty = ctx.ty(expression);
            let first = ctx
                .checker
                .get_signatures_of_type(ty, SignatureKind::Construct)
                .first()
                .copied();
            first.is_some_and(|signature| {
                ctx.checker.get_return_type_of_signature(signature).symbol() == Some(error)
            })
        };
        if matches {
            return Some(node.name().unwrap_or(expression));
        }
    }
    None
}

fn class_self(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<P<Node>> {
    for (module, member) in [
        ("Effect", "Service"),
        ("Context", "Service"),
        ("Context", "Tag"),
        ("Effect", "Tag"),
        ("Schema", "Class"),
        ("Schema", "TaggedClass"),
        ("Schema", "TaggedError"),
        ("Schema", "TaggedRequest"),
        ("Schema", "RequestClass"),
        ("SqlModel", "Class"),
        ("Model", "Class"),
    ] {
        if let Some(result) = double_call_heritage(ctx, node, module, member) {
            return result.self_type;
        }
    }
    None
}

fn self_name(ctx: &RuleContext<'_>, node: P<Node>) -> String {
    if node.kind() == Kind::TypeReference {
        let name = node.as_type_reference_node().type_name();
        if name.kind() == Kind::Identifier {
            return name.text().to_string();
        }
        if name.kind() == Kind::QualifiedName {
            return name.as_qualified_name().right().text().to_string();
        }
    }
    let file = ast::get_source_file_of_node(node).unwrap_or(ctx.file);
    let start = node.pos().expect_source("source type") as usize;
    let end = node.end().expect_source("source type") as usize;
    file.text().get(start..end).unwrap_or_default().to_string()
}

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::PreferSchemaTaggedError,
        Rule::ErrorPayloadShadowsName,
        Rule::OverriddenSchemaConstructor,
        Rule::SchemaOpaqueInstanceMember,
        Rule::SchemaClassMissingBrand,
        Rule::SchemaClassObjectLiteral,
        Rule::RedundantSchemaTagIdentifier,
        Rule::ClassSelfMismatch,
        Rule::ExtendsNativeError,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    let mut nodes = Vec::new();
    walk(ctx.file.as_node(), &mut |node| nodes.push(node));
    let mut classes = HashMap::new();
    let error = if ctx.enabled(Rule::ExtendsNativeError) {
        ctx.checker
            .resolve_name_exported("Error", None, SymbolFlags::Type, false)
    } else {
        None
    };
    for node in nodes {
        if node.kind() == Kind::ObjectLiteralExpression
            && ctx.enabled(Rule::SchemaClassObjectLiteral)
            && let Some(ty) = ctx
                .checker
                .get_contextual_type_exported(node, ContextFlags::empty())
        {
            let mut name = None;
            for member in ctx.union_members(ty) {
                if member
                    .flags()
                    .intersects(TypeFlags::Null | TypeFlags::Undefined)
                {
                    continue;
                }
                if !schema_class_type(ctx, member, &mut classes) {
                    name = None;
                    break;
                }
                if name.is_none() {
                    name = member.symbol().map(|symbol| symbol.name().to_string());
                }
            }
            if let Some(name) = name.filter(|name| !name.is_empty())
                && !in_v4_constructor(ctx, node)
            {
                ctx.emit(Rule::SchemaClassObjectLiteral, node, 377149, &[name]);
            }
        }
        if !matches!(node.kind(), Kind::ClassDeclaration | Kind::ClassExpression) {
            continue;
        }
        if ctx.enabled(Rule::ErrorPayloadShadowsName)
            && let Some((Some(fields), error_name)) = payload(ctx, node)
        {
            let members = match fields.kind() {
                Kind::TypeLiteral => fields.members(),
                Kind::ObjectLiteralExpression => {
                    fields.as_object_literal_expression().properties().nodes()
                }
                _ => &[],
            };
            for &member in members {
                if matches!(
                    member.kind(),
                    Kind::PropertySignature
                        | Kind::PropertyAssignment
                        | Kind::ShorthandPropertyAssignment
                ) && let Some(name) = member.name()
                    && ast::get_text_of_property_name(name) == "name"
                    && !same_payload_name(ctx, member, error_name)
                {
                    ctx.emit(Rule::ErrorPayloadShadowsName, name, 377145, &[]);
                }
            }
        }
        if ctx.effect_version == 4
            && ctx.enabled(Rule::SchemaClassMissingBrand)
            && let Some((self_type, None)) = self_and_brand(ctx, node).or_else(|| opaque(ctx, node))
        {
            ctx.emit(Rule::SchemaClassMissingBrand, self_type, 377141, &[]);
        }
        if ctx.enabled(Rule::SchemaOpaqueInstanceMember) && opaque(ctx, node).is_some() {
            for &member in node.members() {
                if !ast::has_syntactic_modifier(member, ModifierFlags::Static)
                    && matches!(
                        member.kind(),
                        Kind::PropertyDeclaration
                            | Kind::MethodDeclaration
                            | Kind::GetAccessor
                            | Kind::SetAccessor
                            | Kind::Constructor
                    )
                {
                    ctx.emit(Rule::SchemaOpaqueInstanceMember, member, 377102, &[]);
                }
            }
        }
        if node.kind() != Kind::ClassDeclaration {
            continue;
        }
        if ctx.enabled(Rule::PreferSchemaTaggedError)
            && let Some(result) = data_error_heritage(ctx, node, true)
        {
            ctx.emit(
                Rule::PreferSchemaTaggedError,
                result.class_name.unwrap_or(result.call),
                377139,
                &[],
            );
        }
        if ctx.enabled(Rule::OverriddenSchemaConstructor) {
            let extends_schema = extends_elements(node).into_iter().any(|element| {
                if element.kind() != Kind::ExpressionWithTypeArguments {
                    return false;
                }
                let ty = ctx.ty(element.as_expression_with_type_arguments().expression());
                ctx.is_schema_type(ty)
            });
            if extends_schema
                && let Some(&ctor) = node.members().iter().find(|&&member| {
                    member.kind() == Kind::Constructor && !allowed_constructor(member)
                })
            {
                ctx.emit(Rule::OverriddenSchemaConstructor, ctor, 377044, &[]);
            }
        }
        if ctx.enabled(Rule::RedundantSchemaTagIdentifier)
            && let Some(result) = ["TaggedClass", "TaggedError", "TaggedRequest"]
                .into_iter()
                .find_map(|member| double_call_heritage(ctx, node, "Schema", member))
            && let (Some(key), Some(tag)) = (
                result.key,
                string_literal(result.outer.arguments().first().copied()),
            )
            && key.text() == tag.text()
        {
            ctx.emit(
                Rule::RedundantSchemaTagIdentifier,
                key,
                377045,
                &[key.text().to_string()],
            );
        }
        if ctx.enabled(Rule::ClassSelfMismatch)
            && node.name().is_some()
            && let Some(self_type) = class_self(ctx, node)
        {
            let expected = node.name().unwrap().text().to_string();
            if self_name(ctx, self_type) != expected {
                ctx.emit(Rule::ClassSelfMismatch, self_type, 377046, &[expected]);
            }
        }
        if let Some(error) = error
            && let Some(location) = native_error(ctx, node, error)
        {
            ctx.emit(Rule::ExtendsNativeError, location, 377055, &[]);
        }
    }
}
