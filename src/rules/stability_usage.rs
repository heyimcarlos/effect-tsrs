use std::collections::HashMap;

use tsrs_ast::{self as ast, Kind, Node, Symbol};
use tsrs_checker::{ContextFlags, Type};
use tsrs_core::P;

use super::{
    RuleContext,
    stability_common::{Allowlist, DeclaredCache, StabilityInfo},
};
use crate::Rule;

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    let mut declared = DeclaredCache::default();
    let mut contextual_types = HashMap::<P<Node>, Option<P<Type>>>::new();
    let mut constraint_types = HashMap::<P<Node>, Option<P<Type>>>::new();
    let mut bare_constraint_types = HashMap::<P<Node>, Option<P<Type>>>::new();
    for (rule, wanted, code) in [
        (Rule::ExperimentalApiUsage, 2, 377135),
        (Rule::UnstableApiUsage, 1, 377136),
    ] {
        if !ctx.enabled(rule) {
            continue;
        }
        let mut allow = Allowlist::new(ctx, wanted);
        super::walk(ctx.file.as_node(), &mut |node| {
            if ast::is_object_literal_element(node)
                && let Some(name) = node.name()
                && let Some(object) = node
                    .parent()
                    .filter(|p| p.kind() == Kind::ObjectLiteralExpression)
                && !ast::get_text_of_property_name(name).is_empty()
            {
                let contextual = *contextual_types.entry(object).or_insert_with(|| {
                    ctx.checker
                        .get_contextual_type_exported(object, ContextFlags::None)
                });
                if let Some(contextual) = contextual {
                    let mut properties = ctx
                        .checker
                        .get_property_symbols_from_contextual_type(node, contextual, false);
                    if properties
                        .iter()
                        .any(|symbol| symbol.value_declaration() == Some(node))
                    {
                        let mut resolved = false;
                        for bare in [false, true] {
                            let cache = if bare {
                                &mut bare_constraint_types
                            } else {
                                &mut constraint_types
                            };
                            let constraint = *cache.entry(object).or_insert_with(|| {
                                if bare {
                                    ctx.checker
                                        .effect_object_literal_bare_constraint_contextual_type(
                                            object,
                                        )
                                } else {
                                    ctx.checker
                                        .effect_object_literal_constraint_contextual_type(object)
                                }
                            });
                            if let Some(constraint) = constraint {
                                let candidates =
                                    ctx.checker.get_property_symbols_from_contextual_type(
                                        node, constraint, false,
                                    );
                                if candidates
                                    .iter()
                                    .any(|symbol| symbol.value_declaration() != Some(node))
                                {
                                    properties = candidates;
                                    resolved = true;
                                }
                            }
                            if resolved {
                                break;
                            }
                        }
                    }
                    for property in properties {
                        if property.value_declaration() == Some(node) {
                            continue;
                        }
                        let info = declared.symbol(ctx, Some(property));
                        if report(
                            ctx,
                            &mut allow,
                            rule,
                            code,
                            wanted,
                            name,
                            ast::get_text_of_property_name(name).to_string(),
                            info,
                        ) {
                            break;
                        }
                    }
                }
            }
            if node.kind() != Kind::Identifier
                || ast::is_declaration_name_or_import_property_name(node)
            {
                return;
            }
            let callee = node
                .parent()
                .filter(|p| p.kind() == Kind::PropertyAccessExpression && p.name() == Some(node))
                .unwrap_or(node);
            let mut info = StabilityInfo::default();
            let mut selected_declaration = None;
            if let Some(call) = callee.parent().filter(|p| {
                matches!(p.kind(), Kind::CallExpression | Kind::NewExpression)
                    && p.expression() == Some(callee)
            }) {
                let signature = ctx.checker.get_resolved_signature_exported(call);
                selected_declaration = signature.declaration();
                if selected_declaration.is_some() {
                    info = declared.signature(ctx, signature);
                    if info.level == 0 {
                        info.declaration = selected_declaration;
                    }
                }
            }
            let symbol = ctx.symbol(node);
            let reference = ctx.reference_symbol(node);
            let use_symbol = selected_declaration.is_none_or(|declaration| {
                !symbol_has_declaration(symbol, declaration)
                    && !symbol_has_declaration(reference, declaration)
            });
            if info.level == 0 && use_symbol {
                info = declared.symbol(ctx, symbol);
            }
            if info.level == 0 && use_symbol {
                info = declared.symbol(ctx, reference);
            }
            report(
                ctx,
                &mut allow,
                rule,
                code,
                wanted,
                node,
                node.text().to_owned(),
                info,
            );
        });
    }
}

fn symbol_has_declaration(symbol: Option<P<Symbol>>, declaration: P<Node>) -> bool {
    symbol.is_some_and(|s| s.declarations().contains(&declaration))
}

#[allow(clippy::too_many_arguments)]
fn report(
    ctx: &mut RuleContext<'_>,
    allow: &mut Allowlist,
    rule: Rule,
    code: i32,
    wanted: u8,
    node: P<Node>,
    name: String,
    info: StabilityInfo,
) -> bool {
    if info.level != wanted {
        return false;
    }
    let (allowed, api_name) = allow.decide(ctx, info.declaration);
    if allowed {
        return false;
    }
    ctx.emit(
        rule,
        node,
        code,
        &[if api_name.is_empty() { name } else { api_name }],
    );
    true
}
