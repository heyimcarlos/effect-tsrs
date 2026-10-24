use tsrs_ast::{self as ast, Kind, Node, Symbol, SymbolFlags};
use tsrs_checker::{SignatureKind, Type, TypeFlags};
use tsrs_core::P;

use super::Channels;
use crate::rules::RuleContext;

impl RuleContext<'_> {
    pub(crate) fn safe_ty(&mut self, node: P<Node>) -> Option<P<Type>> {
        if !type_at_location_candidate(node) {
            return None;
        }
        Some(self.ty(node))
    }

    pub(crate) fn ty(&mut self, node: P<Node>) -> P<Type> {
        if let Some(&ty) = self.semantic.types.get(&node) {
            return ty;
        }
        let ty = self
            .checker
            .get_checked_type_of_expression(node)
            .unwrap_or_else(|| self.checker.get_type_at_location(node));
        self.semantic.types.insert(node, ty);
        ty
    }

    pub(crate) fn type_string(&mut self, ty: P<Type>) -> String {
        self.checker.type_to_string_exported(ty)
    }

    pub(crate) fn has_property(&mut self, ty: P<Type>, name: &str) -> bool {
        self.checker.get_property_of_type(ty, name).is_some()
    }

    pub(crate) fn covariant_type(&mut self, ty: P<Type>, name: &str) -> Option<P<Type>> {
        let prop = self.checker.get_type_of_property_of_type(ty, name)?;
        let [signature] = self
            .checker
            .get_signatures_of_type(prop, SignatureKind::Call)
        else {
            return None;
        };
        if !signature.type_parameters().is_empty() {
            return None;
        }
        Some(self.checker.get_return_type_of_signature(*signature))
    }

    pub(crate) fn contravariant_type(&mut self, ty: P<Type>, name: &str) -> Option<P<Type>> {
        let prop = self.checker.get_type_of_property_of_type(ty, name)?;
        let [signature] = self
            .checker
            .get_signatures_of_type(prop, SignatureKind::Call)
        else {
            return None;
        };
        if !signature.type_parameters().is_empty() {
            return None;
        }
        let parameter = *signature.parameters().first()?;
        Some(self.checker.get_type_of_symbol(parameter))
    }

    fn effect_variance(&mut self, ty: P<Type>) -> Option<Channels> {
        Some(Channels {
            a: self.covariant_type(ty, "_A")?,
            e: self.covariant_type(ty, "_E")?,
            r: self.covariant_type(ty, "_R")?,
        })
    }

    fn layer_variance(&mut self, ty: P<Type>) -> Option<Channels> {
        Some(Channels {
            a: self.contravariant_type(ty, "_ROut")?,
            e: self.covariant_type(ty, "_E")?,
            r: self.covariant_type(ty, "_RIn")?,
        })
    }

    fn variance_candidates(&mut self, ty: P<Type>, preferred: &str) -> Vec<P<Symbol>> {
        let mut props: Vec<_> = self
            .checker
            .get_properties_of_type(ty)
            .iter()
            .copied()
            .filter(|prop| {
                prop.flags().intersects(SymbolFlags::Property)
                    && !prop.flags().intersects(SymbolFlags::Optional)
                    && prop.value_declaration().is_some()
            })
            .collect();
        props.sort_by_key(|prop| !prop.name().contains(preferred));
        props
    }

    pub(crate) fn effect_type(&mut self, ty: P<Type>) -> Option<Channels> {
        if let Some(&result) = self.semantic.effects.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 4 {
            self.checker
                .get_type_of_property_of_type(ty, "~effect/Effect")
                .and_then(|variance| self.effect_variance(variance))
        } else {
            self.variance_candidates(ty, "EffectTypeId")
                .into_iter()
                .find_map(|prop| {
                    let variance = self.checker.get_type_of_symbol_at_location(prop, None)?;
                    self.effect_variance(variance)
                })
        };
        self.semantic.effects.insert(ty, result);
        result
    }

    pub(crate) fn strict_effect_type(&mut self, ty: P<Type>) -> Option<Channels> {
        if ty.symbol().is_none_or(|symbol| symbol.name() != "Effect") {
            return None;
        }
        self.effect_type(ty)
    }

    pub(crate) fn effect_yieldable_type(&mut self, ty: P<Type>) -> Option<Channels> {
        if let Some(channels) = self.effect_type(ty) {
            return Some(channels);
        }
        if self.detected_effect_version != 4 {
            return None;
        }
        let as_effect = self.checker.get_type_of_property_of_type(ty, "asEffect")?;
        self.checker
            .get_signatures_of_type(as_effect, SignatureKind::Call)
            .iter()
            .find_map(|&signature| {
                let result = self.checker.get_return_type_of_signature(signature);
                self.effect_type(result)
            })
    }

    pub(crate) fn stream_type(&mut self, ty: P<Type>) -> Option<Channels> {
        if let Some(&result) = self.semantic.streams.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 4 {
            self.checker
                .get_type_of_property_of_type(ty, "~effect/Stream")
                .and_then(|variance| self.effect_variance(variance))
        } else {
            self.effect_type(ty)
        };
        self.semantic.streams.insert(ty, result);
        result
    }

    pub(crate) fn layer_type(&mut self, ty: P<Type>) -> Option<Channels> {
        if let Some(&result) = self.semantic.layers.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 4 {
            self.checker
                .get_type_of_property_of_type(ty, "~effect/Layer")
                .and_then(|variance| self.layer_variance(variance))
        } else {
            self.variance_candidates(ty, "LayerTypeId")
                .into_iter()
                .find_map(|prop| {
                    let variance = self.checker.get_type_of_symbol_at_location(prop, None)?;
                    self.layer_variance(variance)
                })
        };
        self.semantic.layers.insert(ty, result);
        result
    }

    pub(crate) fn schema_types(&mut self, ty: P<Type>) -> Option<(P<Type>, P<Type>)> {
        if let Some(&result) = self.semantic.schemas.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 4 {
            self.checker
                .get_type_of_property_of_type(ty, "~effect/Schema/Schema")
                .and_then(|_| {
                    Some((
                        self.checker.get_type_of_property_of_type(ty, "Type")?,
                        self.checker.get_type_of_property_of_type(ty, "Encoded")?,
                    ))
                })
        } else if self.has_property(ty, "ast") {
            self.variance_candidates(ty, "TypeId")
                .into_iter()
                .find_map(|prop| {
                    let variance = self.checker.get_type_of_symbol_at_location(prop, None)?;
                    let a = self.covariant_type(variance, "_A")?;
                    let i = self.covariant_type(variance, "_I")?;
                    self.covariant_type(variance, "_R")?;
                    Some((a, i))
                })
        } else {
            None
        };
        self.semantic.schemas.insert(ty, result);
        result
    }

    pub(crate) fn is_schema_type(&mut self, ty: P<Type>) -> bool {
        self.schema_types(ty).is_some()
    }

    pub(crate) fn is_pipeable_type(&mut self, ty: P<Type>) -> bool {
        self.checker
            .get_type_of_property_of_type(ty, "pipe")
            .is_some_and(|pipe| {
                !self
                    .checker
                    .get_signatures_of_type(pipe, SignatureKind::Call)
                    .is_empty()
            })
    }

    pub(crate) fn service_type(&mut self, ty: P<Type>) -> Option<(P<Type>, P<Type>)> {
        if let Some(&result) = self.semantic.services.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 4
            && self.is_pipeable_type(ty)
            && self.has_property(ty, "~effect/Context/Service")
        {
            self.checker
                .get_type_of_property_of_type(ty, "Identifier")
                .and_then(|identifier| {
                    Some((
                        identifier,
                        self.checker.get_type_of_property_of_type(ty, "Service")?,
                    ))
                })
        } else {
            None
        };
        self.semantic.services.insert(ty, result);
        result
    }

    pub(crate) fn is_service_type(&mut self, ty: P<Type>) -> bool {
        self.service_type(ty).is_some()
    }

    pub(crate) fn context_tag(&mut self, ty: P<Type>) -> Option<(P<Type>, P<Type>)> {
        if let Some(&result) = self.semantic.context_tags.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 3 && self.is_pipeable_type(ty) {
            self.variance_candidates(ty, "TypeId")
                .into_iter()
                .find_map(|prop| {
                    let variance = self.checker.get_type_of_symbol_at_location(prop, None)?;
                    Some((
                        self.covariant_type(variance, "_Identifier")?,
                        self.covariant_type(variance, "_Service")?,
                    ))
                })
        } else {
            None
        };
        self.semantic.context_tags.insert(ty, result);
        result
    }

    pub(crate) fn is_context_tag(&mut self, ty: P<Type>) -> bool {
        self.context_tag(ty).is_some()
    }

    pub(crate) fn is_scope_type(&mut self, ty: P<Type>) -> bool {
        if let Some(&result) = self.semantic.scopes.get(&ty) {
            return result;
        }
        let result = if self.detected_effect_version == 4 {
            self.has_property(ty, "~effect/Scope")
        } else {
            self.is_pipeable_type(ty)
                && self
                    .variance_candidates(ty, "ScopeTypeId")
                    .iter()
                    .any(|symbol| symbol.name().contains("ScopeTypeId"))
        };
        self.semantic.scopes.insert(ty, result);
        result
    }

    pub(crate) fn union_members(&mut self, ty: P<Type>) -> Vec<P<Type>> {
        let mut out = Vec::new();
        fn collect(ty: P<Type>, out: &mut Vec<P<Type>>) {
            if ty.flags().intersects(TypeFlags::Union) {
                for &member in ty.types() {
                    collect(member, out);
                }
            } else {
                out.push(ty);
            }
        }
        collect(ty, &mut out);
        out
    }

    pub(crate) fn is_global_error_type(&mut self, ty: P<Type>) -> bool {
        if let Some(&result) = self.semantic.global_errors.get(&ty) {
            return result;
        }
        let result = !ty.flags().intersects(TypeFlags::Any | TypeFlags::Unknown)
            && self
                .checker
                .resolve_name_exported("Error", None, SymbolFlags::Type, false)
                .is_some_and(|symbol| {
                    let error = self.checker.get_declared_type_of_symbol(symbol);
                    self.checker.is_type_assignable_to(ty, error)
                        && self.checker.is_type_assignable_to(error, ty)
                });
        self.semantic.global_errors.insert(ty, result);
        result
    }

    pub(crate) fn is_yieldable_error_type(&mut self, ty: P<Type>) -> bool {
        if ty.flags().intersects(TypeFlags::Any | TypeFlags::Never) {
            return false;
        }
        if let Some(&result) = self.semantic.yieldable_errors.get(&ty) {
            return result;
        }
        let target = if let Some(target) = self.semantic.yieldable_error_type {
            target
        } else {
            let target = self.program.source_files().iter().find_map(|&file| {
                if !self.is_source_file_in_package(file, "effect") {
                    return None;
                }
                let module = self
                    .checker
                    .get_symbol_of_declaration_exported(file.as_node())?;
                self.checker
                    .try_get_member_in_module_exports_and_properties("Cause", module)?;
                let exported = self
                    .checker
                    .try_get_member_in_module_exports_and_properties("YieldableError", module)?;
                let exported = self.resolve_symbol(exported);
                Some(self.checker.get_declared_type_of_symbol(exported))
            });
            self.semantic.yieldable_error_type = Some(target);
            target
        };
        let result = target.is_some_and(|target| self.checker.is_type_assignable_to(ty, target));
        self.semantic.yieldable_errors.insert(ty, result);
        result
    }

    /// Like the source parser, returns the Promise type itself, not its value
    /// channel, and excludes arbitrary thenables and PromiseLike.
    pub(crate) fn promise_type(&mut self, ty: P<Type>) -> Option<P<Type>> {
        if let Some(&result) = self.semantic.promises.get(&ty) {
            return result;
        }
        let result = self
            .checker
            .resolve_name_exported("Promise", None, SymbolFlags::Type, false)
            .and_then(|symbol| {
                let global = self.checker.get_declared_type_of_symbol(symbol);
                (ty == global
                    || (ty.flags().intersects(TypeFlags::Object) && ty.target() == Some(global)))
                .then_some(ty)
            });
        self.semantic.promises.insert(ty, result);
        result
    }

    pub(crate) fn cannot_be_effect_type(&self, node: P<Node>) -> bool {
        match node.kind() {
            Kind::ArrayLiteralExpression
            | Kind::ArrowFunction
            | Kind::FunctionExpression
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::TemplateExpression
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::NullKeyword
            | Kind::RegularExpressionLiteral
            | Kind::PrefixUnaryExpression
            | Kind::VoidExpression
            | Kind::TypeOfExpression => true,
            Kind::StringLiteral => node
                .parent()
                .is_none_or(|parent| parent.name() != Some(node)),
            Kind::ObjectLiteralExpression if self.detected_effect_version == 4 => node
                .as_object_literal_expression()
                .properties()
                .nodes()
                .iter()
                .all(|property| {
                    property.name().is_some_and(|name| {
                        name.kind() != Kind::ComputedPropertyName
                            && !name.text().starts_with("~effect/")
                    })
                }),
            _ => false,
        }
    }
}

fn type_at_location_candidate(node: P<Node>) -> bool {
    if let Some(parent) = node.parent() {
        if ast::is_jsx_tag_name(node)
            || (parent.kind() == Kind::JsxAttribute && parent.name() == Some(node))
        {
            return false;
        }
        if (node.kind() == Kind::TemplateExpression
            && parent.kind() == Kind::TaggedTemplateExpression)
            || (node.kind() == Kind::MetaProperty
                && parent.kind() == Kind::CallExpression
                && parent.expression() == Some(node))
        {
            return false;
        }
    }
    if (!ast::is_expression(node) && !ast::is_type_node(node) && !ast::is_declaration(node))
        || node.kind() == Kind::ImportClause
    {
        return false;
    }
    let mut current = node;
    if matches!(
        node.kind(),
        Kind::Identifier | Kind::PropertyAccessExpression | Kind::ExpressionWithTypeArguments
    ) {
        loop {
            if current.kind() == Kind::ExpressionWithTypeArguments {
                if let Some(heritage) = current
                    .parent()
                    .filter(|p| p.kind() == Kind::HeritageClause)
                    && let Some(container) = heritage.parent()
                {
                    return !(container.kind() == Kind::InterfaceDeclaration
                        || (ast::is_class_like(container)
                            && heritage.as_heritage_clause().token() == Kind::ImplementsKeyword));
                }
                break;
            }
            let Some(parent) = current.parent() else {
                break;
            };
            if !matches!(
                parent.kind(),
                Kind::PropertyAccessExpression | Kind::ExpressionWithTypeArguments
            ) {
                break;
            }
            current = parent;
        }
    }
    true
}
