//! Public API stability, over the checker's represented type graph.
//!
//! A named child is deliberately a shallow boundary: it contributes its name,
//! arguments and callable surface, while an export and its inherited bases
//! contribute public members. Explicit tags bound child interiors. Keeping
//! these distinct is essential; transitively expanding every named property
//! reports implementation details that are not exposed by the export.
use std::collections::{HashMap, HashSet, VecDeque};

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node, SourceFile, Symbol, SymbolFlags};
use tsrs_checker::{
    self as checker, ObjectFlags, Signature, SignatureFlags, SignatureKind, Type, TypeFlags,
};
use tsrs_core::P;

use super::RuleContext;
use super::stability_common::{
    self as common, declaration_tag, declared_signature, declared_symbol, is_internal,
};
use crate::Rule;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Inspection {
    Expand,
    Shallow,
    InheritExpand,
    InheritShallow,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Work {
    Symbol(P<Symbol>),
    Type(P<Type>, Inspection),
    Signature(P<Signature>, Option<P<Symbol>>),
    Provenance(P<Node>, P<Type>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Offender {
    symbol: Option<P<Symbol>>,
    signature: Option<P<Signature>>,
    declaration: Option<P<Node>>,
    level: u8,
}

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if !ctx.enabled(Rule::ApiStabilityLeak) {
        return;
    }
    let Some(module) = ctx
        .checker
        .get_symbol_of_declaration_exported(ctx.file.as_node())
    else {
        return;
    };
    let exports = sorted_exports(ctx, module);
    let mut visibility = Visibility::default();
    for export in exports {
        if visibility.internal(ctx, module, export) {
            continue;
        }
        let mut ceiling = declared_symbol(ctx, export).level;
        if let Some(forwarding) = forwarding_stability(ctx, export) {
            ceiling = forwarding;
        }
        if ceiling >= 2 {
            continue;
        }
        let Some(target) = common::resolve_alias(ctx, export) else {
            continue;
        };
        let Some(location) = export_location(ctx, export) else {
            continue;
        };
        let mut analysis = Analysis::new(ctx, &mut visibility);
        analysis.enqueue(Work::Symbol(target));
        analysis.finish();
        let mut findings: Vec<_> = analysis
            .findings
            .into_iter()
            .filter(|finding| finding.level > ceiling)
            .collect();
        findings.sort_by_key(|finding| {
            (
                dependency_name(*finding),
                finding.declaration.map(|n| n.pos()),
            )
        });
        let name = export_display_name(ctx, export);
        for finding in findings {
            if finding.signature.is_none()
                && finding.symbol.is_some_and(|symbol| {
                    ctx.same_symbol(symbol, export) || ctx.same_symbol(symbol, target)
                })
            {
                continue;
            }
            let dependency = dependency_name(finding);
            let level = if finding.level == 2 {
                "experimental"
            } else {
                "unstable"
            }
            .to_owned();
            let index = ctx.emit(
                Rule::ApiStabilityLeak,
                location,
                377137,
                &[name.clone(), dependency.clone(), level.clone()],
            );
            if let Some(declaration) = finding.declaration
                && let Some(file) = ast::get_source_file_of_node(declaration)
            {
                let related = ctx.related(file, declaration, 377138, &[dependency, level]);
                ctx.diagnostics[index].related.push(related);
            }
        }
    }
}

/// Accumulating findings outside the graph nodes makes a cycle a simple work
/// list back edge. No partially computed per-node result is reused: each
/// represented (type, context) is expanded exactly once for this export, and
/// all its outgoing edges remain queued. Thus recursive SCCs reach the same
/// union of findings without publishing an incomplete memo to another export.
struct Analysis<'a, 'b> {
    ctx: &'a mut RuleContext<'b>,
    visibility: &'a mut Visibility,
    queue: VecDeque<Work>,
    visited: HashSet<Work>,
    findings: HashSet<Offender>,
    modules: HashSet<P<Symbol>>,
    optional_bases: HashMap<P<Symbol>, bool>,
    safety: HashMap<P<Node>, bool>,
}

impl<'a, 'b> Analysis<'a, 'b> {
    fn new(ctx: &'a mut RuleContext<'b>, visibility: &'a mut Visibility) -> Self {
        Self {
            ctx,
            visibility,
            queue: VecDeque::new(),
            visited: HashSet::new(),
            findings: HashSet::new(),
            modules: HashSet::new(),
            optional_bases: HashMap::new(),
            safety: HashMap::new(),
        }
    }

    fn enqueue(&mut self, work: Work) {
        if self.visited.insert(work) {
            self.queue.push_back(work);
        }
    }

    fn ty(&mut self, ty: Option<P<Type>>, inspection: Inspection) {
        if let Some(ty) = ty {
            self.enqueue(Work::Type(ty, inspection));
        }
    }

    fn provenance(&mut self, node: Option<P<Node>>, ty: P<Type>) {
        if let Some(node) = node {
            self.enqueue(Work::Provenance(node, ty));
        }
    }

    fn finish(&mut self) {
        // The budget is per export. It only guards expanding generic callable
        // recursion whose concrete argument identities grow without a cycle.
        // Ordinary recursive declarations terminate by identity, not depth.
        for _ in 0..100_000 {
            let Some(work) = self.queue.pop_front() else {
                break;
            };
            match work {
                Work::Symbol(symbol) => self.symbol_surface(symbol),
                Work::Type(ty, inspection) => self.type_surface(ty, inspection),
                Work::Signature(signature, owner) => self.signature_surface(signature, owner),
                Work::Provenance(node, ty) => self.type_provenance(node, ty),
            }
        }
    }

    fn inspectable(&self, symbol: P<Symbol>) -> bool {
        symbol.declarations().iter().any(|declaration| {
            ast::get_source_file_of_node(*declaration)
                .is_none_or(|file| !self.ctx.program.is_source_file_default_library(file.path()))
        })
    }

    fn record_symbol(&mut self, symbol: P<Symbol>) {
        if !self.inspectable(symbol) {
            return;
        }
        let declared = declared_symbol(self.ctx, symbol);
        if declared.level != 0 {
            self.findings.insert(Offender {
                symbol: Some(symbol),
                signature: None,
                declaration: declared.declaration,
                level: declared.level,
            });
        }
    }

    fn record_signature(&mut self, mut signature: P<Signature>) {
        let mut seen = HashSet::new();
        while seen.insert(signature) {
            if let Some(target) = signature.target() {
                signature = target;
            } else {
                break;
            }
        }
        let declared = declared_signature(self.ctx, signature);
        if declared.level != 0 {
            self.findings.insert(Offender {
                symbol: None,
                signature: Some(signature),
                declaration: declared.declaration,
                level: declared.level,
            });
        }
    }

    fn record_declaration(&mut self, declaration: P<Node>) {
        if let Some(level) = declaration_tag(declaration)
            && level != 0
        {
            self.findings.insert(Offender {
                symbol: None,
                signature: None,
                declaration: Some(declaration),
                level,
            });
        }
    }

    fn symbol_surface(&mut self, symbol: P<Symbol>) {
        if symbol.flags().intersects(SymbolFlags::Module) {
            if !self.modules.insert(symbol) {
                return;
            }
            for member in sorted_exports(self.ctx, symbol) {
                if self.visibility.internal(self.ctx, symbol, member) {
                    continue;
                }
                self.record_symbol(member);
                if let Some(target) = common::resolve_alias(self.ctx, member) {
                    self.enqueue(Work::Symbol(target));
                }
            }
            return;
        }
        let flags = symbol.flags();
        if flags.intersects(
            SymbolFlags::TypeAlias
                | SymbolFlags::Interface
                | SymbolFlags::Class
                | SymbolFlags::Enum,
        ) {
            if self.symbol_resolution_safe(symbol) {
                let ty = self.ctx.checker.get_declared_type_of_symbol(symbol);
                self.ty(Some(ty), Inspection::Expand);
                self.symbol_provenance(symbol, ty);
            } else {
                self.declared_tags(symbol);
            }
        }
        if flags.intersects(SymbolFlags::Value) && !flags.intersects(SymbolFlags::EnumMember) {
            if self.symbol_resolution_safe(symbol) {
                let ty = self.ctx.checker.get_type_of_symbol(symbol);
                self.ty(Some(ty), Inspection::Expand);
                self.symbol_provenance(symbol, ty);
            } else {
                self.declared_tags(symbol);
            }
        }
        for declaration in symbol.declarations() {
            if declaration.kind() == Kind::ExportAssignment {
                let expression = declaration.as_export_assignment().expression.get();
                let ty = self.ctx.ty(expression);
                self.ty(Some(ty), Inspection::Expand);
            }
        }
    }

    fn symbol_provenance(&mut self, symbol: P<Symbol>, ty: P<Type>) {
        for &declaration in symbol.declarations() {
            if declaration.function_like_data().is_none()
                || matches!(declaration.kind(), Kind::GetAccessor | Kind::SetAccessor)
            {
                self.declaration_provenance(declaration, ty);
            }
        }
    }

    fn declaration_provenance(&mut self, declaration: P<Node>, ty: P<Type>) {
        if is_internal(declaration) {
            return;
        }
        if declaration.kind() == Kind::SetAccessor {
            for parameter in declaration.parameters() {
                self.provenance(parameter.type_node(), ty);
            }
        } else {
            self.provenance(declaration.type_node(), ty);
        }
    }

    fn child_boundary(&mut self, ty: P<Type>) -> Option<P<Symbol>> {
        if let Some(symbol) = ty.alias().and_then(|alias| alias.symbol())
            && declared_symbol(self.ctx, symbol).declaration.is_some()
        {
            return Some(symbol);
        }
        let symbol = ty.symbol().or_else(|| {
            ty.try_as_object_type()
                .and_then(|object| object.target.get())
                .and_then(|target| target.symbol())
        })?;
        declared_symbol(self.ctx, symbol)
            .declaration
            .is_some()
            .then_some(symbol)
    }

    fn arguments(&mut self, ty: P<Type>) -> Vec<P<Type>> {
        let mut arguments = Vec::new();
        if accepts_arguments(ty)
            && let Some(alias) = ty.alias()
        {
            arguments.extend_from_slice(alias.type_arguments());
        }
        if ty.object_flags().intersects(ObjectFlags::Reference) {
            arguments.extend_from_slice(self.ctx.checker.get_type_arguments(ty));
        }
        arguments
    }

    fn type_surface(&mut self, ty: P<Type>, mut inspection: Inspection) {
        if matches!(
            inspection,
            Inspection::InheritExpand | Inspection::InheritShallow
        ) {
            if ty.flags().intersects(TypeFlags::Intersection) && self.child_boundary(ty).is_none() {
                for argument in self.arguments(ty) {
                    self.ty(Some(argument), Inspection::Shallow);
                }
                for &part in ty.types() {
                    self.ty(Some(part), inspection);
                }
                return;
            }
            let target = ty
                .try_as_object_type()
                .and_then(|object| object.target.get())
                .unwrap_or(ty);
            if let Some(symbol) = target.symbol()
                && self.optional_tagged_base(symbol)
            {
                return;
            }
            if let Some(boundary) = self.child_boundary(ty) {
                self.record_symbol(boundary);
                for argument in self.arguments(ty) {
                    self.ty(Some(argument), Inspection::Shallow);
                }
                return;
            }
            inspection = if inspection == Inspection::InheritExpand {
                Inspection::Expand
            } else {
                Inspection::Shallow
            };
        }
        if inspection == Inspection::Shallow
            && let Some(boundary) = self.child_boundary(ty)
        {
            self.record_symbol(boundary);
            for argument in self.arguments(ty) {
                self.ty(Some(argument), Inspection::Shallow);
            }
            return;
        }
        if let Some(alias) = ty.alias() {
            if let Some(symbol) = alias.symbol() {
                self.record_symbol(symbol);
            }
            if accepts_arguments(ty) {
                for &argument in alias.type_arguments() {
                    self.ty(Some(argument), Inspection::Shallow);
                }
            }
        }
        let flags = ty.flags();
        if flags.intersects(TypeFlags::TypeParameter) {
            if let Some(symbol) = ty.symbol() {
                self.record_symbol(symbol);
            }
            self.type_parameter(ty);
        } else if flags.intersects(TypeFlags::UnionOrIntersection) {
            for &part in ty.types() {
                self.ty(Some(part), Inspection::Shallow);
            }
        } else if flags.intersects(TypeFlags::Conditional) {
            self.conditional(ty);
        } else if flags.intersects(TypeFlags::IndexedAccess) {
            let indexed = ty.as_indexed_access_type();
            self.ty(indexed.object_type(), Inspection::Shallow);
            self.ty(indexed.index_type(), Inspection::Shallow);
        } else if flags.intersects(TypeFlags::Index) {
            self.ty(ty.as_index_type().target(), Inspection::Shallow);
        } else if flags.intersects(TypeFlags::TemplateLiteral) {
            for &part in ty.as_template_literal_type().types() {
                self.ty(Some(part), Inspection::Shallow);
            }
        } else if flags.intersects(TypeFlags::StringMapping) {
            if let Some(symbol) = ty.symbol() {
                self.record_symbol(symbol);
            }
            self.ty(ty.as_string_mapping_type().target(), Inspection::Shallow);
        } else if flags.intersects(TypeFlags::Substitution) {
            self.ty(ty.as_substitution_type().base_type(), Inspection::Shallow);
            self.ty(
                ty.as_substitution_type().subst_constraint(),
                Inspection::Shallow,
            );
        } else if flags.intersects(TypeFlags::Object) {
            self.object_surface(ty, inspection);
        } else if flags.intersects(TypeFlags::UniqueESSymbol | TypeFlags::Enum)
            && let Some(symbol) = ty.symbol()
        {
            self.record_symbol(symbol);
        }
    }

    fn type_parameter(&mut self, ty: P<Type>) {
        // This-type constraints refer back to the containing class. They are
        // represented recursive edges and are harmless in this work list.
        let parameter = ty.as_type_parameter();
        let declarations = ty.symbol().map(|s| s.declarations()).unwrap_or(&[]);
        let declaration = declarations
            .iter()
            .copied()
            .find(|node| node.kind() == Kind::TypeParameter);
        let constraint_node =
            declaration.and_then(|node| node.as_type_parameter_declaration().constraint);
        let default_node =
            declaration.and_then(|node| node.as_type_parameter_declaration().default_type);
        let constraint = parameter.constraint.get().or_else(|| {
            if constraint_node.is_none_or(|n| self.annotation_safe(n)) {
                self.ctx.checker.get_constraint_of_type_parameter(ty)
            } else {
                None
            }
        });
        let default = parameter.resolved_default_type.get().or_else(|| {
            if default_node.is_some_and(|n| self.annotation_safe(n)) {
                self.ctx
                    .checker
                    .get_default_from_type_parameter_exported(ty)
            } else {
                None
            }
        });
        if let Some(constraint) = constraint {
            self.ty(Some(constraint), Inspection::Shallow);
            self.provenance(constraint_node, constraint);
        }
        if let Some(default) = default {
            self.ty(Some(default), Inspection::Shallow);
            self.provenance(default_node, default);
        }
    }

    fn conditional(&mut self, ty: P<Type>) {
        let conditional = ty.as_conditional_type();
        // A concrete deferred conditional is a checker relation outcome. Its
        // unselected branches must never be inferred by the rule.
        if ty.mapper().is_some() {
            return;
        }
        let operands = [conditional.check_type(), conditional.extends_type()];
        if !operands.into_iter().flatten().any(contains_parameter) {
            return;
        }
        for operand in operands {
            self.ty(operand, Inspection::Shallow);
        }
        if let Some(root) = conditional.root.get()
            && let Some(node) = root.node.get()
        {
            let node = node.as_conditional_type_node();
            for (node, cached) in [
                (node.true_type, conditional.resolved_true_type.get()),
                (node.false_type, conditional.resolved_false_type.get()),
            ] {
                let represented = cached.or_else(|| self.annotation_type(node));
                if let Some(represented) = represented {
                    self.ty(Some(represented), Inspection::Shallow);
                    self.provenance(Some(node), represented);
                }
            }
        }
    }

    fn object_surface(&mut self, ty: P<Type>, inspection: Inspection) {
        let flags = ty.object_flags();
        if flags.intersects(ObjectFlags::ReverseMapped | ObjectFlags::EvolvingArray) {
            return;
        }
        let target = ty
            .try_as_object_type()
            .and_then(|object| object.target.get())
            .unwrap_or(ty);
        let owner = ty.symbol().or_else(|| target.symbol());
        if let Some(owner) = owner {
            self.record_symbol(owner);
            if owner.flags().intersects(SymbolFlags::Module) {
                return;
            }
        }
        for argument in self.arguments(ty) {
            self.ty(Some(argument), Inspection::Shallow);
        }
        let named = target
            .object_flags()
            .intersects(ObjectFlags::ClassOrInterface);
        if named && owner.is_some_and(|owner| !self.inspectable(owner)) {
            return;
        }
        if flags.intersects(ObjectFlags::Mapped) {
            // Mapped operands are part of the surface independently from a
            // materialized property table; inspect actual checker components.
            let mapped = ty.as_mapped_type();
            let declaration = mapped.declaration.get();
            if declaration.is_none_or(|node| self.annotation_safe(node)) {
                checker::MappedType::resolve_components(self.ctx.checker, ty);
            }
            for part in [
                mapped.constraint_type(),
                mapped.name_type(),
                mapped.template_type(),
            ] {
                self.ty(part, Inspection::Shallow);
            }
            if let Some(node) = declaration {
                self.provenance(Some(node), ty);
            }
            return;
        }
        let class_static = flags.intersects(ObjectFlags::Anonymous)
            && owner.is_some_and(|s| s.flags().intersects(SymbolFlags::Class));
        if class_static
            && inspection == Inspection::Expand
            && let Some(owner) = owner
        {
            let instance = self.ctx.checker.get_declared_type_of_symbol(owner);
            self.ty(Some(instance), Inspection::Expand);
        }
        if named && inspection == Inspection::Expand && ty == target {
            for &parameter in target.as_interface_type().local_type_parameters() {
                self.ty(Some(parameter), Inspection::Shallow);
            }
        }
        if inspection == Inspection::Expand || (!named && !class_static) {
            let members = self.ctx.checker.get_properties_of_type(ty).to_vec();
            for member in members {
                if class_static && member.name() == "prototype" {
                    continue;
                }
                self.member_surface(member, owner);
            }
            let indexes = self.ctx.checker.get_index_infos_of_type(ty).to_vec();
            for info in indexes {
                if let Some(declaration) = info.declaration.get() {
                    if is_internal(declaration) {
                        continue;
                    }
                    if declaration_tag(declaration).is_some() {
                        self.record_declaration(declaration);
                        continue;
                    }
                    if self.inherited_boundary(declaration, owner) {
                        continue;
                    }
                    if let Some(value) = info.value_type.get() {
                        self.provenance(declaration.type_node(), value);
                    }
                }
                self.ty(info.key_type.get(), Inspection::Shallow);
                self.ty(info.value_type.get(), Inspection::Shallow);
            }
        }
        for kind in [SignatureKind::Call, SignatureKind::Construct] {
            for signature in self.ctx.checker.get_signatures_of_type(ty, kind).to_vec() {
                self.enqueue(Work::Signature(signature, owner));
            }
        }
        if named {
            let bases = self.ctx.checker.get_base_types_of_reference_exported(ty);
            let mode = if inspection == Inspection::Expand {
                Inspection::InheritExpand
            } else {
                Inspection::InheritShallow
            };
            // The checker instantiates the heritage with this reference's
            // actual arguments, so bound constraints/defaults do not leak.
            for base in bases {
                self.ty(Some(base), mode);
            }
        }
    }

    fn member_surface(&mut self, member: P<Symbol>, owner: Option<P<Symbol>>) {
        if non_public(member) || member.flags().intersects(SymbolFlags::TypeParameter) {
            return;
        }
        if member.name().starts_with(ast::INTERNAL_SYMBOL_NAME_PREFIX)
            && !checker::is_known_symbol(member)
        {
            return;
        }
        if let Some(declaring) = declaring_symbol(self.ctx, member.declarations().first().copied())
            && Some(declaring) != owner
            && owner.is_some()
        {
            if self.optional_tagged_base(declaring) {
                return;
            }
            if declared_symbol(self.ctx, declaring).declaration.is_some() {
                self.record_symbol(declaring);
                return;
            }
        }
        self.record_symbol(member);
        if declared_symbol(self.ctx, member).declaration.is_some() {
            return;
        }
        if !self.symbol_resolution_safe(member) {
            self.declared_tags(member);
            return;
        }
        let ty = self.ctx.checker.get_type_of_symbol(member);
        self.ty(Some(ty), Inspection::Shallow);
        self.symbol_provenance(member, ty);
    }

    fn inherited_boundary(&mut self, declaration: P<Node>, owner: Option<P<Symbol>>) -> bool {
        if let Some(declaring) = declaring_symbol(self.ctx, Some(declaration))
            && Some(declaring) != owner
            && declared_symbol(self.ctx, declaring).declaration.is_some()
        {
            self.record_symbol(declaring);
            return true;
        }
        false
    }

    fn signature_surface(&mut self, signature: P<Signature>, owner: Option<P<Symbol>>) {
        let mut raw = signature;
        let mut visited = HashSet::new();
        while visited.insert(raw) {
            if let Some(target) = raw.target() {
                raw = target;
            } else {
                break;
            }
        }
        if let Some(declaration) = raw.declaration() {
            if non_public_declaration(declaration) || is_internal(declaration) {
                return;
            }
            let belongs = owner.is_some_and(|owner| owner.declarations().contains(&declaration));
            if declared_signature(self.ctx, raw).declaration.is_some() && !belongs {
                self.record_signature(raw);
                return;
            }
            if !belongs && self.inherited_boundary(declaration, owner) {
                return;
            }
        }
        let own_declaration = owner.and_then(|owner| declared_symbol(self.ctx, owner).declaration);
        if own_declaration.is_none()
            || declared_signature(self.ctx, raw).declaration != own_declaration
        {
            self.record_signature(raw);
        }
        if signature != raw {
            for argument in self
                .ctx
                .checker
                .get_type_arguments_for_resolved_signature(signature)
            {
                self.ty(Some(argument), Inspection::Shallow);
            }
        }
        for &parameter in signature.type_parameters() {
            self.ty(Some(parameter), Inspection::Shallow);
        }
        for parameter in signature
            .this_parameter()
            .into_iter()
            .chain(signature.parameters().iter().copied())
        {
            if !self.symbol_resolution_safe(parameter) {
                continue;
            }
            let ty = self.ctx.checker.get_type_of_symbol(parameter);
            self.ty(Some(ty), Inspection::Shallow);
            for &declaration in parameter.declarations() {
                self.provenance(declaration.type_node(), ty);
            }
        }
        let annotation = raw.declaration().and_then(|node| node.type_node());
        if signature.resolved_return_type.get().is_some()
            || match annotation {
                Some(node) => self.annotation_safe(node),
                None => raw
                    .declaration()
                    .is_some_and(|node| self.inference_safe(node)),
            }
        {
            let result = self.ctx.checker.get_return_type_of_signature(signature);
            self.ty(Some(result), Inspection::Shallow);
            self.provenance(annotation, result);
        }
    }

    fn optional_tagged_base(&mut self, symbol: P<Symbol>) -> bool {
        if let Some(&result) = self.optional_bases.get(&symbol) {
            return result;
        }
        let mut queue = vec![symbol];
        let mut seen = HashSet::new();
        let mut result = true;
        while let Some(current) = queue.pop() {
            if !seen.insert(current) {
                continue;
            }
            if !current
                .flags()
                .intersects(SymbolFlags::Class | SymbolFlags::Interface)
                || current.declarations().is_empty()
            {
                result = false;
                break;
            }
            for &declaration in current.declarations() {
                if !matches!(
                    declaration.kind(),
                    Kind::ClassDeclaration | Kind::ClassExpression | Kind::InterfaceDeclaration
                ) {
                    result = false;
                    break;
                }
                for &member in declaration.members() {
                    if let Some(symbol) =
                        self.ctx.checker.get_symbol_of_declaration_exported(member)
                        && only_internal(symbol)
                    {
                        continue;
                    }
                    if !matches!(
                        member.kind(),
                        Kind::PropertySignature
                            | Kind::PropertyDeclaration
                            | Kind::MethodSignature
                            | Kind::MethodDeclaration
                    ) || !ast::has_question_token(member)
                        || declaration_tag(member).is_none()
                    {
                        result = false;
                        break;
                    }
                }
                if !result {
                    break;
                }
                for &base in ast::get_extends_heritage_clause_elements(declaration) {
                    let name = match base.kind() {
                        Kind::TypeReference => base.as_type_reference_node().type_name,
                        Kind::ExpressionWithTypeArguments => {
                            base.as_expression_with_type_arguments().expression
                        }
                        _ => {
                            result = false;
                            break;
                        }
                    };
                    if let Some(base) = self
                        .ctx
                        .symbol(name)
                        .and_then(|s| common::resolve_alias(self.ctx, s))
                    {
                        queue.push(base);
                    } else {
                        result = false;
                        break;
                    }
                }
            }
            if !result {
                break;
            }
        }
        self.optional_bases.insert(symbol, result);
        result
    }

    fn annotation_type(&mut self, node: P<Node>) -> Option<P<Type>> {
        self.annotation_safe(node)
            .then(|| self.ctx.checker.get_type_from_type_node(node))
    }

    fn symbol_resolution_safe(&mut self, symbol: P<Symbol>) -> bool {
        if self
            .ctx
            .checker
            .value_symbol_links
            .try_get_if_id_assigned(symbol)
            .is_some_and(|links| links.resolved_type.get().is_some())
        {
            return true;
        }
        symbol.declarations().iter().all(|declaration| {
            if declaration.type_node().is_none()
                && (declaration.function_like_data().is_none()
                    || matches!(declaration.kind(), Kind::GetAccessor | Kind::SetAccessor))
                && !matches!(
                    declaration.kind(),
                    Kind::ClassDeclaration
                        | Kind::ClassExpression
                        | Kind::InterfaceDeclaration
                        | Kind::EnumDeclaration
                )
            {
                return self.inference_safe(*declaration);
            }
            declaration.type_node().is_none_or(|node| {
                // Reading a generic alias's own deferred conditional creates
                // the conditional shell, without evaluating either branch.
                // Applications are still gated separately: concrete arguments
                // can make the same declaration eagerly recursive.
                (declaration.kind() == Kind::TypeAliasDeclaration
                    && self.raw_deferred_conditional(node))
                    || self.annotation_safe(node)
            })
        })
    }

    // Oxlint requests rules outside the compiler's source-check lifecycle.
    // Like TSGO, inspect cached or annotated types there without starting
    // speculative inference of an initializer, parameter default, or body.
    fn inference_safe(&self, declaration: P<Node>) -> bool {
        ast::get_source_file_of_node(declaration).is_some_and(|file| {
            self.ctx
                .checker
                .source_file_links
                .try_get(file)
                .is_some_and(|links| links.type_checked.get())
        })
    }

    fn raw_deferred_conditional(&mut self, node: P<Node>) -> bool {
        if node.kind() != Kind::ConditionalType {
            return false;
        }
        let conditional = node.as_conditional_type_node();
        [conditional.check_type, conditional.extends_type]
            .into_iter()
            .any(|node| {
                node.kind() == Kind::TypeReference
                    && self
                        .ctx
                        .symbol(node.as_type_reference_node().type_name)
                        .is_some_and(|symbol| symbol.flags().intersects(SymbolFlags::TypeParameter))
            })
    }

    /// A preflight over declaration identity prevents lazy checker reads from
    /// evaluating recursive *expanding* aliases. Recursive objects are lazy and
    /// safe; conditional/projection applications can eagerly instantiate an
    /// unbounded graph. This examines syntax metadata, never invents a type.
    fn annotation_safe(&mut self, node: P<Node>) -> bool {
        if let Some(&safe) = self.safety.get(&node) {
            return safe;
        }
        let safe = annotation_safe(self.ctx, node, &mut HashSet::new(), false, &mut 0);
        self.safety.insert(node, safe);
        safe
    }

    fn declared_tags(&mut self, symbol: P<Symbol>) {
        // Declaration metadata remains meaningful when a checker read cannot
        // safely materialize a component. Only direct exposed tags are kept.
        for &declaration in symbol.declarations() {
            if let Some(node) = declaration.type_node()
                && matches!(
                    node.kind(),
                    Kind::TypeReference | Kind::ExpressionWithTypeArguments
                )
            {
                let name = if node.kind() == Kind::TypeReference {
                    node.as_type_reference_node().type_name
                } else {
                    node.as_expression_with_type_arguments().expression
                };
                if let Some(symbol) = self.ctx.symbol(name) {
                    self.record_symbol(symbol);
                }
            }
        }
    }

    fn type_provenance(&mut self, node: P<Node>, represented: P<Type>) {
        match node.kind() {
            Kind::ParenthesizedType
            | Kind::TypeOperator
            | Kind::NamedTupleMember
            | Kind::OptionalType
            | Kind::RestType => self.provenance(node.type_node(), represented),
            Kind::TypeReference | Kind::ExpressionWithTypeArguments | Kind::ImportType => {
                let name = match node.kind() {
                    Kind::TypeReference => Some(node.as_type_reference_node().type_name),
                    Kind::ExpressionWithTypeArguments => {
                        Some(node.as_expression_with_type_arguments().expression)
                    }
                    _ => node.as_import_type_node().qualifier,
                };
                if let Some(name) = name
                    && let Some(symbol) = self.ctx.symbol(name)
                {
                    self.record_symbol(symbol);
                }
                if accepts_arguments(represented) {
                    let arguments = if represented
                        .object_flags()
                        .intersects(ObjectFlags::Reference)
                    {
                        self.ctx.checker.get_type_arguments(represented).to_vec()
                    } else {
                        represented
                            .alias()
                            .map_or_else(Vec::new, |a| a.type_arguments().to_vec())
                    };
                    for (&node, &ty) in node.type_arguments().iter().zip(arguments.iter()) {
                        self.provenance(Some(node), ty);
                    }
                }
            }
            Kind::TypeQuery => {
                if let Some(symbol) = self.ctx.symbol(node.as_type_query_node().expr_name) {
                    self.record_symbol(symbol);
                }
            }
            Kind::UnionType | Kind::IntersectionType => {
                let nodes = if node.kind() == Kind::UnionType {
                    node.as_union_type_node().types()
                } else {
                    node.as_intersection_type_node().types()
                };
                let parts = if represented
                    .flags()
                    .intersects(TypeFlags::UnionOrIntersection)
                {
                    represented.types().to_vec()
                } else {
                    vec![represented]
                };
                for &node in nodes.nodes() {
                    if let Some(actual) = self.annotation_type(node)
                        && (parts.contains(&actual)
                            || (actual.flags().intersects(TypeFlags::UnionOrIntersection)
                                && actual.types().iter().all(|part| parts.contains(part))))
                    {
                        self.provenance(Some(node), actual);
                    }
                }
            }
            Kind::ArrayType => {
                if represented
                    .object_flags()
                    .intersects(ObjectFlags::Reference)
                    && let Some(&element) = self.ctx.checker.get_type_arguments(represented).first()
                {
                    self.provenance(Some(node.as_array_type_node().element_type), element);
                }
            }
            Kind::TupleType => {
                if represented
                    .object_flags()
                    .intersects(ObjectFlags::Reference)
                {
                    let arguments = self.ctx.checker.get_type_arguments(represented).to_vec();
                    for (&node, &ty) in node
                        .as_tuple_type_node()
                        .elements
                        .nodes()
                        .iter()
                        .zip(arguments.iter())
                    {
                        self.provenance(Some(node), ty);
                    }
                }
            }
            Kind::IndexedAccessType => {
                if represented.flags().intersects(TypeFlags::IndexedAccess) {
                    let indexed = represented.as_indexed_access_type();
                    if let Some(ty) = indexed.object_type() {
                        self.provenance(Some(node.as_indexed_access_type_node().object_type), ty);
                    }
                    if let Some(ty) = indexed.index_type() {
                        self.provenance(Some(node.as_indexed_access_type_node().index_type), ty);
                    }
                }
            }
            Kind::ConditionalType => {
                if represented.flags().intersects(TypeFlags::Conditional) {
                    let conditional = represented.as_conditional_type();
                    if let Some(ty) = conditional.check_type() {
                        self.provenance(Some(node.as_conditional_type_node().check_type), ty);
                    }
                    if let Some(ty) = conditional.extends_type() {
                        self.provenance(Some(node.as_conditional_type_node().extends_type), ty);
                    }
                }
            }
            Kind::FunctionType | Kind::ConstructorType => {
                let kind = if node.kind() == Kind::ConstructorType {
                    SignatureKind::Construct
                } else {
                    SignatureKind::Call
                };
                for signature in self
                    .ctx
                    .checker
                    .get_signatures_of_type(represented, kind)
                    .to_vec()
                {
                    self.enqueue(Work::Signature(signature, represented.symbol()));
                }
            }
            Kind::TypeLiteral => {
                let members = self
                    .ctx
                    .checker
                    .get_properties_of_type(represented)
                    .to_vec();
                for &declaration in node.members() {
                    if is_internal(declaration) || non_public_declaration(declaration) {
                        continue;
                    }
                    if declaration.function_like_data().is_some() {
                        continue;
                    }
                    let member = self
                        .ctx
                        .checker
                        .get_symbol_of_declaration_exported(declaration);
                    let represented_member = member.and_then(|member| {
                        members
                            .iter()
                            .find(|candidate| candidate.name() == member.name())
                            .copied()
                    });
                    if let Some(member) = represented_member
                        && !non_public(member)
                        && self.symbol_resolution_safe(member)
                    {
                        let ty = self.ctx.checker.get_type_of_symbol(member);
                        self.declaration_provenance(declaration, ty);
                    }
                }
            }
            Kind::MappedType if represented.object_flags().intersects(ObjectFlags::Mapped) => {
                let mapped = represented.as_mapped_type();
                let node = node.as_mapped_type_node();
                if let Some(ty) = mapped.constraint_type() {
                    self.provenance(
                        node.type_parameter
                            .as_type_parameter_declaration()
                            .constraint,
                        ty,
                    );
                }
                if let Some(ty) = mapped.name_type() {
                    self.provenance(node.name_type, ty);
                }
                if let Some(ty) = mapped.template_type() {
                    self.provenance(node.type_, ty);
                }
            }
            _ => {}
        }
    }
}

fn accepts_arguments(ty: P<Type>) -> bool {
    ty.flags().intersects(
        TypeFlags::Object
            | TypeFlags::UnionOrIntersection
            | TypeFlags::Conditional
            | TypeFlags::IndexedAccess
            | TypeFlags::Index
            | TypeFlags::Substitution
            | TypeFlags::TemplateLiteral
            | TypeFlags::StringMapping,
    )
}

fn contains_parameter(ty: P<Type>) -> bool {
    let mut queue = vec![ty];
    let mut visited = HashSet::new();
    while let Some(ty) = queue.pop() {
        if !visited.insert(ty) {
            continue;
        }
        if ty.flags().intersects(TypeFlags::TypeParameter) {
            return true;
        }
        if ty.flags().intersects(TypeFlags::UnionOrIntersection) {
            queue.extend_from_slice(ty.types());
        }
        if let Some(alias) = ty.alias() {
            queue.extend_from_slice(alias.type_arguments());
        }
        if ty.object_flags().intersects(ObjectFlags::Reference) {
            queue.extend_from_slice(
                ty.as_type_reference()
                    .resolved_type_arguments
                    .get()
                    .unwrap_or(&[]),
            );
        }
        if ty.flags().intersects(TypeFlags::IndexedAccess) {
            queue.extend(ty.as_indexed_access_type().object_type());
            queue.extend(ty.as_indexed_access_type().index_type());
        }
        if ty.flags().intersects(TypeFlags::Index) {
            queue.extend(ty.as_index_type().target());
        }
    }
    false
}

fn annotation_safe(
    ctx: &mut RuleContext<'_>,
    node: P<Node>,
    active: &mut HashSet<P<Symbol>>,
    projection: bool,
    work: &mut usize,
) -> bool {
    *work += 1;
    if *work > 4000 {
        return false;
    }
    // Object/function type bodies are lazy: their child annotations are gated
    // individually when the represented member/signature is actually visited.
    if matches!(
        node.kind(),
        Kind::TypeLiteral | Kind::FunctionType | Kind::ConstructorType
    ) {
        return true;
    }
    let projection = projection
        || matches!(
            node.kind(),
            Kind::ConditionalType | Kind::IndexedAccessType | Kind::MappedType | Kind::TypeOperator
        );
    if node.kind() == Kind::TypeReference {
        let name = node.as_type_reference_node().type_name;
        if let Some(symbol) = ctx.symbol(name).and_then(|s| common::resolve_alias(ctx, s))
            && symbol.flags().intersects(SymbolFlags::TypeAlias)
        {
            if !active.insert(symbol) {
                return !projection;
            }
            let safe = symbol.declarations().iter().all(|declaration| {
                declaration
                    .type_node()
                    .is_none_or(|node| annotation_safe(ctx, node, active, projection, work))
            });
            active.remove(&symbol);
            if !safe {
                return false;
            }
        }
    }
    let mut children = Vec::new();
    node.for_each_child(&mut |child| {
        children.push(child);
        false
    });
    children
        .into_iter()
        .all(|node| annotation_safe(ctx, node, active, projection, work))
}

fn non_public_declaration(node: P<Node>) -> bool {
    node.name()
        .is_some_and(|name| name.kind() == Kind::PrivateIdentifier)
        || ast::get_combined_modifier_flags(node)
            .intersects(ModifierFlags::Private | ModifierFlags::Protected)
}

fn only_internal(symbol: P<Symbol>) -> bool {
    !symbol.declarations().is_empty()
        && symbol
            .declarations()
            .iter()
            .all(|declaration| is_internal(*declaration))
}

fn non_public(symbol: P<Symbol>) -> bool {
    checker::is_private_identifier_symbol(Some(symbol))
        || only_internal(symbol)
        || checker::get_declaration_modifier_flags_from_symbol_exported(symbol)
            .intersects(ModifierFlags::Private | ModifierFlags::Protected)
}

fn declaring_symbol(ctx: &mut RuleContext<'_>, declaration: Option<P<Node>>) -> Option<P<Symbol>> {
    let mut parent = declaration?.parent();
    while let Some(node) = parent {
        if matches!(
            node.kind(),
            Kind::ClassDeclaration | Kind::ClassExpression | Kind::InterfaceDeclaration
        ) {
            return ctx.checker.get_symbol_of_declaration_exported(node);
        }
        if matches!(
            node.kind(),
            Kind::SourceFile | Kind::ModuleDeclaration | Kind::TypeAliasDeclaration
        ) {
            break;
        }
        parent = node.parent();
    }
    None
}

fn dependency_name(finding: Offender) -> String {
    if let Some(symbol) = finding.symbol {
        let name = symbol.name();
        if !name.is_empty()
            && !name.starts_with(ast::INTERNAL_SYMBOL_NAME_PREFIX)
            && !name.starts_with("__@")
        {
            return name.to_owned();
        }
    }
    if let Some(declaration) = finding.declaration {
        if let Some(name) = declaration.name() {
            if matches!(
                name.kind(),
                Kind::Identifier | Kind::StringLiteral | Kind::NumericLiteral
            ) {
                return name.text().to_owned();
            }
            if name.kind() == Kind::ComputedPropertyName {
                let expression = name.as_computed_property_name().expression;
                if expression.kind() == Kind::PropertyAccessExpression {
                    let property = expression.as_property_access_expression();
                    if property.expression.kind() == Kind::Identifier
                        && property.expression.text() == "Symbol"
                    {
                        return format!("[Symbol.{}]", property.name().text());
                    }
                }
                if matches!(
                    expression.kind(),
                    Kind::StringLiteral
                        | Kind::NumericLiteral
                        | Kind::BigIntLiteral
                        | Kind::NoSubstitutionTemplateLiteral
                ) {
                    return expression.text().to_owned();
                }
                if let Some(symbol) = declaration.symbol()
                    && !symbol.name().starts_with(ast::INTERNAL_SYMBOL_NAME_PREFIX)
                {
                    return symbol.name().to_owned();
                }
                if let Some(symbol) = finding.symbol.filter(|s| checker::is_known_symbol(*s)) {
                    let name = symbol
                        .name()
                        .trim_start_matches(ast::INTERNAL_SYMBOL_NAME_PREFIX)
                        .trim_start_matches('@');
                    let name = name.rsplit_once('@').map_or(name, |(name, _)| name);
                    return format!("[{name}]");
                }
                return "[computed]".to_owned();
            }
        }
        match declaration.kind() {
            Kind::CallSignature => return "call signature".to_owned(),
            Kind::ConstructSignature | Kind::Constructor => return "constructor".to_owned(),
            Kind::IndexSignature => return "index signature".to_owned(),
            _ => {}
        }
    }
    if let Some(signature) = finding.signature {
        return if signature.flags().intersects(SignatureFlags::Construct) {
            "constructor"
        } else {
            "call signature"
        }
        .to_owned();
    }
    finding
        .symbol
        .map_or_else(|| "<anonymous>".to_owned(), |s| s.name().to_owned())
}

fn sorted_exports(ctx: &mut RuleContext<'_>, module: P<Symbol>) -> Vec<P<Symbol>> {
    let mut exports = ctx.checker.get_exports_of_module_exported(module);
    exports.sort_by_key(|s| s.name());
    exports
}

fn exported(ctx: &mut RuleContext<'_>, module: P<Symbol>, name: &str) -> Option<P<Symbol>> {
    ctx.checker
        .get_exports_of_module_exported(module)
        .into_iter()
        .find(|symbol| symbol.name() == name)
}

fn module_of(ctx: &mut RuleContext<'_>, node: P<Node>) -> Option<P<Symbol>> {
    let symbol = ctx.symbol(node)?;
    let symbol = common::resolve_alias(ctx, symbol)?;
    symbol
        .flags()
        .intersects(SymbolFlags::Module)
        .then_some(symbol)
}

fn forwards(ctx: &mut RuleContext<'_>, statement: P<Node>, symbol: P<Symbol>) -> bool {
    let declaration = statement.as_export_declaration();
    if let Some(clause) = declaration.export_clause {
        return match clause.kind() {
            Kind::NamespaceExport => clause
                .name()
                .is_some_and(|name| name.text() == symbol.name()),
            Kind::NamedExports => {
                clause
                    .as_named_exports()
                    .elements
                    .nodes()
                    .iter()
                    .any(|element| {
                        element
                            .name()
                            .is_some_and(|name| name.text() == symbol.name())
                    })
            }
            _ => false,
        };
    }
    declaration
        .module_specifier
        .and_then(|node| module_of(ctx, node))
        .and_then(|module| exported(ctx, module, symbol.name()))
        .is_some_and(|forwarded| ctx.same_symbol(forwarded, symbol))
}

fn forwarding_stability(ctx: &mut RuleContext<'_>, symbol: P<Symbol>) -> Option<u8> {
    let mut stability = None;
    for &statement in ctx.file.statements.nodes() {
        if statement.kind() != Kind::ExportDeclaration {
            continue;
        }
        if let Some(level) = declaration_tag(statement)
            && forwards(ctx, statement, symbol)
        {
            stability = Some(stability.unwrap_or(0).max(level));
        }
    }
    stability
}

fn forwarding_statement(node: P<Node>) -> Option<P<Node>> {
    let parent = node.parent()?;
    if parent.kind() == Kind::ExportDeclaration {
        return Some(parent);
    }
    parent
        .parent()
        .filter(|node| node.kind() == Kind::ExportDeclaration)
}

fn export_location(ctx: &mut RuleContext<'_>, symbol: P<Symbol>) -> Option<P<Node>> {
    for &declaration in symbol.declarations() {
        if ast::get_source_file_of_node(declaration) == Some(ctx.file) {
            return Some(declaration.name().unwrap_or(declaration));
        }
    }
    let mut fallback = None;
    for &statement in ctx.file.statements.nodes() {
        if statement.kind() != Kind::ExportDeclaration {
            continue;
        }
        let declaration = statement.as_export_declaration();
        if declaration.export_clause.is_some() || declaration.module_specifier.is_none() {
            continue;
        }
        fallback.get_or_insert(statement);
        if forwards(ctx, statement, symbol) {
            return Some(statement);
        }
    }
    fallback
}

fn export_display_name(ctx: &mut RuleContext<'_>, symbol: P<Symbol>) -> String {
    common::module_name(ctx, ctx.file).map_or_else(
        || symbol.name().to_owned(),
        |module| format!("{module}#{}", symbol.name()),
    )
}

fn module_statements(module: P<Symbol>) -> Vec<P<Node>> {
    let mut statements = Vec::new();
    for &declaration in module.declarations() {
        let mut node = declaration;
        while node.kind() == Kind::ModuleDeclaration {
            let Some(body) = node.as_module_declaration().body() else {
                break;
            };
            node = body;
        }
        if matches!(node.kind(), Kind::SourceFile | Kind::ModuleBlock) {
            statements.extend_from_slice(node.statements());
        }
    }
    statements
}

fn module_files(module: P<Symbol>) -> HashSet<P<SourceFile>> {
    module
        .declarations()
        .iter()
        .filter(|node| matches!(node.kind(), Kind::SourceFile | Kind::ModuleDeclaration))
        .filter_map(|node| ast::get_source_file_of_node(*node))
        .collect()
}

/// Visibility is a property of an export path, rather than of a symbol alone.
/// An explicit module export wins over redundant stars; merged public paths
/// keep a symbol public. Cyclic star paths add no new public declaration.
#[derive(Default)]
struct Visibility {
    active: HashSet<(P<Symbol>, P<Symbol>)>,
    memo: HashMap<(P<Symbol>, P<Symbol>), bool>,
}

impl Visibility {
    fn internal(
        &mut self,
        ctx: &mut RuleContext<'_>,
        module: P<Symbol>,
        symbol: P<Symbol>,
    ) -> bool {
        let key = (module, symbol);
        if let Some(&result) = self.memo.get(&key) {
            return result;
        }
        if !self.active.insert(key) {
            return true;
        }
        let result = self.inspect(ctx, module, symbol);
        self.active.remove(&key);
        // A result reached through an active cycle can depend on its caller.
        // Cache only complete top-level questions, never a provisional edge.
        if self.active.is_empty() {
            self.memo.insert(key, result);
        }
        result
    }

    fn inspect(&mut self, ctx: &mut RuleContext<'_>, module: P<Symbol>, symbol: P<Symbol>) -> bool {
        let files = module_files(module);
        if files.is_empty() {
            return false;
        }
        let mut found = false;
        for &declaration in symbol.declarations() {
            if !ast::get_source_file_of_node(declaration).is_some_and(|file| files.contains(&file))
            {
                continue;
            }
            found = true;
            if !self.path_internal(ctx, module, symbol, declaration) {
                return false;
            }
        }
        if found
            && exported(ctx, module, symbol.name())
                .is_some_and(|export| ctx.same_symbol(export, symbol))
        {
            return true;
        }
        for statement in module_statements(module) {
            if statement.kind() != Kind::ExportDeclaration {
                continue;
            }
            let declaration = statement.as_export_declaration();
            if declaration.export_clause.is_some() || !forwards(ctx, statement, symbol) {
                continue;
            }
            found = true;
            if is_internal(statement) {
                continue;
            }
            let Some(target) = declaration
                .module_specifier
                .and_then(|node| module_of(ctx, node))
            else {
                return false;
            };
            if !self.internal(ctx, target, symbol) {
                return false;
            }
        }
        found
    }

    fn path_internal(
        &mut self,
        ctx: &mut RuleContext<'_>,
        module: P<Symbol>,
        symbol: P<Symbol>,
        declaration: P<Node>,
    ) -> bool {
        if is_internal(declaration) {
            return true;
        }
        let statement = forwarding_statement(declaration);
        if statement.is_some_and(is_internal) {
            return true;
        }
        match declaration.kind() {
            Kind::ExportSpecifier | Kind::ExportAssignment => {
                let target_module = statement
                    .and_then(|s| s.as_export_declaration().module_specifier)
                    .and_then(|n| module_of(ctx, n))
                    .unwrap_or(module);
                self.alias_internal(ctx, target_module, symbol)
            }
            Kind::ImportSpecifier | Kind::ImportClause => {
                let mut parent = declaration.parent();
                while let Some(node) = parent {
                    if node.kind() == Kind::ImportDeclaration {
                        let Some(target) =
                            module_of(ctx, node.as_import_declaration().module_specifier())
                        else {
                            return false;
                        };
                        return self.alias_internal(ctx, target, symbol);
                    }
                    if matches!(node.kind(), Kind::SourceFile | Kind::ModuleBlock) {
                        break;
                    }
                    parent = node.parent();
                }
                false
            }
            Kind::ImportEqualsDeclaration => {
                if !symbol.flags().intersects(SymbolFlags::Alias) {
                    return false;
                }
                let reference = declaration.as_import_equals_declaration().module_reference;
                let mut target = ctx.checker.get_immediate_aliased_symbol(symbol);
                if target.is_none() {
                    target = match reference.kind() {
                        Kind::QualifiedName => {
                            let qualified = reference.as_qualified_name();
                            module_of(ctx, qualified.left)
                                .and_then(|m| exported(ctx, m, qualified.right.text()))
                        }
                        Kind::ExternalModuleReference => {
                            module_of(ctx, reference.as_external_module_reference().expression)
                        }
                        _ => None,
                    };
                }
                let Some(target) = target.filter(|target| *target != symbol) else {
                    return false;
                };
                let mut modules = HashSet::new();
                for &declaration in target.declarations() {
                    let mut node = Some(declaration);
                    while let Some(parent) = node {
                        if matches!(parent.kind(), Kind::SourceFile | Kind::ModuleDeclaration) {
                            if let Some(module) =
                                ctx.checker.get_symbol_of_declaration_exported(parent)
                            {
                                modules.insert(module);
                            }
                            break;
                        }
                        node = parent.parent();
                    }
                }
                !modules.is_empty()
                    && modules
                        .into_iter()
                        .all(|module| self.internal(ctx, module, target))
            }
            _ => false,
        }
    }

    fn alias_internal(
        &mut self,
        ctx: &mut RuleContext<'_>,
        module: P<Symbol>,
        symbol: P<Symbol>,
    ) -> bool {
        if !symbol.flags().intersects(SymbolFlags::Alias) || symbol.declarations().is_empty() {
            return false;
        }
        ctx.checker
            .get_immediate_aliased_symbol(symbol)
            .filter(|target| *target != symbol)
            .is_some_and(|target| self.internal(ctx, module, target))
    }
}
