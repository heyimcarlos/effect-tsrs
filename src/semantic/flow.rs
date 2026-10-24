//! Checker-backed normalization of calls and result-producing function bodies.
use std::collections::{HashMap, HashSet};

use tsrs_ast::{self as ast, Kind, ModifierFlags, Node, NodeFlags, Symbol, SymbolFlags};
use tsrs_checker::{ObjectFlags, Signature, SignatureKind, Type, TypeFlags};
use tsrs_core::P;

use crate::rules::RuleContext;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransformationKind {
    Pipe,
    Pipeable,
    DataFirst,
    DataLast,
    Call,
    EffectFn,
    EffectFnUntraced,
}

#[derive(Clone)]
enum FlowType {
    Node(P<Node>),
    PipeOutput {
        call: P<Node>,
        type_index: usize,
    },
    Argument {
        call: P<Node>,
        index: usize,
        output: bool,
    },
}
impl FlowType {
    fn get(&self, ctx: &mut RuleContext<'_>) -> Option<P<Type>> {
        match *self {
            Self::Node(node) => Some(ctx.ty(node)),
            Self::PipeOutput { call, type_index } => {
                let signature = ctx.checker.get_resolved_signature_exported(call);
                ctx.checker
                    .get_type_arguments_for_resolved_signature(signature)
                    .get(type_index)
                    .copied()
            }
            Self::Argument {
                call,
                index,
                output,
            } => {
                let t = ctx
                    .checker
                    .get_contextual_type_for_argument_at_index_exported(call, index);
                let signatures = ctx.checker.get_signatures_of_type(t, SignatureKind::Call);
                let sig = *signatures.first()?;
                if output {
                    Some(ctx.checker.get_return_type_of_signature(sig))
                } else {
                    sig.parameters()
                        .first()
                        .map(|s| ctx.checker.get_type_of_symbol_exported(*s))
                }
            }
        }
    }
}

#[derive(Clone)]
pub(crate) struct FlowTransformation {
    pub kind: TransformationKind,
    pub callee: P<Node>,
    pub args: Vec<P<Node>>,
    pub type_arguments: Vec<P<Node>>,
    output: FlowType,
    input: Option<P<Node>>,
}
impl FlowTransformation {
    pub fn out_type(&self, ctx: &mut RuleContext<'_>) -> Option<P<Type>> {
        self.output.get(ctx)
    }
}

#[derive(Clone)]
pub(crate) struct PipingFlow {
    pub node: P<Node>,
    pub subject: P<Node>,
    pub transformations: Vec<FlowTransformation>,
    subject_type: FlowType,
}
impl PipingFlow {
    pub fn subject_type(&self, ctx: &mut RuleContext<'_>) -> Option<P<Type>> {
        self.subject_type.get(ctx)
    }
    pub fn input_type(&self, ctx: &mut RuleContext<'_>, index: usize) -> Option<P<Type>> {
        if index >= self.transformations.len() {
            return None;
        }
        if index == 0 {
            self.subject_type(ctx)
        } else {
            self.transformations[index - 1].out_type(ctx)
        }
    }
    pub fn input_node(&self, index: usize) -> Option<P<Node>> {
        let step = self.transformations.get(index)?;
        step.input.or_else(|| (index == 0).then_some(self.subject))
    }
    pub fn copy_prefix(&self, count: usize) -> Option<Self> {
        if count > self.transformations.len() {
            return None;
        }
        let mut result = self.clone();
        result.transformations.truncate(count);
        Some(result)
    }
}

#[derive(Clone)]
pub(crate) struct ParsedPipeCall {
    pub node: P<Node>,
    pub subject: P<Node>,
    pub args: Vec<P<Node>>,
    pub kind: TransformationKind,
}

pub(crate) fn unwrap_expression(mut node: P<Node>) -> P<Node> {
    while matches!(
        node.kind(),
        Kind::ParenthesizedExpression
            | Kind::AsExpression
            | Kind::SatisfiesExpression
            | Kind::NonNullExpression
            | Kind::TypeAssertionExpression
    ) {
        let Some(expression) = node.expression() else {
            break;
        };
        node = expression;
    }
    node
}
fn type_arguments(node: P<Node>) -> Vec<P<Node>> {
    let node = unwrap_expression(node);
    if node.kind() != Kind::CallExpression {
        return Vec::new();
    }
    node.as_call_expression()
        .type_arguments()
        .map(|t| t.nodes().to_vec())
        .unwrap_or_default()
}
fn checked_call(node: P<Node>) -> Option<P<Node>> {
    let node = unwrap_expression(node);
    if node.kind() != Kind::CallExpression || ast::is_optional_chain(node) {
        return None;
    }
    let c = node.as_call_expression();
    if ast::is_optional_chain(unwrap_expression(c.expression))
        || c.arguments
            .nodes()
            .iter()
            .any(|n| unwrap_expression(*n).kind() == Kind::SpreadElement)
    {
        return None;
    }
    Some(node)
}
fn raw_signature(mut s: P<Signature>) -> P<Signature> {
    while let Some(t) = s.target() {
        s = t;
    }
    s
}

impl RuleContext<'_> {
    pub(crate) fn parse_pipe_call(&mut self, node: P<Node>) -> Option<ParsedPipeCall> {
        let node = checked_call(node)?;
        let call = node.as_call_expression();
        let callee = unwrap_expression(call.expression);
        let args = call.arguments.nodes();
        if self.is_package_api(callee, "effect", "pipe") || self.is_api(callee, "Function", "pipe")
        {
            return Some(ParsedPipeCall {
                node,
                subject: *args.first()?,
                args: args[1..].to_vec(),
                kind: TransformationKind::Pipe,
            });
        }
        if callee.kind() == Kind::PropertyAccessExpression {
            let access = callee.as_property_access_expression();
            if access.name().text() == "pipe" {
                return Some(ParsedPipeCall {
                    node,
                    subject: access.expression,
                    args: args.to_vec(),
                    kind: TransformationKind::Pipeable,
                });
            }
        }
        None
    }

    pub(crate) fn piping_flows(&mut self, include_effect_fn: bool) -> Vec<PipingFlow> {
        let cached = if include_effect_fn {
            &self.semantic.flows_with_fn
        } else {
            &self.semantic.flows
        };
        if let Some(flows) = cached {
            return flows.clone();
        }
        let mut queue = self.file.as_node().iter_children();
        let mut result = Vec::new();
        while let Some(node) = queue.pop() {
            let node = unwrap_expression(node);
            let (flow, independent) = self.build_piping_flow(node, include_effect_fn);
            if !flow.transformations.is_empty() {
                result.push(flow);
                queue.extend(independent);
            } else {
                queue.extend(node.iter_children());
            }
        }
        result.sort_by_key(|flow| flow.node.pos());
        if include_effect_fn {
            self.semantic.flows_with_fn = Some(result.clone());
        } else {
            self.semantic.flows = Some(result.clone());
        }
        result
    }

    pub(crate) fn longest_piping_flow_at(
        &mut self,
        node: P<Node>,
        include_effect_fn: bool,
    ) -> Option<PipingFlow> {
        if !ast::is_expression(node) {
            return None;
        }
        Some(self.build_piping_flow(node, include_effect_fn).0)
    }

    fn build_piping_flow(
        &mut self,
        root: P<Node>,
        include_effect_fn: bool,
    ) -> (PipingFlow, Vec<P<Node>>) {
        let root = unwrap_expression(root);
        let mut node = root;
        let mut segments: Vec<Vec<FlowTransformation>> = Vec::new();
        let mut independent = Vec::new();
        let mut subject_type = None;
        let mut visit_subject_children = true;
        loop {
            node = unwrap_expression(node);
            if let Some(pipe) = self.parse_pipe_call(node) {
                let offset = usize::from(pipe.kind == TransformationKind::Pipe);
                let mut steps = Vec::new();
                for (i, arg) in pipe.args.iter().copied().enumerate() {
                    steps.push(self.pipe_step(arg, pipe.kind, node, offset + i));
                    independent.extend(unwrap_expression(arg).iter_children());
                }
                segments.push(steps);
                node = pipe.subject;
                continue;
            }
            if include_effect_fn && let Some((function, trailing, kind)) = self.flow_fn_call(node) {
                let call = node.as_call_expression();
                let offset = call.arguments.nodes().len() - trailing.len();
                if !trailing.is_empty() {
                    let steps = trailing
                        .iter()
                        .enumerate()
                        .map(|(i, arg)| self.pipe_step(*arg, kind, node, offset + i))
                        .collect();
                    // An Effect.fn expression is a separate flow boundary.
                    visit_subject_children = false;
                    if !segments.is_empty() {
                        independent.push(node);
                    } else {
                        subject_type = Some(FlowType::Argument {
                            call: node,
                            index: offset,
                            output: false,
                        });
                        segments.push(steps);
                        independent.extend(function.iter_children());
                        for arg in trailing {
                            independent.extend(unwrap_expression(arg).iter_children());
                        }
                    }
                    break;
                }
            }
            let Some(call_node) = checked_call(node) else {
                break;
            };
            let call = call_node.as_call_expression();
            let arguments = call.arguments.nodes();
            if let Some(subject_index) = self.data_subject_index(call_node) {
                let args: Vec<_> = arguments
                    .iter()
                    .enumerate()
                    .filter_map(|(i, arg)| (i != subject_index).then_some(*arg))
                    .collect();
                for arg in &args {
                    independent.extend(arg.iter_children());
                }
                independent.extend(call.expression.iter_children());
                segments.push(vec![FlowTransformation {
                    kind: if subject_index == 0 {
                        TransformationKind::DataFirst
                    } else {
                        TransformationKind::DataLast
                    },
                    callee: call.expression,
                    args,
                    type_arguments: type_arguments(call_node),
                    output: FlowType::Node(call_node),
                    input: Some(arguments[subject_index]),
                }]);
                node = arguments[subject_index];
                continue;
            }
            if arguments.len() == 1 {
                let mut callee = call.expression;
                let mut args = Vec::new();
                let mut type_src = call_node;
                if let Some(factory_node) = checked_call(callee) {
                    if self.curried_pipeable(factory_node, arguments[0]) {
                        let factory = factory_node.as_call_expression();
                        callee = factory.expression;
                        args = factory.arguments.nodes().to_vec();
                        type_src = factory_node;
                        independent.push(callee);
                        independent.extend(args.iter().copied());
                    } else {
                        independent.extend(callee.iter_children());
                    }
                } else {
                    independent.extend(callee.iter_children());
                }
                segments.push(vec![FlowTransformation {
                    kind: TransformationKind::Call,
                    callee,
                    args,
                    type_arguments: type_arguments(type_src),
                    output: FlowType::Node(call_node),
                    input: Some(arguments[0]),
                }]);
                node = arguments[0];
                continue;
            }
            break;
        }
        if visit_subject_children {
            independent.extend(node.iter_children());
        }
        let transformations = segments.into_iter().rev().flatten().collect();
        (
            PipingFlow {
                node: root,
                subject: node,
                transformations,
                subject_type: subject_type.unwrap_or(FlowType::Node(node)),
            },
            independent,
        )
    }

    fn pipe_step(
        &self,
        argument: P<Node>,
        kind: TransformationKind,
        call: P<Node>,
        index: usize,
    ) -> FlowTransformation {
        let node = unwrap_expression(argument);
        let (callee, args) = if node.kind() == Kind::CallExpression {
            let c = node.as_call_expression();
            (c.expression, c.arguments.nodes().to_vec())
        } else {
            (node, Vec::new())
        };
        FlowTransformation {
            kind,
            callee,
            args,
            type_arguments: type_arguments(node),
            output: if matches!(
                kind,
                TransformationKind::Pipe | TransformationKind::Pipeable
            ) {
                FlowType::PipeOutput {
                    call,
                    type_index: index + usize::from(kind == TransformationKind::Pipeable),
                }
            } else {
                FlowType::Argument {
                    call,
                    index,
                    output: true,
                }
            },
            input: None,
        }
    }

    fn flow_fn_call(
        &mut self,
        node: P<Node>,
    ) -> Option<(P<Node>, Vec<P<Node>>, TransformationKind)> {
        let parsed = self.parsed_fn(checked_call(node)?)?;
        Some((
            parsed.function,
            parsed.pipe_arguments,
            if parsed.untraced {
                TransformationKind::EffectFnUntraced
            } else {
                TransformationKind::EffectFn
            },
        ))
    }

    fn data_subject_index(&mut self, node: P<Node>) -> Option<usize> {
        let call = node.as_call_expression();
        let args = call.arguments.nodes();
        if args.len() < 2 {
            return None;
        }
        let resolved = self.checker.get_resolved_signature_exported(node);
        if args.len() < resolved.min_argument_count()
            || args.len() > resolved.parameters().len() && !resolved.has_rest_parameter()
        {
            return None;
        }
        let raw = raw_signature(resolved);
        let ty = self.ty(call.expression);
        let candidates = self
            .checker
            .get_signatures_of_type(ty, SignatureKind::Call)
            .to_vec();
        let prefer_first = resolved.parameters().first().is_some_and(|s| {
            s.name().to_ascii_lowercase().starts_with("self") || s.name() == "this"
        });
        let indexes = if args.len() == 2 && !prefer_first {
            vec![1, 0]
        } else if args.len() == 2 {
            vec![0, 1]
        } else {
            vec![0]
        };
        let mut found = None;
        for index in indexes {
            for candidate in &candidates {
                if self.flow_same_overload_symbol(raw, raw_signature(*candidate))
                    && self.pipeable_shapes_match(raw, raw_signature(*candidate), index)
                    && self.pipeable_witness(*candidate, args, index)
                {
                    if let Some(previous) = found
                        && previous != index
                    {
                        return if prefer_first { Some(0) } else { None };
                    }
                    found = Some(index);
                    break;
                }
            }
        }
        found
    }
    fn curried_pipeable(&mut self, factory: P<Node>, subject: P<Node>) -> bool {
        let call = factory.as_call_expression();
        if call.arguments.nodes().is_empty() {
            return false;
        }
        let pipeable = raw_signature(self.checker.get_resolved_signature_exported(factory));
        let ty = self.ty(call.expression);
        for sig in self
            .checker
            .get_signatures_of_type(ty, SignatureKind::Call)
            .to_vec()
        {
            if sig == pipeable {
                continue;
            }
            for index in [0, sig.parameters().len().saturating_sub(1)] {
                if self.flow_same_overload_symbol(raw_signature(sig), pipeable)
                    && self.pipeable_shapes_match(raw_signature(sig), pipeable, index)
                {
                    let mut args = call.arguments.nodes().to_vec();
                    if index > args.len() {
                        continue;
                    }
                    args.insert(index, subject);
                    if self.pipeable_witness(pipeable, &args, index) {
                        return true;
                    }
                }
            }
        }
        false
    }
    fn pipeable_witness(
        &mut self,
        candidate: P<Signature>,
        arguments: &[P<Node>],
        subject_index: usize,
    ) -> bool {
        let args: Vec<_> = arguments
            .iter()
            .enumerate()
            .filter_map(|(i, n)| (i != subject_index).then_some(*n))
            .collect();
        if args.len() < candidate.min_argument_count()
            || args.len() > candidate.parameters().len() && !candidate.has_rest_parameter()
        {
            return false;
        }
        for (i, arg) in args.iter().enumerate() {
            let Some(parameter) = candidate
                .parameters()
                .get(i.min(candidate.parameters().len().saturating_sub(1)))
            else {
                return false;
            };
            let a = self.ty(*arg);
            let p = self.checker.get_type_of_symbol_exported(*parameter);
            if !self.flow_type_accepts(a, p)
                && (candidate.type_parameters().is_empty() || !self.same_callable_shape(a, p))
            {
                return false;
            }
        }
        let returned = self.checker.get_return_type_of_signature(candidate);
        let t = self.ty(arguments[subject_index]);
        for sig in self
            .checker
            .get_signatures_of_type(returned, SignatureKind::Call)
            .to_vec()
        {
            if sig.parameters().len() != 1 || sig.has_rest_parameter() {
                continue;
            }
            let p = self
                .checker
                .get_type_of_symbol_exported(sig.parameters()[0]);
            if self.flow_type_accepts(t, p)
                || ((!candidate.type_parameters().is_empty() || !sig.type_parameters().is_empty())
                    && self.same_callable_shape(t, p))
            {
                return true;
            }
        }
        false
    }
    fn same_callable_shape(&mut self, a: P<Type>, b: P<Type>) -> bool {
        self.checker
            .get_signatures_of_type(a, SignatureKind::Call)
            .is_empty()
            == self
                .checker
                .get_signatures_of_type(b, SignatureKind::Call)
                .is_empty()
    }
    fn flow_type_accepts(&mut self, a: P<Type>, b: P<Type>) -> bool {
        if b.flags().intersects(TypeFlags::TypeParameter) {
            return self
                .checker
                .get_constraint_of_type_parameter_exported(b)
                .is_none_or(|c| self.flow_type_accepts(a, c));
        }
        if a == b {
            return true;
        }
        if a.object_flags().intersects(ObjectFlags::Reference)
            && b.object_flags().intersects(ObjectFlags::Reference)
            && a.target() == b.target()
        {
            return true;
        }
        self.checker.is_type_assignable_to(a, b)
    }
    fn flow_same_overload_symbol(&mut self, a: P<Signature>, b: P<Signature>) -> bool {
        let Some(a) = a.declaration() else {
            return true;
        };
        let Some(b) = b.declaration() else {
            return false;
        };
        let a = self.checker.get_symbol_of_declaration_exported(a);
        let b = self.checker.get_symbol_of_declaration_exported(b);
        same_type_symbol(self, a, b)
    }
    pub(crate) fn pipeable_shapes_match(
        &mut self,
        data: P<Signature>,
        candidate: P<Signature>,
        index: usize,
    ) -> bool {
        let key = (raw_signature(data), raw_signature(candidate), index);
        if let Some(result) = self.semantic.pipeable_shapes.get(&key) {
            return *result;
        }
        let result = self.compute_pipeable_shapes_match(key.0, key.1, key.2);
        self.semantic.pipeable_shapes.insert(key, result);
        result
    }
    fn compute_pipeable_shapes_match(
        &mut self,
        data: P<Signature>,
        candidate: P<Signature>,
        index: usize,
    ) -> bool {
        if index >= data.parameters().len()
            || data.parameters().len() != candidate.parameters().len() + 1
        {
            return false;
        }
        let data = raw_signature(data);
        let candidate = raw_signature(candidate);
        let returned = self.checker.get_return_type_of_signature(candidate);
        let inner = self
            .checker
            .get_signatures_of_type(returned, SignatureKind::Call);
        if inner.len() != 1
            || inner[0].target().is_some()
            || inner[0].parameters().len() != 1
            || inner[0].has_rest_parameter()
        {
            return false;
        }
        let inner = inner[0];
        let mut matcher = ShapeMatcher::default();
        for t in data.type_parameters() {
            matcher.left_binders.insert(*t);
        }
        for t in candidate
            .type_parameters()
            .iter()
            .chain(inner.type_parameters())
        {
            matcher.right_binders.insert(*t);
        }
        if matcher.left_binders.len() != matcher.right_binders.len() {
            return false;
        }
        let mut j = 0;
        for (i, p) in data.parameters().iter().enumerate() {
            let q = if i == index {
                inner.parameters()[0]
            } else {
                let q = candidate.parameters()[j];
                j += 1;
                q
            };
            let left_rest = i + 1 == data.parameters().len() && data.has_rest_parameter();
            let right_rest =
                i != index && j == candidate.parameters().len() && candidate.has_rest_parameter();
            if left_rest != right_rest
                || p.flags().intersects(SymbolFlags::Optional)
                    != q.flags().intersects(SymbolFlags::Optional)
            {
                return false;
            }
            let a = self.checker.get_type_of_symbol_exported(*p);
            let b = self.checker.get_type_of_symbol_exported(q);
            if !matcher.matches(self, a, b, 0) {
                return false;
            }
        }
        let a = self.checker.get_return_type_of_signature(data);
        let b = self.checker.get_return_type_of_signature(inner);
        matcher.matches(self, a, b, 0) && matcher.validate_binders(self)
    }
}

#[derive(Clone, Default)]
struct ShapeMatcher {
    left_binders: HashSet<P<Type>>,
    right_binders: HashSet<P<Type>>,
    mapping: HashMap<P<Type>, P<Type>>,
    reverse: HashMap<P<Type>, P<Type>>,
    seen: HashSet<(P<Type>, P<Type>)>,
    work: usize,
    union_search: usize,
}
impl ShapeMatcher {
    fn matches(&mut self, ctx: &mut RuleContext<'_>, a: P<Type>, b: P<Type>, depth: usize) -> bool {
        let a = nondistributed_type(a);
        let b = nondistributed_type(b);
        if a == b {
            return true;
        }
        self.work += 1;
        if depth > 64 || self.work > 4096 {
            return false;
        }
        if let Some(base) = no_infer_base(ctx, a) {
            return self.matches(ctx, base, b, depth + 1);
        }
        if let Some(base) = no_infer_base(ctx, b) {
            return self.matches(ctx, a, base, depth + 1);
        }
        if !self.seen.insert((a, b)) {
            return true;
        }
        let result = self.compare(ctx, a, b, depth);
        self.seen.remove(&(a, b));
        result
    }
    fn compare(&mut self, ctx: &mut RuleContext<'_>, a: P<Type>, b: P<Type>, depth: usize) -> bool {
        if a.alias().is_some() || b.alias().is_some() {
            let (Some(x), Some(y)) = (a.alias(), b.alias()) else {
                return false;
            };
            if !same_type_symbol(ctx, x.symbol(), y.symbol()) {
                return false;
            }
            return self.list(ctx, x.type_arguments(), y.type_arguments(), depth + 1);
        }
        if a.flags().intersects(TypeFlags::TypeParameter)
            || b.flags().intersects(TypeFlags::TypeParameter)
        {
            if !a.flags().intersects(TypeFlags::TypeParameter)
                || !b.flags().intersects(TypeFlags::TypeParameter)
            {
                return false;
            }
            if self.left_binders.contains(&a) || self.right_binders.contains(&b) {
                if !self.left_binders.contains(&a) || !self.right_binders.contains(&b) {
                    return false;
                }
                if let Some(mapped) = self.mapping.get(&a) {
                    return *mapped == b;
                }
                if self.reverse.contains_key(&b) {
                    return false;
                }
                self.mapping.insert(a, b);
                self.reverse.insert(b, a);
                return true;
            }
            return same_type_symbol(ctx, a.symbol(), b.symbol());
        }
        if a.flags() != b.flags() {
            return false;
        }
        if a.flags().intersects(TypeFlags::Union) {
            if a.types().len() != b.types().len() {
                return false;
            }
            return self.union_at(
                ctx,
                a.types(),
                b.types(),
                &vec![false; b.types().len()],
                0,
                depth + 1,
            );
        }
        if a.flags().intersects(TypeFlags::Intersection) {
            return self.list(ctx, a.types(), b.types(), depth + 1);
        }
        if a.flags().intersects(TypeFlags::Conditional) {
            let x = a.as_conditional_type();
            let y = b.as_conditional_type();
            if !self.optional(ctx, x.check_type(), y.check_type(), depth + 1)
                || !self.optional(ctx, x.extends_type(), y.extends_type(), depth + 1)
            {
                return false;
            }
            let x = ctx.checker.get_true_type_of_conditional_type(a);
            let y = ctx.checker.get_true_type_of_conditional_type(b);
            if !self.matches(ctx, x, y, depth + 1) {
                return false;
            }
            let x = ctx.checker.get_false_type_of_conditional_type(a);
            let y = ctx.checker.get_false_type_of_conditional_type(b);
            return self.matches(ctx, x, y, depth + 1);
        }
        if a.flags().intersects(TypeFlags::IndexedAccess) {
            let x = a.as_indexed_access_type();
            let y = b.as_indexed_access_type();
            return self.optional(ctx, x.object_type(), y.object_type(), depth + 1)
                && self.optional(ctx, x.index_type(), y.index_type(), depth + 1);
        }
        if a.flags().intersects(TypeFlags::Index) {
            return self.optional(
                ctx,
                a.as_index_type().target(),
                b.as_index_type().target(),
                depth + 1,
            );
        }
        if a.flags().intersects(TypeFlags::TemplateLiteral) {
            return a.as_template_literal_type().texts() == b.as_template_literal_type().texts()
                && self.list(ctx, a.types(), b.types(), depth + 1);
        }
        if a.flags().intersects(TypeFlags::StringMapping) {
            return same_type_symbol(ctx, a.symbol(), b.symbol())
                && self.optional(
                    ctx,
                    a.as_string_mapping_type().target(),
                    b.as_string_mapping_type().target(),
                    depth + 1,
                );
        }
        if a.flags().intersects(TypeFlags::Substitution) {
            let x = a.as_substitution_type();
            let y = b.as_substitution_type();
            return self.optional(ctx, x.base_type(), y.base_type(), depth + 1)
                && self.optional(ctx, x.subst_constraint(), y.subst_constraint(), depth + 1);
        }
        if a.flags().intersects(TypeFlags::Object) {
            return self.object(ctx, a, b, depth + 1);
        }
        if a.flags().intersects(TypeFlags::Literal) {
            return a.as_literal_type().value() == b.as_literal_type().value()
                && same_optional_symbol(ctx, a.symbol(), b.symbol());
        }
        if a.flags()
            .intersects(TypeFlags::UniqueESSymbol | TypeFlags::Enum)
        {
            return same_type_symbol(ctx, a.symbol(), b.symbol());
        }
        a.flags().intersects(TypeFlags::Singleton)
    }
    fn object(&mut self, ctx: &mut RuleContext<'_>, a: P<Type>, b: P<Type>, depth: usize) -> bool {
        let x = a.object_flags();
        let y = b.object_flags();
        if x.intersects(ObjectFlags::Mapped) || y.intersects(ObjectFlags::Mapped) {
            if !x.intersects(ObjectFlags::Mapped) || !y.intersects(ObjectFlags::Mapped) {
                return false;
            }
            if tsrs_checker::get_mapped_type_modifiers(a)
                != tsrs_checker::get_mapped_type_modifiers(b)
            {
                return false;
            }
            tsrs_checker::MappedType::resolve_components(ctx.checker, a);
            tsrs_checker::MappedType::resolve_components(ctx.checker, b);
            let x = a.as_mapped_type();
            let y = b.as_mapped_type();
            let (Some(l), Some(r)) = (x.type_parameter(), y.type_parameter()) else {
                return false;
            };
            self.left_binders.insert(l);
            self.right_binders.insert(r);
            return self.matches(ctx, l, r, depth + 1)
                && self.optional(ctx, x.constraint_type(), y.constraint_type(), depth + 1)
                && self.optional(ctx, x.name_type(), y.name_type(), depth + 1)
                && self.optional(ctx, x.template_type(), y.template_type(), depth + 1);
        }
        let unsupported = ObjectFlags::ReverseMapped
            | ObjectFlags::EvolvingArray
            | ObjectFlags::InstantiationExpressionType;
        if x.intersects(unsupported) || y.intersects(unsupported) {
            return false;
        }
        if x.intersects(ObjectFlags::Reference) || y.intersects(ObjectFlags::Reference) {
            if !x.intersects(ObjectFlags::Reference) || !y.intersects(ObjectFlags::Reference) {
                return false;
            }
            let (Some(at), Some(bt)) = (a.target(), b.target()) else {
                return false;
            };
            if at != bt && !same_type_symbol(ctx, at.symbol(), bt.symbol()) {
                return false;
            }
            let left = ctx.checker.get_type_arguments(a).to_vec();
            let right = ctx.checker.get_type_arguments(b).to_vec();
            return self.list(ctx, &left, &right, depth + 1);
        }
        if !x.intersects(ObjectFlags::Anonymous) || !y.intersects(ObjectFlags::Anonymous) {
            return !x.intersects(ObjectFlags::Anonymous)
                && !y.intersects(ObjectFlags::Anonymous)
                && same_type_symbol(ctx, a.symbol(), b.symbol());
        }
        let left = ctx.checker.get_properties_of_type(a).to_vec();
        let right = ctx.checker.get_properties_of_type(b).to_vec();
        if left.len() != right.len() {
            return false;
        }
        for p in left {
            let Some(q) = right.iter().find(|q| q.name() == p.name()).copied() else {
                return false;
            };
            if ctx.checker.is_readonly_symbol_exported(p)
                != ctx.checker.is_readonly_symbol_exported(q)
                || !self.parameter(ctx, p, false, q, false, depth + 1)
            {
                return false;
            }
        }
        let left = ctx.checker.get_index_infos_of_type(a).to_vec();
        let right = ctx.checker.get_index_infos_of_type(b).to_vec();
        if left.len() != right.len() {
            return false;
        }
        for (x, y) in left.into_iter().zip(right) {
            if x.is_readonly() != y.is_readonly()
                || !self.matches(ctx, x.key_type(), y.key_type(), depth + 1)
                || !self.matches(ctx, x.value_type(), y.value_type(), depth + 1)
            {
                return false;
            }
        }
        if !ctx
            .checker
            .get_signatures_of_type(a, SignatureKind::Construct)
            .is_empty()
            || !ctx
                .checker
                .get_signatures_of_type(b, SignatureKind::Construct)
                .is_empty()
        {
            return false;
        }
        let left = ctx
            .checker
            .get_signatures_of_type(a, SignatureKind::Call)
            .to_vec();
        let right = ctx
            .checker
            .get_signatures_of_type(b, SignatureKind::Call)
            .to_vec();
        if left.len() != right.len() {
            return false;
        }
        left.into_iter().zip(right).all(|(x, y)| {
            x.target().is_none() && y.target().is_none() && self.signature(ctx, x, y, depth + 1)
        })
    }
    fn signature(
        &mut self,
        ctx: &mut RuleContext<'_>,
        a: P<Signature>,
        b: P<Signature>,
        depth: usize,
    ) -> bool {
        if a.has_rest_parameter() != b.has_rest_parameter()
            || a.min_argument_count() != b.min_argument_count()
            || a.parameters().len() != b.parameters().len()
            || ctx
                .checker
                .get_type_predicate_of_signature_exported(a)
                .is_some()
            || ctx
                .checker
                .get_type_predicate_of_signature_exported(b)
                .is_some()
        {
            return false;
        }
        self.left_binders
            .extend(a.type_parameters().iter().copied());
        self.right_binders
            .extend(b.type_parameters().iter().copied());
        match (a.this_parameter(), b.this_parameter()) {
            (None, None) => {}
            (Some(x), Some(y)) => {
                if !self.parameter(ctx, x, false, y, false, depth + 1) {
                    return false;
                }
            }
            _ => return false,
        }
        for (i, (x, y)) in a.parameters().iter().zip(b.parameters()).enumerate() {
            if !self.parameter(
                ctx,
                *x,
                i + 1 == a.parameters().len() && a.has_rest_parameter(),
                *y,
                i + 1 == b.parameters().len() && b.has_rest_parameter(),
                depth + 1,
            ) {
                return false;
            }
        }
        let x = ctx.checker.get_return_type_of_signature(a);
        let y = ctx.checker.get_return_type_of_signature(b);
        self.matches(ctx, x, y, depth + 1)
    }
    fn parameter(
        &mut self,
        ctx: &mut RuleContext<'_>,
        a: P<Symbol>,
        a_rest: bool,
        b: P<Symbol>,
        b_rest: bool,
        depth: usize,
    ) -> bool {
        if a_rest != b_rest
            || a.flags().intersects(SymbolFlags::Optional)
                != b.flags().intersects(SymbolFlags::Optional)
        {
            return false;
        }
        let a = ctx.checker.get_type_of_symbol_exported(a);
        let b = ctx.checker.get_type_of_symbol_exported(b);
        self.matches(ctx, a, b, depth + 1)
    }
    fn optional(
        &mut self,
        ctx: &mut RuleContext<'_>,
        a: Option<P<Type>>,
        b: Option<P<Type>>,
        depth: usize,
    ) -> bool {
        match (a, b) {
            (None, None) => true,
            (Some(a), Some(b)) => self.matches(ctx, a, b, depth),
            _ => false,
        }
    }
    fn list(
        &mut self,
        ctx: &mut RuleContext<'_>,
        a: &[P<Type>],
        b: &[P<Type>],
        depth: usize,
    ) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(a, b)| self.matches(ctx, *a, *b, depth + 1))
    }
    fn union_at(
        &mut self,
        ctx: &mut RuleContext<'_>,
        a: &[P<Type>],
        b: &[P<Type>],
        used: &[bool],
        i: usize,
        depth: usize,
    ) -> bool {
        if i == a.len() {
            return true;
        }
        for j in 0..b.len() {
            if used[j] {
                continue;
            }
            self.union_search += 1;
            if self.union_search > 128 {
                return false;
            }
            let mut branch = self.clone();
            if !branch.matches(ctx, a[i], b[j], depth + 1) {
                self.work = self.work.max(branch.work);
                self.union_search = self.union_search.max(branch.union_search);
                continue;
            }
            let mut taken = used.to_vec();
            taken[j] = true;
            if branch.union_at(ctx, a, b, &taken, i + 1, depth + 1) {
                *self = branch;
                return true;
            }
            self.work = self.work.max(branch.work);
            self.union_search = self.union_search.max(branch.union_search);
        }
        false
    }
    fn validate_binders(&mut self, ctx: &mut RuleContext<'_>) -> bool {
        if self.left_binders.len() != self.right_binders.len()
            || self.mapping.len() != self.left_binders.len()
        {
            return false;
        }
        let mappings: Vec<_> = self.mapping.iter().map(|(a, b)| (*a, *b)).collect();
        for (a, b) in mappings {
            if binder_modifiers(a) != binder_modifiers(b) {
                return false;
            }
            let x = ctx.checker.get_constraint_of_type_parameter_exported(a);
            let y = ctx.checker.get_constraint_of_type_parameter_exported(b);
            if !self.optional(ctx, x, y, 0) {
                return false;
            }
            let x = ctx.checker.get_default_from_type_parameter_exported(a);
            let y = ctx.checker.get_default_from_type_parameter_exported(b);
            if !self.optional(ctx, x, y, 0) {
                return false;
            }
        }
        true
    }
}
fn nondistributed_type(t: P<Type>) -> P<Type> {
    if t.flags().intersects(TypeFlags::TypeParameter) && t.as_type_parameter().is_distributed.get()
    {
        t.as_type_parameter().constraint.get().unwrap_or(t)
    } else {
        t
    }
}
fn same_type_symbol(ctx: &mut RuleContext<'_>, a: Option<P<Symbol>>, b: Option<P<Symbol>>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => ctx.same_symbol(a, b),
        _ => false,
    }
}
fn same_optional_symbol(
    ctx: &mut RuleContext<'_>,
    a: Option<P<Symbol>>,
    b: Option<P<Symbol>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => ctx.same_symbol(a, b),
        _ => false,
    }
}
fn binder_modifiers(t: P<Type>) -> ModifierFlags {
    t.symbol()
        .map(|s| {
            s.declarations()
                .iter()
                .fold(ModifierFlags::None, |flags, d| flags | d.modifier_flags())
        })
        .unwrap_or(ModifierFlags::None)
        & (ModifierFlags::In | ModifierFlags::Out | ModifierFlags::Const)
}
fn no_infer_base(ctx: &mut RuleContext<'_>, t: P<Type>) -> Option<P<Type>> {
    if t.flags().intersects(TypeFlags::Substitution)
        && t.as_substitution_type()
            .subst_constraint()
            .is_some_and(|c| c.flags().intersects(TypeFlags::Unknown))
    {
        return t.as_substitution_type().base_type();
    }
    let alias = t.alias()?;
    if alias.type_arguments().len() != 1 {
        return None;
    }
    let symbol = alias.symbol()?;
    for declaration in symbol.declarations() {
        if declaration.kind() != Kind::TypeAliasDeclaration {
            continue;
        }
        let declaration = declaration.as_type_alias_declaration();
        let Some(parameters) = declaration.type_parameters() else {
            continue;
        };
        if parameters.nodes().len() != 1 {
            continue;
        }
        let Some(body) = declaration.type_() else {
            continue;
        };
        if body.kind() == Kind::IntrinsicKeyword {
            return Some(alias.type_arguments()[0]);
        }
        if body.kind() != Kind::IndexedAccessType {
            continue;
        }
        let indexed = body.as_indexed_access_type_node();
        if indexed.object_type.kind() != Kind::TupleType
            || indexed.index_type.kind() != Kind::ConditionalType
        {
            continue;
        }
        let elements = indexed.object_type.as_tuple_type_node().elements.nodes();
        if elements.len() != 1 {
            continue;
        }
        let conditional = indexed.index_type.as_conditional_type_node();
        if conditional.extends_type.kind() != Kind::AnyKeyword
            || conditional.false_type.kind() != Kind::NeverKeyword
        {
            continue;
        }
        let numeric = conditional.true_type;
        if numeric.kind() != Kind::LiteralType {
            continue;
        }
        let literal = numeric.as_literal_type_node().literal;
        if literal.kind() != Kind::NumericLiteral || literal.text() != "0" {
            continue;
        }
        let binder = parameters.nodes()[0].name().and_then(|n| ctx.symbol(n));
        let is_binder = |ctx: &mut RuleContext<'_>, n: P<Node>| {
            if n.kind() != Kind::TypeReference || n.type_argument_list().is_some() {
                return false;
            }
            let target = ctx.symbol(n.as_type_reference_node().type_name);
            same_type_symbol(ctx, binder, target)
        };
        if is_binder(ctx, elements[0]) && is_binder(ctx, conditional.check_type) {
            return Some(alias.type_arguments()[0]);
        }
    }
    None
}

pub(crate) const LAZY_THUNK: u8 = 1;
pub(crate) const LAZY_ALLOW_ASYNC: u8 = 2;
pub(crate) const LAZY_ALLOW_GENERATOR: u8 = 4;
pub(crate) const LAZY_ALLOW_MULTI_STATEMENT: u8 = 8;
#[derive(Clone)]
pub(crate) struct LazyExpression {
    pub node: P<Node>,
    pub expression: P<Node>,
    pub params: Vec<P<Node>>,
}
#[derive(Clone)]
pub(crate) struct IdentityForwarder {
    pub target: P<Node>,
    pub type_arguments: Vec<P<Node>>,
    pub parameter: Option<P<Node>>,
}

fn function_parts(node: P<Node>) -> Option<(P<Node>, Vec<P<Node>>)> {
    if !matches!(node.kind(), Kind::ArrowFunction | Kind::FunctionExpression) {
        return None;
    }
    let data = node.function_like_data()?;
    if data
        .type_parameters
        .get()
        .is_some_and(|p| !p.nodes().is_empty())
    {
        return None;
    }
    Some((node.body()?, node.parameters().to_vec()))
}
fn single_return(node: P<Node>) -> Option<P<Node>> {
    if node.kind() == Kind::ReturnStatement {
        return node.as_return_statement().expression();
    }
    if node.kind() != Kind::Block {
        return None;
    }
    let statements = node.as_block().statements.nodes();
    if statements.len() != 1 {
        return None;
    }
    if statements[0].kind() == Kind::ReturnStatement {
        statements[0].as_return_statement().expression()
    } else {
        None
    }
}
fn contains_return(node: P<Node>) -> bool {
    if node.kind() == Kind::ReturnStatement {
        return true;
    }
    if ast::is_function_like(node) {
        return false;
    }
    node.iter_children().into_iter().any(contains_return)
}
impl RuleContext<'_> {
    pub(crate) fn parse_lazy_expression(
        &mut self,
        node: P<Node>,
        flags: u8,
    ) -> Option<LazyExpression> {
        let node = unwrap_expression(node);
        if flags & LAZY_ALLOW_ASYNC == 0
            && ast::get_combined_modifier_flags(node).intersects(ModifierFlags::Async)
        {
            return None;
        }
        let (body, params) = function_parts(node)?;
        if flags & LAZY_THUNK != 0 && !params.is_empty() {
            return None;
        }
        if flags & LAZY_ALLOW_GENERATOR == 0 && node.body_data()?.asterisk_token.is_some() {
            return None;
        }
        let expression = if body.kind() == Kind::Block {
            let statements = body.as_block().statements.nodes();
            if statements.is_empty()
                || flags & LAZY_ALLOW_MULTI_STATEMENT == 0 && statements.len() != 1
            {
                return None;
            }
            let last = *statements.last()?;
            if last.kind() != Kind::ReturnStatement {
                return None;
            }
            if flags & LAZY_ALLOW_MULTI_STATEMENT != 0
                && statements[..statements.len() - 1]
                    .iter()
                    .copied()
                    .any(contains_return)
            {
                return None;
            }
            last.as_return_statement().expression()?
        } else {
            body
        };
        Some(LazyExpression {
            node,
            expression,
            params,
        })
    }
    pub(crate) fn unwrap_identity_forwarder(&mut self, node: P<Node>) -> IdentityForwarder {
        let node = unwrap_expression(node);
        let fallback = IdentityForwarder {
            target: node,
            type_arguments: Vec::new(),
            parameter: None,
        };
        let Some(lazy) = self.parse_lazy_expression(node, 0) else {
            return fallback;
        };
        if lazy.params.len() != 1 {
            return fallback;
        }
        let parameter = lazy.params[0];
        if parameter.kind() != Kind::Parameter {
            return fallback;
        }
        let p = parameter.as_parameter_declaration();
        if p.name.kind() != Kind::Identifier
            || p.dot_dot_dot_token().is_some()
            || p.initializer().is_some()
        {
            return fallback;
        }
        let Some(call) = checked_call(lazy.expression) else {
            return fallback;
        };
        let c = call.as_call_expression();
        if c.arguments.nodes().len() != 1 {
            return fallback;
        }
        let argument = unwrap_expression(c.arguments.nodes()[0]);
        if argument.kind() != Kind::Identifier || !self.same_reference(p.name, argument) {
            return fallback;
        }
        IdentityForwarder {
            target: unwrap_expression(c.expression),
            type_arguments: type_arguments(call),
            parameter: Some(parameter),
        }
    }
    pub(crate) fn same_reference(&mut self, left: P<Node>, right: P<Node>) -> bool {
        let left = unwrap_expression(left);
        let right = unwrap_expression(right);
        if left.kind() != right.kind() {
            return false;
        }
        if left == right {
            return true;
        }
        match left.kind() {
            Kind::Identifier => {
                let a = self.reference_symbol(left);
                let b = self.reference_symbol(right);
                a.is_some() && a == b
            }
            Kind::PropertyAccessExpression => {
                let a = self.reference_symbol(left);
                let b = self.reference_symbol(right);
                a.is_some()
                    && a == b
                    && self.same_reference(
                        left.as_property_access_expression().expression,
                        right.as_property_access_expression().expression,
                    )
            }
            Kind::ThisKeyword | Kind::SuperKeyword => true,
            _ => false,
        }
    }
    pub(crate) fn is_expression_value_stable_at_location(
        &mut self,
        expression: P<Node>,
        location: P<Node>,
    ) -> bool {
        let expression = unwrap_expression(expression);
        match expression.kind() {
            Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::NullKeyword => true,
            Kind::Identifier => {
                if self.is_global(expression, "undefined") {
                    return true;
                }
                let Some(symbol) = self.symbol(expression) else {
                    return false;
                };
                let Some(node) = symbol.value_declaration() else {
                    return false;
                };
                if node.kind() != Kind::VariableDeclaration {
                    return false;
                }
                let Some(initializer) = node.as_variable_declaration().initializer() else {
                    return false;
                };
                let Some(parent) = node.parent() else {
                    return false;
                };
                parent.kind() == Kind::VariableDeclarationList
                    && parent.flags().intersects(NodeFlags::Const)
                    && ast::get_source_file_of_node(node) == ast::get_source_file_of_node(location)
                    && initializer.end() <= location.pos()
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DispatchConditionKind {
    Predicate,
    SwitchCase,
}
#[derive(Clone)]
pub(crate) struct DispatchCondition {
    pub kind: DispatchConditionKind,
    pub subject: P<Node>,
    pub value: Option<P<Node>>,
    pub tag_subject: Option<P<Node>>,
    pub tag_value: Option<P<Node>>,
}
#[derive(Clone)]
pub(crate) struct DispatchBranch {
    pub condition: DispatchCondition,
    pub result: P<Node>,
}
#[derive(Clone)]
pub(crate) struct ResultDispatch {
    pub node: P<Node>,
    pub branches: Vec<DispatchBranch>,
    pub fallback: Option<P<Node>>,
}
#[derive(Clone)]
pub(crate) struct ReturningDispatch {
    pub node: P<Node>,
    pub body: P<Node>,
    pub params: Vec<P<Node>>,
    pub dispatch: ResultDispatch,
}
fn condition(
    kind: DispatchConditionKind,
    subject: P<Node>,
    value: Option<P<Node>>,
) -> DispatchCondition {
    DispatchCondition {
        kind,
        subject,
        value,
        tag_subject: None,
        tag_value: None,
    }
}
fn tag_subject(node: P<Node>) -> Option<P<Node>> {
    let node = unwrap_expression(node);
    if node.kind() != Kind::PropertyAccessExpression {
        return None;
    }
    let access = node.as_property_access_expression();
    (access.name.text() == "_tag").then(|| unwrap_expression(access.expression))
}
fn conditional_dispatch(node: P<Node>) -> Option<ResultDispatch> {
    let node = unwrap_expression(node);
    if node.kind() != Kind::ConditionalExpression {
        return None;
    }
    let mut result = ResultDispatch {
        node,
        branches: Vec::new(),
        fallback: None,
    };
    let mut current = node;
    loop {
        let conditional = current.as_conditional_expression();
        if unwrap_expression(conditional.when_true).kind() == Kind::ConditionalExpression {
            return None;
        }
        result.branches.push(DispatchBranch {
            condition: condition(
                DispatchConditionKind::Predicate,
                conditional.condition,
                None,
            ),
            result: conditional.when_true,
        });
        let next = unwrap_expression(conditional.when_false);
        if next.kind() == Kind::ConditionalExpression {
            current = next;
        } else {
            result.fallback = Some(conditional.when_false);
            break;
        }
    }
    Some(result)
}
fn if_dispatch(node: P<Node>) -> Option<ResultDispatch> {
    let mut result = ResultDispatch {
        node,
        branches: Vec::new(),
        fallback: None,
    };
    let mut current = node;
    loop {
        let statement = current.as_if_statement();
        let value = single_return(statement.then_statement)?;
        result.branches.push(DispatchBranch {
            condition: condition(DispatchConditionKind::Predicate, statement.expression, None),
            result: value,
        });
        let Some(next) = statement.else_statement else {
            break;
        };
        if next.kind() == Kind::IfStatement {
            current = next;
        } else {
            result.fallback = Some(single_return(next)?);
            break;
        }
    }
    Some(result)
}
fn block_dispatch(node: P<Node>) -> Option<ResultDispatch> {
    let statements = node.as_block().statements.nodes();
    if statements.is_empty() {
        return None;
    }
    if statements.len() == 1 {
        let statement = statements[0];
        match statement.kind() {
            Kind::ReturnStatement => {
                return conditional_dispatch(statement.as_return_statement().expression()?);
            }
            Kind::IfStatement => return if_dispatch(statement),
            Kind::SwitchStatement => {
                let statement = statement.as_switch_statement();
                let clauses = statement.case_block.as_case_block().clauses.nodes();
                let mut result = ResultDispatch {
                    node,
                    branches: Vec::new(),
                    fallback: None,
                };
                for (i, clause) in clauses.iter().copied().enumerate() {
                    let c = clause.as_case_or_default_clause();
                    let values = c.statements.nodes();
                    if values.len() != 1 {
                        return None;
                    }
                    let value = single_return(values[0])?;
                    if clause.kind() == Kind::DefaultClause {
                        if i + 1 != clauses.len() || result.fallback.is_some() {
                            return None;
                        }
                        result.fallback = Some(value);
                    } else {
                        result.branches.push(DispatchBranch {
                            condition: condition(
                                DispatchConditionKind::SwitchCase,
                                statement.expression,
                                c.expression,
                            ),
                            result: value,
                        });
                    }
                }
                return (!result.branches.is_empty()).then_some(result);
            }
            _ => {}
        }
    }
    let mut result = ResultDispatch {
        node,
        branches: Vec::new(),
        fallback: None,
    };
    let mut end = statements.len();
    if statements[end - 1].kind() == Kind::ReturnStatement {
        result.fallback = Some(statements[end - 1].as_return_statement().expression()?);
        end -= 1;
    }
    if end == 0 {
        return None;
    }
    for statement in &statements[..end] {
        if statement.kind() != Kind::IfStatement {
            return None;
        }
        let statement = statement.as_if_statement();
        if statement.else_statement.is_some() {
            return None;
        }
        result.branches.push(DispatchBranch {
            condition: condition(DispatchConditionKind::Predicate, statement.expression, None),
            result: single_return(statement.then_statement)?,
        });
    }
    Some(result)
}
impl RuleContext<'_> {
    pub(crate) fn parse_tag_match(&mut self, node: P<Node>) -> Option<(P<Node>, P<Node>)> {
        let node = unwrap_expression(node);
        if node.kind() == Kind::BinaryExpression {
            let b = node.as_binary_expression();
            if !matches!(
                b.operator_token.kind(),
                Kind::EqualsEqualsToken | Kind::EqualsEqualsEqualsToken
            ) {
                return None;
            }
            if let Some(subject) = tag_subject(b.left) {
                return Some((subject, unwrap_expression(b.right())));
            }
            if let Some(subject) = tag_subject(b.right()) {
                return Some((subject, unwrap_expression(b.left)));
            }
            return None;
        }
        let call = checked_call(node)?;
        let c = call.as_call_expression();
        if c.arguments.nodes().len() == 2
            && self.is_api(unwrap_expression(c.expression), "Predicate", "isTagged")
        {
            return Some((
                unwrap_expression(c.arguments.nodes()[0]),
                unwrap_expression(c.arguments.nodes()[1]),
            ));
        }
        if c.arguments.nodes().len() == 1 {
            let inner = checked_call(c.expression)?;
            let inner = inner.as_call_expression();
            if inner.arguments.nodes().len() == 1
                && self.is_api(unwrap_expression(inner.expression), "Predicate", "isTagged")
            {
                return Some((
                    unwrap_expression(c.arguments.nodes()[0]),
                    unwrap_expression(inner.arguments.nodes()[0]),
                ));
            }
        }
        None
    }
    pub(crate) fn parse_result_dispatch(&mut self, node: P<Node>) -> Option<ResultDispatch> {
        let original = node;
        let node = unwrap_expression(node);
        let mut result = match node.kind() {
            Kind::Block => block_dispatch(node),
            Kind::ConditionalExpression => conditional_dispatch(node),
            _ => None,
        }?;
        result.node = original;
        for branch in &mut result.branches {
            let condition = &mut branch.condition;
            let tag = match condition.kind {
                DispatchConditionKind::Predicate => self.parse_tag_match(condition.subject),
                DispatchConditionKind::SwitchCase => {
                    tag_subject(condition.subject).zip(condition.value)
                }
            };
            if let Some((subject, value)) = tag {
                condition.tag_subject = Some(subject);
                condition.tag_value = Some(value);
            }
        }
        Some(result)
    }
    pub(crate) fn parse_returning_dispatch(&mut self, node: P<Node>) -> Option<ReturningDispatch> {
        let node = unwrap_expression(node);
        let (body, params) = function_parts(node)?;
        let dispatch = self.parse_result_dispatch(body)?;
        Some(ReturningDispatch {
            node,
            body,
            params,
            dispatch,
        })
    }
    pub(crate) fn common_tag_subject(&mut self, dispatch: &ResultDispatch) -> Option<P<Node>> {
        let first = &dispatch.branches.first()?.condition;
        let subject = first.tag_subject?;
        first.tag_value?;
        for branch in &dispatch.branches[1..] {
            branch.condition.tag_value?;
            if !self.same_reference(subject, branch.condition.tag_subject?) {
                return None;
            }
        }
        Some(subject)
    }
}
