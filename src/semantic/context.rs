use tsrs_ast::{self as ast, Kind, Node};
use tsrs_core::P;

use super::ContextInfo;
use crate::rules::RuleContext;

const CAN_YIELD: u8 = 1;
const IN_THUNK: u8 = 2;
const PENDING_FUNCTION: u8 = 4;
const PENDING_TRY_PROPERTY: u8 = 8;
const PENDING: u8 = PENDING_FUNCTION | PENDING_TRY_PROPERTY;

#[derive(Clone)]
pub(crate) struct ParsedFn {
    pub function: P<Node>,
    pub pipe_arguments: Vec<P<Node>>,
    pub untraced: bool,
}

#[derive(Clone, Copy)]
struct Registration {
    node: P<Node>,
    enable: u8,
    disable: u8,
    generator: Option<P<Node>>,
    sets_generator: bool,
}

fn register(registrations: &mut Vec<Registration>, node: P<Node>, enable: u8, disable: u8) {
    registrations.push(Registration {
        node,
        enable,
        disable,
        generator: None,
        sets_generator: false,
    });
}

fn split_arguments(args: &[P<Node>]) -> Option<(P<Node>, Vec<P<Node>>)> {
    let first = *args.first()?;
    let start = usize::from(!matches!(
        first.kind(),
        Kind::ArrowFunction | Kind::FunctionExpression
    ));
    args.iter()
        .enumerate()
        .skip(start)
        .find_map(|(index, &node)| {
            matches!(node.kind(), Kind::ArrowFunction | Kind::FunctionExpression)
                .then(|| (node, args[index + 1..].to_vec()))
        })
}

impl RuleContext<'_> {
    pub(crate) fn gen_function(&mut self, node: P<Node>) -> Option<P<Node>> {
        if let Some(&result) = self.semantic.gen_functions.get(&node) {
            return result;
        }
        let result = if node.kind() == Kind::CallExpression {
            let call = node.as_call_expression();
            split_arguments(call.arguments().nodes()).and_then(|(function, _)| {
                (function.kind() == Kind::FunctionExpression
                    && function.as_function_expression().asterisk_token().is_some()
                    && self.is_api(call.expression(), "Effect", "gen"))
                .then_some(function)
            })
        } else {
            None
        };
        self.semantic.gen_functions.insert(node, result);
        result
    }

    pub(crate) fn parsed_fn(&mut self, node: P<Node>) -> Option<ParsedFn> {
        if node.kind() != Kind::CallExpression {
            return None;
        }
        let call = node.as_call_expression();
        let (function, pipe_arguments) = split_arguments(call.arguments().nodes())?;
        let callee = call.expression();
        let (target, trace) = if callee.kind() == Kind::CallExpression {
            let inner = callee.as_call_expression();
            (
                inner.expression(),
                inner.arguments().nodes().first().copied(),
            )
        } else {
            (callee, None)
        };
        let variant = if self.is_api(target, "Effect", "fn") {
            "fn"
        } else if trace.is_none() && self.is_api(target, "Effect", "fnUntraced") {
            "fnUntraced"
        } else if trace.is_none() && self.is_api(target, "Effect", "fnUntracedEager") {
            "fnUntracedEager"
        } else {
            return None;
        };
        Some(ParsedFn {
            function,
            pipe_arguments,
            untraced: variant != "fn",
        })
    }

    pub(crate) fn effect_context(&mut self, node: P<Node>) -> u8 {
        self.ensure_context(node);
        self.semantic
            .contexts
            .get(&node)
            .map_or(0, |info| info.flags)
    }

    pub(crate) fn yield_generator(&mut self, node: P<Node>) -> Option<P<Node>> {
        self.ensure_context(node);
        self.semantic
            .contexts
            .get(&node)
            .and_then(|info| info.generator)
    }

    fn ensure_context(&mut self, node: P<Node>) {
        let Some(file) = ast::get_source_file_of_node(node) else {
            return;
        };
        if self.semantic.context_files.contains_key(&file) {
            return;
        }
        self.semantic.context_files.insert(file, true);
        self.walk_context(file.as_node(), ContextInfo::default(), 0, &mut Vec::new());
    }

    fn walk_context(
        &mut self,
        node: P<Node>,
        parent: ContextInfo,
        parent_disable: u8,
        registrations: &mut Vec<Registration>,
    ) {
        let registration_count = registrations.len();
        let mut info = parent;
        let mut disable = parent_disable;
        let mut enable = 0;
        for registration in registrations.iter() {
            if registration.node == node {
                disable |= registration.disable;
                enable |= registration.enable;
                if registration.sets_generator {
                    info.generator = registration.generator;
                }
            }
        }
        info.flags = (info.flags & !disable) | enable;
        let mut children_disable = 0;

        if info.flags & PENDING_FUNCTION != 0
            && matches!(node.kind(), Kind::ArrowFunction | Kind::FunctionExpression)
        {
            if let Some(body) = node.body() {
                register(registrations, body, IN_THUNK, PENDING);
            }
        } else if info.flags & PENDING_TRY_PROPERTY != 0
            && node.kind() == Kind::ObjectLiteralExpression
        {
            children_disable |= PENDING;
            for &property in node.as_object_literal_expression().properties().nodes() {
                if property.kind() != Kind::PropertyAssignment {
                    continue;
                }
                if property.name().is_some_and(|name| name.text() == "try") {
                    let value = property.as_property_assignment().initializer();
                    register(registrations, value, PENDING_FUNCTION, 0);
                }
            }
        } else if matches!(
            node.kind(),
            Kind::ParenthesizedExpression
                | Kind::SatisfiesExpression
                | Kind::AsExpression
                | Kind::NonNullExpression
                | Kind::TypeAssertionExpression
        ) {
            if let Some(expression) = node.expression() {
                register(registrations, expression, info.flags & PENDING, 0);
            }
        } else if info.flags & PENDING != 0 {
            children_disable |= PENDING;
        }

        let generator = self.gen_function(node).or_else(|| {
            self.parsed_fn(node).and_then(|parsed| {
                (parsed.function.kind() == Kind::FunctionExpression
                    && parsed
                        .function
                        .as_function_expression()
                        .asterisk_token()
                        .is_some())
                .then_some(parsed.function)
            })
        });
        if let Some(generator) = generator
            && let Some(body) = generator.body()
        {
            registrations.push(Registration {
                node: body,
                enable: CAN_YIELD,
                disable: 0,
                generator: Some(generator),
                sets_generator: true,
            });
        }

        if node.kind() == Kind::CallExpression {
            let call = node.as_call_expression();
            if let Some(&argument) = call.arguments().nodes().first() {
                let target = call.expression();
                if ["sync", "promise", "callback", "suspend"]
                    .iter()
                    .any(|api| self.is_api(target, "Effect", api))
                {
                    register(registrations, argument, PENDING_FUNCTION, 0);
                } else if ["try", "tryPromise"]
                    .iter()
                    .any(|api| self.is_api(target, "Effect", api))
                {
                    register(registrations, argument, PENDING, 0);
                }
            }
        }
        if ast::is_function_like(node) {
            children_disable |= CAN_YIELD | IN_THUNK | PENDING;
        }
        if info.flags & CAN_YIELD == 0 {
            info.generator = None;
        }
        self.semantic.contexts.insert(
            node,
            ContextInfo {
                flags: info.flags & (CAN_YIELD | IN_THUNK),
                generator: info.generator,
            },
        );
        node.for_each_child(&mut |child| {
            self.walk_context(child, info, children_disable, registrations);
            false
        });
        registrations.truncate(registration_count);
    }
}
