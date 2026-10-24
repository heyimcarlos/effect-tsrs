use tsrs_ast::{self as ast, Kind, ModifierFlags, Node};
use tsrs_core::P;

use super::{RuleContext, walk};
use crate::Rule;

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    let floating = ctx.enabled(Rule::FloatingEffect);
    let asynchronous = ctx.enabled(Rule::AsyncFunction);
    let unnecessary_pipe = ctx.enabled(Rule::UnnecessaryPipe);
    if !floating && !asynchronous && !unnecessary_pipe {
        return;
    }
    walk(ctx.file.as_node(), &mut |node| {
        if floating && node.kind() == Kind::ExpressionStatement {
            check_floating(ctx, node.as_expression_statement().expression());
        }
        if asynchronous
            && matches!(
                node.kind(),
                Kind::FunctionDeclaration
                    | Kind::FunctionExpression
                    | Kind::ArrowFunction
                    | Kind::MethodDeclaration
            )
            && ast::get_combined_modifier_flags(node).intersects(ModifierFlags::Async)
        {
            ctx.emit(Rule::AsyncFunction, node, 377081, &[]);
        }
        if unnecessary_pipe && node.kind() == Kind::CallExpression && is_unnecessary_pipe(ctx, node)
        {
            ctx.emit(Rule::UnnecessaryPipe, node, 377013, &[]);
        }
    });
}

fn check_floating(ctx: &mut RuleContext<'_>, expression: P<Node>) {
    if expression.kind() == Kind::BinaryExpression
        && matches!(
            expression.as_binary_expression().operator_token().kind(),
            Kind::EqualsToken
                | Kind::QuestionQuestionEqualsToken
                | Kind::AmpersandAmpersandEqualsToken
                | Kind::BarBarEqualsToken
        )
    {
        return;
    }
    if ctx.cannot_be_effect_type(expression) {
        return;
    }
    let Some(ty) = ctx.safe_ty(expression) else {
        return;
    };
    let has_effect_id = if ctx.detected_effect_version == 4 {
        ctx.has_property(ty, "~effect/Effect")
    } else {
        ctx.effect_type(ty).is_some()
    };
    if has_effect_id {
        if ctx.effect_type(ty).is_none() {
            return;
        }
        if (ctx.has_property(ty, "await") && ctx.has_property(ty, "poll"))
            || ctx.has_property(ty, "_tag")
            || ctx.has_property(ty, "get")
        {
            return;
        }
    } else if ctx.stream_type(ty).is_none() {
        return;
    }
    if ctx.strict_effect_type(ty).is_some() {
        ctx.emit(Rule::FloatingEffect, expression, 377001, &[]);
    } else {
        let name = ctx.type_string(ty);
        ctx.emit(Rule::FloatingEffect, expression, 377058, &[name]);
    }
}

fn is_unnecessary_pipe(ctx: &mut RuleContext<'_>, node: P<Node>) -> bool {
    let call = node.as_call_expression();
    let callee = call.expression();
    let argument_count = call.arguments().nodes().len();
    match callee.kind() {
        Kind::PropertyAccessExpression => {
            if callee.as_property_access_expression().name().text() != "pipe" || argument_count > 1
            {
                return false;
            }
            if ctx.is_package_api(callee, "effect", "pipe") {
                argument_count == 1
            } else {
                argument_count == 0
            }
        }
        Kind::Identifier => argument_count == 1 && ctx.is_package_api(callee, "effect", "pipe"),
        _ => false,
    }
}
