// Ported from tsc/internal/transformers/inliners/constenum.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `ConstEnumInliningTransformer` — replaces property/element accesses on
// const enum members with their constant values (skipped under
// `isolatedModules`).
//
// PORT notes:
//   - The Go transformer struct embeds `transformers.Transformer` and holds
//     `emitResolver`; here the resolver arrives as `Rc<RefCell<dyn
//     EmitResolver>>` from `TransformOptions` and the `EmitContext` is the
//     shared `Rc<RefCell<EmitContext>>` (see crate docs).
//   - `*ast.Node` → `NodeId`; nil → `Option<NodeId>`; `any` constant values
//     → `tsc_evaluator::Value`.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_core::options_generated::CompilerOptions;
use tsc_debug as debug;
use tsc_evaluator::Value;
use tsc_printer::EmitResolver;
use tsc_scanner::utilities::get_text_of_node;

use crate::chain::TransformOptions;
use crate::estransforms::{Ec, make_transformer, visit_each_child};
use crate::transformer::Transformer;

/// `NewConstEnumInliningTransformer`.
pub fn new_const_enum_inlining_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let compiler_options = opts
        .compiler_options
        .expect("constEnumInliningTransformer requires compiler options");
    if compiler_options.get_isolated_modules() {
        debug::fail("const enums are not inlined under isolated modules");
    }
    let emit_resolver = opts
        .emit_resolver
        .clone()
        .expect("constEnumInliningTransformer requires an emit resolver");
    make_transformer(opts, move |ec| {
        let emit_resolver = emit_resolver.clone();
        let ec2 = ec.clone();
        Box::new(move |v, cx, node| visit(&ec2, compiler_options, &emit_resolver, v, cx, node))
    })
}

/// `(tx *ConstEnumInliningTransformer) visit`.
fn visit<'a>(
    ec: &Ec,
    compiler_options: &CompilerOptions,
    emit_resolver: &Rc<RefCell<dyn EmitResolver + 'a>>,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    match cx.nodes[node].kind {
        Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
            let parse = ec.borrow().parse_node(cx.nodes, node);
            let Some(parse) = parse else {
                return Some(visit_each_child(v, cx, node));
            };
            let value = emit_resolver.borrow().get_constant_value(parse, cx.nodes);
            let Some(value) = value else {
                return Some(visit_each_child(v, cx, node));
            };
            let mut replacement: Option<NodeId> = None;
            match value {
                Value::Number(n) => {
                    if n.is_inf() {
                        if n.abs() == n {
                            replacement =
                                Some(ec.borrow_mut().factory.new_identifier(cx.nodes, "Infinity"));
                        } else {
                            let inner =
                                ec.borrow_mut().factory.new_identifier(cx.nodes, "Infinity");
                            replacement =
                                Some(ec.borrow_mut().factory.new_prefix_unary_expression(
                                    cx.nodes,
                                    Kind::MinusToken,
                                    Some(inner),
                                ));
                        }
                    } else if n.is_nan() {
                        replacement = Some(ec.borrow_mut().factory.new_identifier(cx.nodes, "NaN"));
                    } else if n.abs() == n {
                        replacement = Some(ec.borrow_mut().factory.new_numeric_literal(
                            cx.nodes,
                            &n.string(),
                            ast::TokenFlags::NONE,
                        ));
                    } else {
                        let lit = ec.borrow_mut().factory.new_numeric_literal(
                            cx.nodes,
                            &n.abs().string(),
                            ast::TokenFlags::NONE,
                        );
                        replacement = Some(ec.borrow_mut().factory.new_prefix_unary_expression(
                            cx.nodes,
                            Kind::MinusToken,
                            Some(lit),
                        ));
                    }
                }
                Value::String(s) => {
                    replacement = Some(ec.borrow_mut().factory.new_string_literal(
                        cx.nodes,
                        &s,
                        ast::TokenFlags::NONE,
                    ));
                }
                // technically not supported by strada, and issues a checker
                // error, handled here for completeness
                Value::PseudoBigInt(b) => {
                    if b == Default::default() {
                        replacement = Some(ec.borrow_mut().factory.new_big_int_literal(
                            cx.nodes,
                            "0",
                            ast::TokenFlags::NONE,
                        ));
                    } else if !b.negative {
                        replacement = Some(ec.borrow_mut().factory.new_big_int_literal(
                            cx.nodes,
                            &b.base10_value,
                            ast::TokenFlags::NONE,
                        ));
                    } else {
                        let lit = ec.borrow_mut().factory.new_big_int_literal(
                            cx.nodes,
                            &b.base10_value,
                            ast::TokenFlags::NONE,
                        );
                        replacement = Some(ec.borrow_mut().factory.new_prefix_unary_expression(
                            cx.nodes,
                            Kind::MinusToken,
                            Some(lit),
                        ));
                    }
                }
                // Go leaves `replacement` nil for `bool` values and returns it;
                // `nil` maps to `None` (the node is elided).
                Value::Bool(_) => {}
            }

            if compiler_options.remove_comments.is_false_or_unknown()
                && let Some(replacement) = replacement
            {
                let original = ec.borrow().most_original(Some(node));
                if let Some(original) = original
                    && !ast::node_is_synthesized(&cx.nodes[original])
                {
                    let original_text = get_text_of_node(original, cx.nodes);
                    let escaped_text = safe_multi_line_comment(&original_text);
                    ec.borrow().add_synthetic_trailing_comment(
                        replacement,
                        Kind::MultiLineCommentTrivia,
                        &escaped_text,
                        false,
                    );
                }
            }
            replacement
        }
        _ => Some(visit_each_child(v, cx, node)),
    }
}

/// `safeMultiLineComment`.
fn safe_multi_line_comment(text: &str) -> String {
    let mut b = String::with_capacity(text.len() + 2);
    b.push(' ');
    let mut text = text;
    loop {
        let Some(i) = text.find("*/") else {
            break;
        };
        b.push_str(&text[..i]);
        b.push_str("*_/");
        text = &text[i + 2..];
    }
    b.push_str(text);
    b.push(' ');
    b
}
