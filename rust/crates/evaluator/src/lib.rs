// Ported from tsc/internal/evaluator/evaluator.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Compile-time constant expression evaluator.

use tsc_ast::utilities::{
    OuterExpressionKinds, is_entity_name_expression, outer_expression_kinds, skip_outer_expressions,
};
use tsc_ast::{Kind, Node, NodeId};
use tsc_core::core::if_else;
use tsc_jsnum::{Number, PseudoBigInt, from_string};

/// The dynamic value stored in `Result::value`, mirroring the Go `any` field,
/// which holds `string | jsnum.Number | bool | jsnum.PseudoBigInt | nil`.
/// Go `nil` maps to `Option<Value>::None` on `Result::value`.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    String(String),
    Number(Number),
    Bool(bool),
    PseudoBigInt(PseudoBigInt),
}

/// `type Result struct`.
#[derive(Clone, Debug, Default)]
pub struct Result {
    /// `Value any` — `None` mirrors Go `nil`.
    pub value: Option<Value>,
    pub is_syntactically_string: bool,
    pub resolved_other_files: bool,
    pub has_external_references: bool,
}

/// `NewResult(value, isSyntacticallyString, resolvedOtherFiles, hasExternalReferences)`.
pub fn new_result(
    value: Option<Value>,
    is_syntactically_string: bool,
    resolved_other_files: bool,
    has_external_references: bool,
) -> Result {
    Result {
        value,
        is_syntactically_string,
        resolved_other_files,
        has_external_references,
    }
}

/// `type Evaluator func(expr *ast.Node, location *ast.Node) Result`.
///
/// PORT: the Go func value becomes a boxed closure trait object. `*ast.Node`
/// → `NodeId` plus the owning `nodes` arena; `location` is `Option<NodeId>`
/// since Go callers pass nil.
pub type Evaluator<'a> = dyn FnMut(NodeId, Option<NodeId>, &[Node]) -> Result + 'a;

/// `NewEvaluator(evaluateEntity, outerExpressionsToSkip)`.
pub fn new_evaluator<'a, F>(
    evaluate_entity: F,
    outer_expressions_to_skip: OuterExpressionKinds,
) -> Box<Evaluator<'a>>
where
    F: FnMut(NodeId, Option<NodeId>, &[Node]) -> Result + 'a,
{
    let mut evaluator = EvaluatorImpl {
        evaluate_entity,
        outer_expressions_to_skip,
    };
    Box::new(
        move |expr: NodeId, location: Option<NodeId>, nodes: &[Node]| {
            evaluator.evaluate(expr, location, nodes)
        },
    )
}

/// The state captured by the `evaluate` closure Go assembles inside
/// `NewEvaluator`; recursion becomes a method call on `self`.
struct EvaluatorImpl<F> {
    evaluate_entity: F,
    outer_expressions_to_skip: OuterExpressionKinds,
}

impl<F> EvaluatorImpl<F>
where
    F: FnMut(NodeId, Option<NodeId>, &[Node]) -> Result,
{
    /// The `evaluate` closure body inside `NewEvaluator`.
    fn evaluate(&mut self, expr: NodeId, location: Option<NodeId>, nodes: &[Node]) -> Result {
        let mut is_syntactically_string = false;
        let mut resolved_other_files = false;
        let mut has_external_references = false;
        // It's unclear when/whether we should consider skipping other kinds of outer expressions.
        // Type assertions intentionally break evaluation when evaluating literal types, such as:
        //     type T = `one ${"two" as any} three`; // string
        // But it's less clear whether such an assertion should break enum member evaluation:
        //     enum E {
        //       A = "one" as any
        //     }
        // SatisfiesExpressions and non-null assertions seem to have even less reason to break
        // emitting enum members as literals. However, these expressions also break Babel's
        // evaluation (but not esbuild's), and the isolatedModules errors we give depend on
        // our evaluation results, so we're currently being conservative so as to issue errors
        // on code that might break Babel.
        let expr = skip_outer_expressions(
            expr,
            self.outer_expressions_to_skip | outer_expression_kinds::PARENTHESES,
            nodes,
        );
        match nodes[expr].kind {
            Kind::PrefixUnaryExpression => {
                let unary = nodes[expr].as_prefix_unary_expression();
                let result = self.evaluate(unary.operand.unwrap(), location, nodes);
                resolved_other_files = result.resolved_other_files;
                has_external_references = result.has_external_references;
                // `if value, ok := result.Value.(jsnum.Number); ok`
                if let Some(Value::Number(value)) = result.value {
                    let evaluated = match unary.operator {
                        Kind::PlusToken => Some(value),
                        Kind::MinusToken => Some(-value),
                        Kind::TildeToken => Some(value.bitwise_not()),
                        _ => None,
                    };
                    if let Some(value) = evaluated {
                        return Result {
                            value: Some(Value::Number(value)),
                            is_syntactically_string,
                            resolved_other_files,
                            has_external_references,
                        };
                    }
                }
            }
            Kind::BinaryExpression => {
                let binary = nodes[expr].as_binary_expression();
                let left = self.evaluate(binary.left.unwrap(), location, nodes);
                let right = self.evaluate(binary.right.unwrap(), location, nodes);
                let operator = nodes[binary.operator_token.unwrap()].kind;
                is_syntactically_string = (left.is_syntactically_string
                    || right.is_syntactically_string)
                    && operator == Kind::PlusToken;
                resolved_other_files = left.resolved_other_files || right.resolved_other_files;
                has_external_references =
                    left.has_external_references || right.has_external_references;
                // `leftNum, leftIsNum := left.Value.(jsnum.Number)` etc.
                let left_num = match &left.value {
                    Some(Value::Number(n)) => Some(*n),
                    _ => None,
                };
                let right_num = match &right.value {
                    Some(Value::Number(n)) => Some(*n),
                    _ => None,
                };
                if let (Some(left_num), Some(right_num)) = (left_num, right_num) {
                    let evaluated = match operator {
                        Kind::BarToken => Some(left_num.bitwise_or(right_num)),
                        Kind::AmpersandToken => Some(left_num.bitwise_and(right_num)),
                        Kind::GreaterThanGreaterThanToken => {
                            Some(left_num.signed_right_shift(right_num))
                        }
                        Kind::GreaterThanGreaterThanGreaterThanToken => {
                            Some(left_num.unsigned_right_shift(right_num))
                        }
                        Kind::LessThanLessThanToken => Some(left_num.left_shift(right_num)),
                        Kind::CaretToken => Some(left_num.bitwise_xor(right_num)),
                        Kind::AsteriskToken => Some(left_num * right_num),
                        Kind::SlashToken => Some(left_num / right_num),
                        Kind::PlusToken => Some(left_num + right_num),
                        Kind::MinusToken => Some(left_num - right_num),
                        Kind::PercentToken => Some(left_num.remainder(right_num)),
                        Kind::AsteriskAsteriskToken => Some(left_num.exponentiate(right_num)),
                        _ => None,
                    };
                    if let Some(value) = evaluated {
                        return Result {
                            value: Some(Value::Number(value)),
                            is_syntactically_string,
                            resolved_other_files,
                            has_external_references,
                        };
                    }
                }
                // `leftStr, leftIsStr := left.Value.(string)` etc., followed by
                // the `+` string-concatenation path.
                let left_str = match &left.value {
                    Some(Value::String(s)) => Some(s.clone()),
                    _ => None,
                };
                let right_str = match &right.value {
                    Some(Value::String(s)) => Some(s.clone()),
                    _ => None,
                };
                if (left_str.is_some() || left_num.is_some())
                    && (right_str.is_some() || right_num.is_some())
                    && operator == Kind::PlusToken
                {
                    // PORT: `leftIsNum`/`rightIsNum` imply `leftNum`/`rightNum`
                    // are `Some` here, so the `unwrap`s can't fail.
                    let left_str = left_str.unwrap_or_else(|| left_num.unwrap().string());
                    let right_str = right_str.unwrap_or_else(|| right_num.unwrap().string());
                    return Result {
                        value: Some(Value::String(left_str + &right_str)),
                        is_syntactically_string,
                        resolved_other_files,
                        has_external_references,
                    };
                }
            }
            Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral => {
                return Result {
                    value: Some(Value::String(nodes[expr].text(nodes).into_owned())),
                    is_syntactically_string: true,
                    resolved_other_files: false,
                    has_external_references: false,
                };
            }
            Kind::TemplateExpression => {
                return self.evaluate_template_expression(&nodes[expr], location, nodes);
            }
            Kind::NumericLiteral => {
                return Result {
                    value: Some(Value::Number(from_string(&nodes[expr].text(nodes)))),
                    is_syntactically_string: false,
                    resolved_other_files: false,
                    has_external_references: false,
                };
            }
            Kind::Identifier => {
                return (self.evaluate_entity)(expr, location, nodes);
            }
            Kind::ElementAccessExpression | Kind::PropertyAccessExpression => {
                if is_entity_name_expression(&nodes[nodes[expr].expression().unwrap()], nodes) {
                    return (self.evaluate_entity)(expr, location, nodes);
                }
            }
            _ => {}
        }
        Result {
            value: None,
            is_syntactically_string,
            resolved_other_files,
            has_external_references,
        }
    }

    /// `evaluateTemplateExpression(expr, location, evaluate)` — folded into a
    /// method so it can share the captured `evaluate` closure via `self`.
    fn evaluate_template_expression(
        &mut self,
        expr: &Node,
        location: Option<NodeId>,
        nodes: &[Node],
    ) -> Result {
        let template = expr.as_template_expression();
        // Go: `strings.Builder`.
        let mut sb = String::new();
        sb.push_str(&nodes[template.head.unwrap()].text(nodes));
        let mut resolved_other_files = false;
        let mut has_external_references = false;
        // `expr.AsTemplateExpression().TemplateSpans.Nodes` — always present on
        // a well-formed TemplateExpression; Go would nil-deref otherwise.
        for &span_id in template.template_spans.as_ref().unwrap().nodes() {
            let span = &nodes[span_id];
            let span_result = self.evaluate(span.expression().unwrap(), location, nodes);
            // `if spanResult.Value == nil`
            let Some(value) = &span_result.value else {
                return Result {
                    value: None,
                    is_syntactically_string: true,
                    resolved_other_files: false,
                    has_external_references: false,
                };
            };
            sb.push_str(&any_to_string(value));
            sb.push_str(&nodes[span.as_template_span().literal.unwrap()].text(nodes));
            resolved_other_files = resolved_other_files || span_result.resolved_other_files;
            has_external_references =
                has_external_references || span_result.has_external_references;
        }
        Result {
            value: Some(Value::String(sb)),
            is_syntactically_string: true,
            resolved_other_files,
            has_external_references,
        }
    }
}

/// `AnyToString(v)`.
///
/// PORT: Go's `panic("Unhandled case in AnyToString")` is unrepresentable —
/// `Value` enumerates exactly the variants Go's type switch accepts.
pub fn any_to_string(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.string(),
        Value::Bool(b) => if_else(*b, "true", "false").to_string(),
        Value::PseudoBigInt(b) => b.string(),
    }
}

/// `IsTruthy(v)`.
///
/// PORT: see `any_to_string` — `Value` covers every Go type-switch case.
pub fn is_truthy(v: &Value) -> bool {
    match v {
        Value::String(s) => !s.is_empty(),
        Value::Number(n) => *n != 0.0 && !n.is_nan(),
        Value::Bool(b) => *b,
        // `v != jsnum.PseudoBigInt{}` — the zero PseudoBigInt is the value 0.
        Value::PseudoBigInt(b) => *b != PseudoBigInt::default(),
    }
}
