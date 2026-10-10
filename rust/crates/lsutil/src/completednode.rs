// Ported from tsc/internal/ls/lsutil/completednode.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.

use tsc_ast::ast::Node;
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_astnav::tokens::find_child_of_kind;
use tsc_core::core::last_or_nil;
use tsc_core::text::TextPos;

use crate::children::{get_last_visited_child, ls_scanner};

/// `PositionBelongsToNode` returns true if the position belongs to the node.
/// Assumes `candidate.Pos() <= position` holds.
pub fn position_belongs_to_node(
    nodes: &mut Vec<Node>,
    candidate: NodeId,
    position: TextPos,
    file: NodeId,
) -> bool {
    if nodes[candidate].pos() > position {
        panic!("Expected candidate.pos <= position");
    }
    position < nodes[candidate].end() || !is_completed_node(nodes, Some(candidate), file)
}

/// `IsCompletedNode`.
pub fn is_completed_node(nodes: &mut Vec<Node>, n: Option<NodeId>, source_file: NodeId) -> bool {
    let Some(n) = n else {
        return false;
    };
    if ast::node_is_missing(Some(n), nodes) {
        return false;
    }

    match nodes[n].kind {
        Kind::ClassDeclaration
        | Kind::InterfaceDeclaration
        | Kind::EnumDeclaration
        | Kind::ObjectLiteralExpression
        | Kind::ObjectBindingPattern
        | Kind::TypeLiteral
        | Kind::Block
        | Kind::ModuleBlock
        | Kind::CaseBlock
        | Kind::NamedImports
        | Kind::NamedExports => node_ends_with(nodes, n, Kind::CloseBraceToken, source_file),

        Kind::CatchClause => {
            let block = nodes[n].as_catch_clause().block;
            is_completed_node(nodes, block, source_file)
        }

        Kind::NewExpression => {
            if nodes[n].argument_list().is_none() {
                return true;
            }
            // fallthrough
            node_ends_with(nodes, n, Kind::CloseParenToken, source_file)
        }

        Kind::CallExpression | Kind::ParenthesizedExpression | Kind::ParenthesizedType => {
            node_ends_with(nodes, n, Kind::CloseParenToken, source_file)
        }

        Kind::FunctionType | Kind::ConstructorType => {
            let type_ = nodes[n].type_();
            is_completed_node(nodes, type_, source_file)
        }

        Kind::Constructor
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::ConstructSignature
        | Kind::CallSignature
        | Kind::ArrowFunction => {
            if let Some(body) = nodes[n].body() {
                return is_completed_node(nodes, Some(body), source_file);
            }
            if let Some(t) = nodes[n].type_() {
                return is_completed_node(nodes, Some(t), source_file);
            }
            // Even though type parameters can be unclosed, we can get away with
            // having at least a closing paren.
            has_child_of_kind(nodes, n, Kind::CloseParenToken, source_file)
        }

        Kind::ModuleDeclaration => {
            let body = nodes[n].body();
            body.is_some() && is_completed_node(nodes, body, source_file)
        }

        Kind::IfStatement => {
            let else_statement = nodes[n].as_if_statement().else_statement;
            let then_statement = nodes[n].as_if_statement().then_statement;
            if else_statement.is_some() {
                return is_completed_node(nodes, else_statement, source_file);
            }
            is_completed_node(nodes, then_statement, source_file)
        }

        Kind::ExpressionStatement => {
            let expression = nodes[n].expression();
            is_completed_node(nodes, expression, source_file)
                || has_child_of_kind(nodes, n, Kind::SemicolonToken, source_file)
        }

        Kind::ArrayLiteralExpression
        | Kind::ArrayBindingPattern
        | Kind::ElementAccessExpression
        | Kind::ComputedPropertyName
        | Kind::TupleType => node_ends_with(nodes, n, Kind::CloseBracketToken, source_file),

        Kind::IndexSignature => {
            let t = nodes[n].type_();
            if t.is_some() {
                return is_completed_node(nodes, t, source_file);
            }
            has_child_of_kind(nodes, n, Kind::CloseBracketToken, source_file)
        }

        Kind::CaseClause | Kind::DefaultClause => {
            // there is no such thing as terminator token for CaseClause/DefaultClause so for simplicity always consider them non-completed
            false
        }

        Kind::ForStatement | Kind::ForInStatement | Kind::ForOfStatement | Kind::WhileStatement => {
            let statement = nodes[n].statement();
            is_completed_node(nodes, statement, source_file)
        }
        Kind::DoStatement => {
            // rough approximation: if DoStatement has While keyword - then if node is completed is checking the presence of ')';
            if has_child_of_kind(nodes, n, Kind::WhileKeyword, source_file) {
                return node_ends_with(nodes, n, Kind::CloseParenToken, source_file);
            }
            let statement = nodes[n].statement();
            is_completed_node(nodes, statement, source_file)
        }

        Kind::TypeQuery => {
            let expr_name = nodes[n].as_type_query_node().expr_name;
            is_completed_node(nodes, expr_name, source_file)
        }

        Kind::TypeOfExpression
        | Kind::DeleteExpression
        | Kind::VoidExpression
        | Kind::YieldExpression
        | Kind::SpreadElement => {
            let expression = nodes[n].expression();
            is_completed_node(nodes, expression, source_file)
        }

        Kind::TaggedTemplateExpression => {
            let template = nodes[n].as_tagged_template_expression().template;
            is_completed_node(nodes, template, source_file)
        }

        Kind::TemplateExpression => {
            let Some(template_spans) = nodes[n].as_template_expression().template_spans.clone()
            else {
                return false;
            };
            let last_span = last_or_nil(&template_spans.nodes);
            is_completed_node(nodes, last_span, source_file)
        }

        Kind::TemplateSpan => ast::node_is_present(nodes[n].as_template_span().literal, nodes),

        Kind::ExportDeclaration | Kind::ImportDeclaration => {
            ast::node_is_present(nodes[n].module_specifier(), nodes)
        }

        Kind::PrefixUnaryExpression => {
            let operand = nodes[n].as_prefix_unary_expression().operand;
            is_completed_node(nodes, operand, source_file)
        }

        Kind::BinaryExpression => {
            let right = nodes[n].as_binary_expression().right;
            is_completed_node(nodes, right, source_file)
        }

        Kind::ConditionalExpression => {
            let when_false = nodes[n].as_conditional_expression().when_false;
            is_completed_node(nodes, when_false, source_file)
        }

        _ => true,
    }
}

/// Checks if node ends with `expectedLastToken`.
/// If child at position `length - 1` is `SemicolonToken` it is skipped and
/// `expectedLastToken` is compared with child at position `length - 2`.
fn node_ends_with(
    nodes: &mut Vec<Node>,
    n: NodeId,
    expected_last_token: Kind,
    source_file: NodeId,
) -> bool {
    let last_child_node = get_last_visited_child(nodes, n, source_file);
    let mut last_node_and_tokens: Vec<NodeId> = Vec::new();
    let token_start_pos = if let Some(last_child_node) = last_child_node {
        last_node_and_tokens.push(last_child_node);
        nodes[last_child_node].end()
    } else {
        nodes[n].pos()
    };
    let text = nodes[source_file].as_source_file().text.clone();
    let language_variant = nodes[source_file].as_source_file().language_variant;
    let mut scan = ls_scanner(&text, language_variant, token_start_pos);
    let mut start_pos = token_start_pos;
    while start_pos < nodes[n].end() {
        let token_kind = scan.token();
        let token_full_start = scan.token_full_start() as TextPos;
        let token_end = scan.token_end() as TextPos;
        let flags = scan.token_flags();
        let token = ast::get_or_create_token(
            nodes,
            source_file,
            token_kind,
            token_full_start,
            token_end,
            n,
            flags,
        );
        last_node_and_tokens.push(token);
        start_pos = token_end;
        scan.scan();
    }
    if last_node_and_tokens.is_empty() {
        return false;
    }
    let last_child = last_node_and_tokens[last_node_and_tokens.len() - 1];
    if nodes[last_child].kind == expected_last_token {
        return true;
    } else if nodes[last_child].kind == Kind::SemicolonToken && last_node_and_tokens.len() > 1 {
        return nodes[last_node_and_tokens[last_node_and_tokens.len() - 2]].kind
            == expected_last_token;
    }
    false
}

/// `hasChildOfKind`.
fn has_child_of_kind(
    nodes: &mut Vec<Node>,
    containing_node: NodeId,
    kind: Kind,
    source_file: NodeId,
) -> bool {
    find_child_of_kind(nodes, source_file, containing_node, kind).is_some()
}
