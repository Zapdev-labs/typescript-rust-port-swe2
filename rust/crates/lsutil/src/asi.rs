// Ported from tsc/internal/ls/lsutil/asi.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.

use tsc_ast::ast::Node;
use tsc_ast::{self as ast, FindAncestorResult, Kind, NodeId};
use tsc_astnav::tokens::{find_next_token, get_start_of_node};
use tsc_core::text::TextPos;
use tsc_scanner::scanner::get_ecma_line_of_position;

use crate::children::get_last_child;
use crate::children::get_last_token;

/// `PositionIsASICandidate`.
pub fn position_is_asi_candidate(
    nodes: &mut Vec<Node>,
    pos: TextPos,
    context: NodeId,
    file: NodeId,
) -> bool {
    let context_ancestor =
        ast::find_ancestor_or_quit(Some(context), nodes, &mut |ancestor, _nodes| {
            if ancestor.end() != pos {
                return FindAncestorResult::Quit;
            }
            ast::to_find_ancestor_result(syntax_may_be_asi_candidate(ancestor.kind))
        });

    context_ancestor.is_some() && node_is_asi_candidate(nodes, context_ancestor, file)
}

/// `SyntaxMayBeASICandidate`.
pub fn syntax_may_be_asi_candidate(kind: Kind) -> bool {
    syntax_requires_trailing_comma_or_semicolon_or_asi(kind)
        || syntax_requires_trailing_function_block_or_semicolon_or_asi(kind)
        || syntax_requires_trailing_module_block_or_semicolon_or_asi(kind)
        || syntax_requires_trailing_semicolon_or_asi(kind)
}

/// `SyntaxRequiresTrailingCommaOrSemicolonOrASI`.
pub fn syntax_requires_trailing_comma_or_semicolon_or_asi(kind: Kind) -> bool {
    kind == Kind::CallSignature
        || kind == Kind::ConstructSignature
        || kind == Kind::IndexSignature
        || kind == Kind::PropertySignature
        || kind == Kind::MethodSignature
}

/// `SyntaxRequiresTrailingFunctionBlockOrSemicolonOrASI`.
pub fn syntax_requires_trailing_function_block_or_semicolon_or_asi(kind: Kind) -> bool {
    kind == Kind::FunctionDeclaration
        || kind == Kind::Constructor
        || kind == Kind::MethodDeclaration
        || kind == Kind::GetAccessor
        || kind == Kind::SetAccessor
}

/// `SyntaxRequiresTrailingModuleBlockOrSemicolonOrASI`.
pub fn syntax_requires_trailing_module_block_or_semicolon_or_asi(kind: Kind) -> bool {
    kind == Kind::ModuleDeclaration
}

/// `SyntaxRequiresTrailingSemicolonOrASI`.
pub fn syntax_requires_trailing_semicolon_or_asi(kind: Kind) -> bool {
    kind == Kind::VariableStatement
        || kind == Kind::ExpressionStatement
        || kind == Kind::DoStatement
        || kind == Kind::ContinueStatement
        || kind == Kind::BreakStatement
        || kind == Kind::ReturnStatement
        || kind == Kind::ThrowStatement
        || kind == Kind::DebuggerStatement
        || kind == Kind::PropertyDeclaration
        || kind == Kind::TypeAliasDeclaration
        || kind == Kind::ImportDeclaration
        || kind == Kind::ImportEqualsDeclaration
        || kind == Kind::ExportDeclaration
        || kind == Kind::NamespaceExportDeclaration
        || kind == Kind::ExportAssignment
}

/// `NodeIsASICandidate`.
pub fn node_is_asi_candidate(nodes: &mut Vec<Node>, node: Option<NodeId>, file: NodeId) -> bool {
    let Some(node) = node else {
        return false;
    };

    let last_token = get_last_token(nodes, Some(node), file);
    if last_token.is_some_and(|t| nodes[t].kind == Kind::SemicolonToken) {
        return false;
    }

    if syntax_requires_trailing_comma_or_semicolon_or_asi(nodes[node].kind) {
        if last_token.is_some_and(|t| nodes[t].kind == Kind::CommaToken) {
            return false;
        }
    } else if syntax_requires_trailing_module_block_or_semicolon_or_asi(nodes[node].kind) {
        let last_child = get_last_child(nodes, node, file);
        if last_child.is_some_and(|c| ast::is_module_block(&nodes[c])) {
            return false;
        }
    } else if syntax_requires_trailing_function_block_or_semicolon_or_asi(nodes[node].kind) {
        let last_child = get_last_child(nodes, node, file);
        if last_child.is_some_and(|c| ast::is_function_block(Some(c), nodes)) {
            return false;
        }
    } else if !syntax_requires_trailing_semicolon_or_asi(nodes[node].kind) {
        return false;
    }

    // See comment in parser's `parseDoStatement`
    if nodes[node].kind == Kind::DoStatement {
        return true;
    }

    let top_node = ast::find_ancestor(Some(node), nodes, &mut |n, _| n.parent.is_none())
        .expect("NodeIsASICandidate: every node chain terminates at a root");
    let next_token = find_next_token(nodes, file, node, top_node);
    let Some(next_token) = next_token else {
        return true;
    };
    if nodes[next_token].kind == Kind::CloseBraceToken {
        return true;
    }

    let next_token_start =
        get_start_of_node(nodes, file, next_token, false /* includeJSDoc */);
    let start_line = get_ecma_line_of_position(nodes[file].as_source_file(), nodes[node].end());
    let end_line = get_ecma_line_of_position(nodes[file].as_source_file(), next_token_start);
    start_line != end_line
}
