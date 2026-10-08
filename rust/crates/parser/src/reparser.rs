// Ported from tsc/internal/parser/reparser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// TODO: full port in progress.
use tsc_ast::{Node, NodeId};

pub fn extract_eventual_pos(_nodes: &[Node], _node: NodeId) -> i32 { 0 }
pub fn has_parsed_jsdoc_namespace(_nodes: &[Node], _node: NodeId) -> bool { false }
pub fn is_matching_tag(_nodes: &[Node], _a: NodeId, _b: NodeId) -> bool { false }
pub fn is_valid_statement_type(_nodes: &[Node], _node: NodeId) -> bool { false }
pub fn is_valid_tuple_type(_nodes: &[Node], _node: NodeId) -> bool { false }
pub fn reparse_top_level_import(_nodes: &mut Vec<Node>, _node: NodeId) {}
pub fn reparse_un_parenthesized_arrow_function(_nodes: &mut Vec<Node>, _node: NodeId) {}
