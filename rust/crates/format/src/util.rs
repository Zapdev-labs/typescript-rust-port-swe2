// Ported from tsc/internal/format/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_astnav::tokens::find_preceding_token;
use tsc_core::text::{TextPos, TextRange};
use tsc_scanner::scanner::{compute_line_of_position, compute_position_of_line_and_byte_offset};

use crate::indent::decode_rune_in_string;

/// `GetECMALineStarts` — reads the `OnceLock`-cached `SourceFile::ecma_line_map`
/// instead of the `tsc_scanner` helper, whose `SourceFileLike` impl recomputes
/// the whole line map per call (O(text) → quadratic formatting on large files).
pub(crate) fn line_map<'a>(nodes: &'a [Node], source_file: NodeId) -> &'a [TextPos] {
    nodes[source_file].as_source_file().ecma_line_map()
}

/// `GetECMALineOfPosition`
pub(crate) fn line_of_position(nodes: &[Node], source_file: NodeId, pos: i32) -> i32 {
    compute_line_of_position(line_map(nodes, source_file), pos)
}

/// `GetECMALineAndByteOffsetOfPosition`
pub(crate) fn line_and_byte_offset_of_position(
    nodes: &[Node],
    source_file: NodeId,
    pos: i32,
) -> (i32, i32) {
    let line_starts = line_map(nodes, source_file);
    let line = compute_line_of_position(line_starts, pos);
    (line, pos - line_starts[line as usize])
}

/// `GetECMAEndLinePosition`
pub(crate) fn end_line_position(nodes: &[Node], source_file: NodeId, line: i32) -> i32 {
    let mut pos = line_map(nodes, source_file)[line as usize] as usize;
    let bytes = nodes[source_file].as_source_file().text.as_bytes();
    loop {
        let (ch, size) = decode_rune_in_string(&bytes[pos..]);
        if size == 0 || tsc_stringutil::is_line_break(ch) {
            return pos as i32 - 1;
        }
        pos += size;
    }
}

/// `GetECMAPositionOfLineAndByteOffset`
pub(crate) fn position_of_line_and_byte_offset(
    nodes: &[Node],
    source_file: NodeId,
    line: i32,
    byte_offset: i32,
) -> i32 {
    compute_position_of_line_and_byte_offset(&line_map(nodes, source_file), line, byte_offset)
}

/// `rangeIsOnOneLine`
pub(crate) fn range_is_on_one_line(node: TextRange, file: NodeId, nodes: &[Node]) -> bool {
    let start_line = line_of_position(nodes, file, node.pos());
    let end_line = line_of_position(nodes, file, node.end());
    start_line == end_line
}

/// `getOpenTokenForList`
pub(crate) fn get_open_token_for_list(
    node: NodeId,
    list: &tsc_ast::ast::NodeList,
    nodes: &[Node],
) -> Kind {
    let n = &nodes[node];
    match n.kind {
        Kind::Constructor
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::ArrowFunction
        | Kind::CallSignature
        | Kind::ConstructSignature
        | Kind::FunctionType
        | Kind::ConstructorType
        | Kind::GetAccessor
        | Kind::SetAccessor => {
            if n.type_parameter_list()
                .is_some_and(|l| std::ptr::eq(l, list))
            {
                return Kind::LessThanToken;
            } else if n.parameter_list().is_some_and(|l| std::ptr::eq(l, list)) {
                return Kind::OpenParenToken;
            }
        }
        Kind::CallExpression | Kind::NewExpression => {
            if n.type_argument_list()
                .is_some_and(|l| std::ptr::eq(l, list))
            {
                return Kind::LessThanToken;
            } else if n.argument_list().is_some_and(|l| std::ptr::eq(l, list)) {
                return Kind::OpenParenToken;
            }
        }
        Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::InterfaceDeclaration
        | Kind::TypeAliasDeclaration => {
            if n.type_parameter_list()
                .is_some_and(|l| std::ptr::eq(l, list))
            {
                return Kind::LessThanToken;
            }
        }
        Kind::TypeReference
        | Kind::TaggedTemplateExpression
        | Kind::TypeQuery
        | Kind::ExpressionWithTypeArguments
        | Kind::ImportType => {
            if n.type_argument_list()
                .is_some_and(|l| std::ptr::eq(l, list))
            {
                return Kind::LessThanToken;
            }
        }
        Kind::TypeLiteral => {
            return Kind::OpenBraceToken;
        }
        _ => {}
    }

    Kind::Unknown
}

/// `getCloseTokenForOpenToken`
pub(crate) fn get_close_token_for_open_token(kind: Kind) -> Kind {
    // TODO: matches strada - seems like it could handle more pairs of braces, though? [] notably missing
    match kind {
        Kind::OpenParenToken => Kind::CloseParenToken,
        Kind::LessThanToken => Kind::GreaterThanToken,
        Kind::OpenBraceToken => Kind::CloseBraceToken,
        _ => Kind::Unknown,
    }
}

/// `GetLineStartPositionForPosition`
pub fn get_line_start_position_for_position(
    position: i32,
    source_file: NodeId,
    nodes: &[Node],
) -> i32 {
    let line_starts = line_map(nodes, source_file);
    let line = compute_line_of_position(line_starts, position);
    line_starts[line as usize]
}

/// `findImmediatelyPrecedingTokenOfKind`
///
/// Validating `expectedTokenKind` ensures the token was typed in the context we expect (eg: not a comment).
pub(crate) fn find_immediately_preceding_token_of_kind(
    end: i32,
    expected_token_kind: Kind,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> Option<NodeId> {
    let preceding_token = find_preceding_token(nodes, source_file, end)?;
    if nodes[preceding_token].kind != expected_token_kind || nodes[preceding_token].end() != end {
        return None;
    }
    Some(preceding_token)
}

/// `findOutermostNodeWithinListLevel`
///
/// Finds the highest node enclosing `node` at the same list level as `node`
/// and whose end does not exceed `node.end`.
///
/// Consider typing the following
/// ```text
/// let x = 1;
/// while (true) {
/// }
/// ```
/// Upon typing the closing curly, we want to format the entire `while`-statement, but not the preceding
/// variable declaration.
pub(crate) fn find_outermost_node_within_list_level(
    node: Option<NodeId>,
    nodes: &[Node],
) -> Option<NodeId> {
    let node_end = nodes[node?].end();
    let mut current = node;
    while let Some(c) = current {
        let Some(parent) = nodes[c].parent else { break };
        if nodes[parent].end() != node_end || is_list_element(parent, c, nodes) {
            break;
        }
        current = Some(parent);
    }
    current
}

/// `isListElement` — returns true if node is a element in some list in parent
/// i.e. parent is class declaration with the list of members and node is one of members.
fn is_list_element(parent: NodeId, node: NodeId, nodes: &[Node]) -> bool {
    match nodes[parent].kind {
        Kind::ClassDeclaration | Kind::InterfaceDeclaration => nodes[node]
            .loc
            .contained_by(&nodes[parent].member_list().expect("member list").loc),
        Kind::ModuleDeclaration => {
            let body = nodes[parent].body();
            body.is_some_and(|b| {
                nodes[b].kind == Kind::ModuleBlock
                    && nodes[node]
                        .loc
                        .contained_by(&nodes[b].statement_list().expect("statement list").loc)
            })
        }
        Kind::SourceFile | Kind::Block | Kind::ModuleBlock => nodes[node]
            .loc
            .contained_by(&nodes[parent].statement_list().expect("statement list").loc),
        Kind::CatchClause => {
            let block = nodes[parent].as_catch_clause().block.expect("catch block");
            nodes[node]
                .loc
                .contained_by(&nodes[block].statement_list().expect("statement list").loc)
        }
        _ => false,
    }
}

/// `isMemberListElement`
pub(crate) fn is_member_list_element(parent: NodeId, node: NodeId, nodes: &[Node]) -> bool {
    match nodes[parent].kind {
        Kind::ClassDeclaration
        | Kind::ClassExpression
        | Kind::InterfaceDeclaration
        | Kind::EnumDeclaration
        | Kind::TypeLiteral
        | Kind::MappedType => nodes[node]
            .loc
            .contained_by(&nodes[parent].member_list().expect("member list").loc),
        _ => false,
    }
}
