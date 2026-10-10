// Ported from tsc/internal/ls/lsutil/children.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.
//
// PORT: `GetOrCreateToken` needs `&mut Vec<Node>` while
// `GetScannerForSourceFile` borrows `&SourceFile` inside the same arena, so
// the scanning loops clone `SourceFile::text` once and drive a `Scanner`
// over the clone (the same compromise tsc-astnav's `nav_scanner` makes).

use std::cell::Cell;

use tsc_ast::ast::Node;
use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeFlags, NodeId, NodeList};
use tsc_core::text::TextPos;
use tsc_astnav::tokens::visit_each_child_and_jsdoc;
use tsc_core::languagevariant::LanguageVariant;
use tsc_scanner::scanner::Scanner;

/// `scanner.GetScannerForSourceFile(sourceFile, pos)` on already-cloned text.
pub(crate) fn ls_scanner<'a>(
    text: &'a str,
    language_variant: LanguageVariant,
    pos: TextPos,
) -> Scanner<'a> {
    let mut s = Scanner::new();
    s.set_text(text);
    s.set_language_variant(language_variant);
    // Go panics on negative positions (slice OOB); `expect` mirrors that.
    s.reset_pos(usize::try_from(pos).expect("lsutil: negative position cannot be scanned"));
    s.scan();
    s
}

/// Replaces `last(node.getChildren(sourceFile))`.
pub fn get_last_child(
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<NodeId> {
    let last_child_node = get_last_visited_child(nodes, node, source_file);
    if ast::is_js_doc_single_comment_node(&nodes[node], nodes) && last_child_node.is_none() {
        return None;
    }
    let token_start_pos = last_child_node.map_or_else(|| nodes[node].pos(), |c| nodes[c].end());
    let mut last_token: Option<NodeId> = None;
    let text = nodes[source_file].as_source_file().text.clone();
    let language_variant = nodes[source_file].as_source_file().language_variant;
    let mut scan = ls_scanner(&text, language_variant, token_start_pos);
    let mut start_pos = token_start_pos;
    while start_pos < nodes[node].end() {
        let token_kind = scan.token();
        let token_full_start = scan.token_full_start() as TextPos;
        let token_end = scan.token_end() as TextPos;
        let flags = scan.token_flags();
        last_token = Some(ast::get_or_create_token(
            nodes,
            source_file,
            token_kind,
            token_full_start,
            token_end,
            node,
            flags,
        ));
        start_pos = token_end;
        scan.scan();
    }
    last_token.or(last_child_node)
}

/// `GetLastToken`.
pub fn get_last_token(
    nodes: &mut Vec<Node>,
    node: Option<NodeId>,
    source_file: NodeId,
) -> Option<NodeId> {
    let node = node?;

    if nodes[node].kind.is_token_kind() || ast::is_identifier(&nodes[node]) {
        return None;
    }

    assert_has_real_position(&nodes[node]);

    let last_child = get_last_child(nodes, node, source_file)?;

    if nodes[last_child].kind < Kind::FIRST_NODE {
        Some(last_child)
    } else {
        get_last_token(nodes, Some(last_child), source_file)
    }
}

/// Gets the last visited child of the given node.
/// NOTE: This doesn't include unvisited tokens; for this, use `get_last_child`
/// or `get_last_token`.
pub fn get_last_visited_child(
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<NodeId> {
    let last_child: Cell<Option<NodeId>> = Cell::new(None);

    let visit_node = |cx: &mut VisitorCx, n: NodeId, _v: &NodeVisitor| -> Option<NodeId> {
        // `n != nil` is guaranteed — `visit_each_child_and_jsdoc` never calls
        // the hook with Go's nil.
        if !cx.nodes[n].flags.intersects(NodeFlags::REPARSED) {
            last_child.set(Some(n));
        }
        Some(n)
    };
    let visit_nodes = |_cx: &mut VisitorCx,
                      node_list: Option<NodeList>,
                      _v: &NodeVisitor|
     -> Option<NodeList> {
        if let Some(node_list) = &node_list {
            if !node_list.nodes.is_empty() {
                for &v in node_list.nodes.iter().rev() {
                    if !_cx.nodes[v].flags.intersects(NodeFlags::REPARSED) {
                        last_child.set(Some(v));
                        break;
                    }
                }
            }
        }
        node_list
    };

    visit_each_child_and_jsdoc(
        nodes,
        source_file,
        node,
        Some(&visit_node),
        Some(&visit_nodes),
    );
    last_child.get()
}

/// `GetFirstToken`.
pub fn get_first_token(
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Option<NodeId> {
    if ast::is_identifier(&nodes[node]) || nodes[node].kind.is_token_kind() {
        return None;
    }
    assert_has_real_position(&nodes[node]);
    let mut first_child: Option<NodeId> = None;
    nodes[node].for_each_child(nodes, &mut |n| {
        if nodes[node].flags.intersects(NodeFlags::REPARSED) {
            return false;
        }
        first_child = Some(n);
        true
    });

    let token_end_position = first_child.map_or_else(|| nodes[node].end(), |c| nodes[c].pos());
    let text = nodes[source_file].as_source_file().text.clone();
    let language_variant = nodes[source_file].as_source_file().language_variant;
    let scan = ls_scanner(&text, language_variant, nodes[node].pos());
    let mut first_token: Option<NodeId> = None;
    if nodes[node].pos() < token_end_position {
        let token_kind = scan.token();
        let token_full_start = scan.token_full_start() as TextPos;
        let token_end = scan.token_end() as TextPos;
        first_token = Some(ast::get_or_create_token(
            nodes,
            source_file,
            token_kind,
            token_full_start,
            token_end,
            node,
            scan.token_flags(),
        ));
    }

    if first_token.is_some() {
        return first_token;
    }
    let first_child = first_child?;
    if nodes[first_child].kind < Kind::FIRST_NODE {
        return Some(first_child);
    }
    get_first_token(nodes, first_child, source_file)
}

/// `AssertHasRealPosition`.
pub fn assert_has_real_position(node: &Node) {
    if ast::position_is_synthesized(node.pos()) || ast::position_is_synthesized(node.end()) {
        panic!("Node must have a real position for this operation.");
    }
}
