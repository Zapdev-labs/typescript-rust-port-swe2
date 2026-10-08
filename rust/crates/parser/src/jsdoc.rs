// Ported from tsc/internal/parser/jsdoc.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::{Node, NodeFlags, NodeId};

use crate::parser::{
    JSDocScannerInfo, JSDOC_SCANNER_INFO_HAS_DEPRECATED, JSDOC_SCANNER_INFO_HAS_JSDOC,
    JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK, Parser,
};
use crate::utilities::get_jsdoc_comment_ranges;

/// `func init() { ast.SetParseJSDocForNode(parseJSDocForNode) }` — wired by
/// `parser::register_jsdoc_parse_hook`.

/// `func parseJSDocForNode(sourceFile *ast.SourceFile, node *ast.Node) []*ast.Node`
///
/// Lazily parses JSDoc for a node in a TS file. Called on first access to
/// `Node::jsdoc` for non-JS source files.
pub fn parse_jsdoc_for_node(
    _nodes: &mut Vec<Node>,
    _source_file: NodeId,
    _node: NodeId,
) -> Vec<NodeId> {
    // TODO: full JSDoc lazy-parse port pending (jsdoc.go).
    Vec::new()
}

impl<'a> Parser<'a> {
    /// `func (p *Parser) withJSDoc(node *ast.Node, info jsdocScannerInfo) []*ast.Node`
    pub fn with_jsdoc(&mut self, node: NodeId, info: JSDocScannerInfo) -> Vec<NodeId> {
        if !info & JSDOC_SCANNER_INFO_HAS_JSDOC != 0 {
            return Vec::new();
        }
        // For TS/TSX files, defer JSDoc parsing to first access, unless the comment
        // contains @see/@link (needed for unused-identifier checks).
        // @deprecated is detected via cheap text scan to set PossiblyContainsDeprecatedTag;
        // callers must confirm via JSDoc lookup.
        if !self.is_java_script() {
            self.nodes[node].flags |= NodeFlags::HAS_JSDOC;
            if info & JSDOC_SCANNER_INFO_HAS_DEPRECATED != 0 {
                self.nodes[node].flags |= NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG;
            }
            if !info & JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK != 0 {
                return Vec::new();
            }
            // Fall through to eager parse for @see/@link
        }
        let mut ranges = get_jsdoc_comment_ranges(
            &self.factory,
            std::mem::take(&mut self.jsdoc_comment_ranges_space),
            node,
            self.source_text,
            &self.nodes,
        );
        // Should only be called once per node
        self.has_deprecated_tag = false;
        let mut jsdoc: Vec<NodeId> = Vec::with_capacity(8);
        let mut pos = self.nodes[node].pos();
        for comment in &ranges {
            if let Some(parsed) = self.parse_jsdoc_comment(
                node,
                comment.text_range.pos(),
                comment.text_range.end(),
                pos,
            ) {
                self.nodes[parsed].parent = Some(node);
                jsdoc.push(parsed);
                pos = self.nodes[parsed].end();
            }
        }
        ranges.clear();
        self.jsdoc_comment_ranges_space = ranges;
        if !jsdoc.is_empty() {
            if !self.nodes[node].flags.intersects(NodeFlags::HAS_JSDOC) {
                self.nodes[node].flags |= NodeFlags::HAS_JSDOC;
            }
            if self.has_deprecated_tag {
                self.has_deprecated_tag = false;
                self.nodes[node].flags |= NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG;
            }
            if self.is_java_script() {
                self.reparse_tags(node, &jsdoc);
            }
            self.jsdoc_infos.push(crate::parser::JSDocInfo {
                parent: Some(node),
                js_docs: jsdoc.clone(),
            });
            return jsdoc;
        }
        Vec::new()
    }

    /// `func (p *Parser) parseJSDocComment(parent, start, end, fullStart)` —
    /// TODO: full port pending; returns `None` for now.
    pub fn parse_jsdoc_comment(
        &mut self,
        _parent: NodeId,
        _start: i32,
        _end: i32,
        _full_start: i32,
    ) -> Option<NodeId> {
        None
    }

    /// `func (p *Parser) reparseTags(node, jsdoc)` — reparser.go; TODO.
    pub fn reparse_tags(&mut self, _node: NodeId, _jsdoc: &[NodeId]) {}
}
