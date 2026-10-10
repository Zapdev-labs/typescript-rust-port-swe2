// Ported from tsc/internal/format/context.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_astnav::tokens::find_child_of_kind;
use tsc_core::text::TextRange;
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN, Tristate};
use tsc_lsutil::FormatCodeSettings;
use tsc_scanner::scanner::get_token_pos_of_node;

use crate::api::FormatRequestKind;
use crate::scanner::TextRangeWithKind;
use crate::util::range_is_on_one_line;

/// `type FormattingContext struct`
///
/// PORT: `SourceFile` becomes `source_file: NodeId`; all methods that need
/// the arena take `nodes` (mutable where `astnav` requires it).
pub struct FormattingContext {
    pub(crate) current_token_span: TextRangeWithKind,
    pub(crate) next_token_span: TextRangeWithKind,
    pub(crate) context_node: NodeId,
    pub(crate) current_token_parent: NodeId,
    pub(crate) next_token_parent: NodeId,

    context_node_all_on_same_line: Tristate,
    next_node_all_on_same_line: Tristate,
    tokens_are_on_same_line: Tristate,
    context_node_block_is_on_one_line: Tristate,
    next_node_block_is_on_one_line: Tristate,

    pub source_file: NodeId,
    pub formatting_request_kind: FormatRequestKind,
    pub options: FormatCodeSettings,
}

impl FormattingContext {
    /// `NewFormattingContext`
    pub(crate) fn new(
        file: NodeId,
        kind: FormatRequestKind,
        options: FormatCodeSettings,
    ) -> FormattingContext {
        FormattingContext {
            current_token_span: TextRangeWithKind::default(),
            next_token_span: TextRangeWithKind::default(),
            context_node: NodeId::NONE,
            current_token_parent: NodeId::NONE,
            next_token_parent: NodeId::NONE,
            context_node_all_on_same_line: TS_UNKNOWN,
            next_node_all_on_same_line: TS_UNKNOWN,
            tokens_are_on_same_line: TS_UNKNOWN,
            context_node_block_is_on_one_line: TS_UNKNOWN,
            next_node_block_is_on_one_line: TS_UNKNOWN,
            source_file: file,
            formatting_request_kind: kind,
            options,
        }
    }

    /// `(this *FormattingContext) UpdateContext`
    pub(crate) fn update_context(
        &mut self,
        cur: TextRangeWithKind,
        cur_parent: NodeId,
        next: TextRangeWithKind,
        next_parent: NodeId,
        common_parent: NodeId,
    ) {
        if cur_parent == NodeId::NONE {
            panic!("nil current range node parent in update context");
        }
        if next_parent == NodeId::NONE {
            panic!("nil next range node parent in update context");
        }
        if common_parent == NodeId::NONE {
            panic!("nil common parent node in update context");
        }
        self.current_token_span = cur;
        self.current_token_parent = cur_parent;
        self.next_token_span = next;
        self.next_token_parent = next_parent;
        self.context_node = common_parent;

        // drop cached results
        self.context_node_all_on_same_line = TS_UNKNOWN;
        self.next_node_all_on_same_line = TS_UNKNOWN;
        self.tokens_are_on_same_line = TS_UNKNOWN;
        self.context_node_block_is_on_one_line = TS_UNKNOWN;
        self.next_node_block_is_on_one_line = TS_UNKNOWN;
    }

    /// `(this *FormattingContext) rangeIsOnOneLine`
    fn range_is_on_one_line(&self, node: TextRange, nodes: &[Node]) -> Tristate {
        if range_is_on_one_line(node, self.source_file, nodes) {
            return TS_TRUE;
        }
        TS_FALSE
    }

    /// `(this *FormattingContext) nodeIsOnOneLine`
    fn node_is_on_one_line(&self, node: NodeId, nodes: &[Node]) -> Tristate {
        self.range_is_on_one_line(with_token_start(node, self.source_file, nodes), nodes)
    }

    /// `(this *FormattingContext) blockIsOnOneLine`
    fn block_is_on_one_line(&mut self, node: NodeId, nodes: &mut Vec<Node>) -> Tristate {
        let open_brace = find_child_of_kind(
            nodes,
            self.source_file,
            node,
            tsc_ast::kind_generated::Kind::OpenBraceToken,
        );
        let close_brace = find_child_of_kind(
            nodes,
            self.source_file,
            node,
            tsc_ast::kind_generated::Kind::CloseBraceToken,
        );
        if let (Some(open_brace), Some(close_brace)) = (open_brace, close_brace) {
            let close_brace_start = get_token_pos_of_node(
                close_brace,
                nodes[self.source_file].as_source_file(),
                false,
                nodes,
            );
            return self.range_is_on_one_line(
                TextRange::new(nodes[open_brace].end(), close_brace_start),
                nodes,
            );
        }
        TS_FALSE
    }

    /// `(this *FormattingContext) ContextNodeAllOnSameLine`
    pub(crate) fn context_node_all_on_same_line(&mut self, nodes: &[Node]) -> bool {
        if self.context_node_all_on_same_line == TS_UNKNOWN {
            self.context_node_all_on_same_line = self.node_is_on_one_line(self.context_node, nodes);
        }
        self.context_node_all_on_same_line == TS_TRUE
    }

    /// `(this *FormattingContext) NextNodeAllOnSameLine`
    pub(crate) fn next_node_all_on_same_line(&mut self, nodes: &[Node]) -> bool {
        if self.next_node_all_on_same_line == TS_UNKNOWN {
            self.next_node_all_on_same_line =
                self.node_is_on_one_line(self.next_token_parent, nodes);
        }
        self.next_node_all_on_same_line == TS_TRUE
    }

    /// `(this *FormattingContext) TokensAreOnSameLine`
    pub(crate) fn tokens_are_on_same_line(&mut self, nodes: &[Node]) -> bool {
        if self.tokens_are_on_same_line == TS_UNKNOWN {
            self.tokens_are_on_same_line = self.range_is_on_one_line(
                TextRange::new(
                    self.current_token_span.loc.pos(),
                    self.next_token_span.loc.pos(),
                ),
                nodes,
            );
        }
        self.tokens_are_on_same_line == TS_TRUE
    }

    /// `(this *FormattingContext) ContextNodeBlockIsOnOneLine`
    pub(crate) fn context_node_block_is_on_one_line(&mut self, nodes: &mut Vec<Node>) -> bool {
        if self.context_node_block_is_on_one_line == TS_UNKNOWN {
            self.context_node_block_is_on_one_line =
                self.block_is_on_one_line(self.context_node, nodes);
        }
        self.context_node_block_is_on_one_line == TS_TRUE
    }

    /// `(this *FormattingContext) NextNodeBlockIsOnOneLine`
    pub(crate) fn next_node_block_is_on_one_line(&mut self, nodes: &mut Vec<Node>) -> bool {
        if self.next_node_block_is_on_one_line == TS_UNKNOWN {
            self.next_node_block_is_on_one_line =
                self.block_is_on_one_line(self.next_token_parent, nodes);
        }
        self.next_node_block_is_on_one_line == TS_TRUE
    }
}

/// `withTokenStart`
pub(crate) fn with_token_start(loc: NodeId, file: NodeId, nodes: &[Node]) -> TextRange {
    let start_pos = get_token_pos_of_node(loc, nodes[file].as_source_file(), false, nodes);
    TextRange::new(start_pos, nodes[loc].end())
}
