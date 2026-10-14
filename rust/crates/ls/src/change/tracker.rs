// Ported from tsc/internal/ls/change/tracker.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::{RefCell, RefMut};
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{ArenaCell, Kind, Node, NodeId, NodeList, self as ast};
use tsc_astnav::tokens as astnav;
use tsc_collections::{MultiMap, Set};
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::{TextPos, TextRange};
use tsc_format as format;
use tsc_lsconv::converters::Converters;
use tsc_lsproto::{Position, Range, TextEdit};
use tsc_lsutil::{self as lsutil, FormatCodeSettings};
use tsc_printer::{self as printer, EmitContext};
use tsc_scanner::scanner;
use tsc_spanmap as spanmap;
use tsc_stringutil as stringutil;
use tsc_tspath::RootedFilePath;

use crate::change::trackerimpl::{has_comments_before_line_break, need_semicolon_between};

/// `type NodeOptions struct`
#[derive(Clone, Default)]
pub struct NodeOptions {
    /// `Prefix` — text to be inserted before the new node.
    pub prefix: String,
    /// `Suffix` — text to be inserted after the new node.
    pub suffix: String,
    /// `indentation` — text of inserted node will be formatted with this
    /// indentation; otherwise indentation is inferred from the old node.
    pub(crate) indentation: Option<i32>,
    /// `delta` — text of inserted node will be formatted with this delta;
    /// otherwise delta is inferred from the new node kind.
    pub(crate) delta: Option<i32>,
    /// `LeadingTriviaOption` — Go embeds the type; flattened here.
    pub leading_trivia_option: LeadingTriviaOption,
    /// `TrailingTriviaOption` — Go embeds the type; flattened here.
    pub trailing_trivia_option: TrailingTriviaOption,
    /// `joiner` — unexported in Go and never set outside this package.
    pub(crate) joiner: String,
}

/// `type LeadingTriviaOption int`
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
#[repr(i32)]
pub enum LeadingTriviaOption {
    /// `LeadingTriviaOptionNone`
    #[default]
    None = 0,
    /// `LeadingTriviaOptionExclude`
    Exclude = 1,
    /// `LeadingTriviaOptionIncludeAll`
    IncludeAll = 2,
    /// `LeadingTriviaOptionJSDoc`
    JSDoc = 3,
    /// `LeadingTriviaOptionStartLine`
    StartLine = 4,
}

/// `type TrailingTriviaOption int`
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
#[repr(i32)]
pub enum TrailingTriviaOption {
    /// `TrailingTriviaOptionNone`
    #[default]
    None = 0,
    /// `TrailingTriviaOptionExclude`
    Exclude = 1,
    /// `TrailingTriviaOptionExcludeWhitespace`
    ExcludeWhitespace = 2,
    /// `TrailingTriviaOptionInclude`
    Include = 3,
}

/// `type trackerEditKind int`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum TrackerEditKind {
    /// `trackerEditKindText`
    Text,
    /// `trackerEditKindRemove`
    Remove,
    /// `trackerEditKindReplaceWithSingleNode`
    ReplaceWithSingleNode,
    /// `trackerEditKindReplaceWithMultipleNodes`
    ReplaceWithMultipleNodes,
}

/// `type trackerEdit struct`
#[derive(Clone)]
pub(crate) struct TrackerEdit {
    pub kind: TrackerEditKind,
    /// `core.TextRange` — Go embeds it; flattened here.
    pub range: TextRange,
    /// `NewText` — kind == Text.
    pub new_text: String,
    /// `*ast.Node` — kind == ReplaceWithSingleNode.
    pub node: NodeId,
    /// `nodes` — kind == ReplaceWithMultipleNodes.
    pub nodes: Vec<NodeId>,
    /// `options`.
    pub options: NodeOptions,
}

/// `type deletedNode struct`
pub(crate) struct DeletedNode {
    pub source_file: NodeId,
    pub node: NodeId,
}

/// `type nodesInsertedAtStartState struct`
pub(crate) struct NodesInsertedAtStartState {
    pub node: NodeId,
    pub source_file: NodeId,
}

/// `type Tracker struct`.
///
/// PORT: Go's `Tracker` embeds `*printer.EmitContext` and `*ast.NodeFactory`
/// (an alias of `&emitContext.Factory.NodeFactory`). Rust has no embedding, so
/// `emit_context` is a named public field and `t.NewX(...)` calls become
/// `tracker.node_factory(file).new_x(&mut nodes, ...)` — the file argument
/// binds the factory's `file_index` so minted `NodeId`s index the caller's
/// arena. Methods that inspect or mutate syntax take the source file's arena
/// as `nodes: &Rc<ArenaCell>`; the handle is recorded so
/// `get_changes` can re-borrow arenas for every changed file.
///
/// PORT(lifetimes): `Converters<'c>` is invariant over its inner lifetime, so
/// callers that hold `&'x Converters<'h>` (`'x` shorter than `'h`) cannot
/// provide `&'a Converters<'a>` — the tracker therefore keeps the two
/// lifetimes distinct.
pub struct Tracker<'a, 'c> {
    /// `formatSettings`.
    pub format_settings: FormatCodeSettings,
    /// `newLine`.
    pub new_line: String,
    /// `converters`.
    pub(crate) converters: &'a Converters<'c>,
    /// `ctx`.
    pub ctx: Context,
    /// `*printer.EmitContext` (Go embedded field).
    pub emit_context: EmitContext,

    /// `changes`.
    pub(crate) changes: MultiMap<NodeId, TrackerEdit>,
    /// PORT(addition): `file_index` → arena handle, so `get_changes` (which
    /// takes no arena arguments, matching Go) can borrow every changed file's
    /// `Vec<Node>`. Populated by every method that receives a `nodes` handle.
    pub(crate) arena_handles: FxHashMap<u32, Rc<ArenaCell>>,
    /// `deletedNodes`.
    pub(crate) deleted_nodes: Vec<DeletedNode>,
    /// `nodesWithInsertionsAtStart` — keyed by the container `NodeId`.
    pub(crate) nodes_with_insertions_at_start: FxHashMap<NodeId, NodesInsertedAtStartState>,

    /// `unmappableFiles` collects the files for which an edit could not be
    /// represented within a single verbatim span of the original text.
    /// `get_changes` drops their edits so a partial, corrupting change is
    /// never emitted for a content-mapped file.
    pub(crate) unmappable_files: Set<RootedFilePath>,
}

/// `NewTracker`.
pub fn new_tracker<'a, 'c>(
    ctx: Context,
    compiler_options: &CompilerOptions,
    format_options: FormatCodeSettings,
    converters: &'a Converters<'c>,
) -> Tracker<'a, 'c> {
    let emit_context = EmitContext::new();
    let new_line = compiler_options
        .new_line
        .get_new_line_character()
        .to_string();
    let ctx = format::with_format_code_settings(&ctx, format_options.clone(), &new_line);
    Tracker {
        emit_context,
        changes: MultiMap::new(),
        ctx,
        converters,
        format_settings: format_options,
        new_line,
        arena_handles: FxHashMap::default(),
        deleted_nodes: Vec::new(),
        nodes_with_insertions_at_start: FxHashMap::default(),
        unmappable_files: Set::new(),
    }
}

impl<'a, 'c> Tracker<'a, 'c> {
    /// `t.NodeFactory` — the embedded `*ast.NodeFactory` (`=
    /// &emitContext.Factory.NodeFactory` in Go).
    ///
    /// PORT: returns the printer `NodeFactory`, which `Deref`s to
    /// `ast::NodeFactory` — all `new_*` constructors are reachable through it.
    /// The factory's `file_index` is bound to `file`'s arena so minted
    /// `NodeId`s resolve in the arena callers mutate.
    pub fn node_factory(&mut self, file: NodeId) -> &mut printer::NodeFactory {
        self.emit_context
            .factory
            .set_file_index(file.file_index() as u32);
        &mut self.emit_context.factory
    }

    /// PORT(addition): borrow the arena for `nodes`, registering the handle
    /// for later `get_changes` use. Every public entry point that touches a
    /// source file's nodes must go through this so `get_changes` sees the
    /// arena even if the file key was only added via `replace_*`.
    pub(crate) fn borrow_nodes<'x>(
        &mut self,
        nodes: &'x Rc<ArenaCell>,
        file: NodeId,
    ) -> tsc_ast::ArenaMut {
        self.arena_handles
            .insert(file.file_index() as u32, nodes.clone());
        nodes.cow()
    }

    /// `GetChanges` returns the accumulated text edits grouped by file name.
    /// Any file whose edits could not be faithfully mapped back onto
    /// content-mapped original text is omitted from the returned map, and its
    /// name is included in the returned slice. Dropping the whole file (rather
    /// than the individual edit) keeps a logical change atomic, and returning
    /// the result inline means a caller cannot forget to check it or
    /// accidentally emit a partial, corrupting change.
    /// Note: after calling this, the Tracker object must be discarded!
    ///
    /// PORT: `map[tspath.RootedFilePath][]*lsproto.TextEdit` →
    /// `FxHashMap<RootedFilePath, Vec<TextEdit>>`.
    pub fn get_changes(
        &mut self,
    ) -> (
        FxHashMap<RootedFilePath, Vec<TextEdit>>,
        Vec<RootedFilePath>,
    ) {
        self.finish_delete_declarations();
        self.finish_nodes_with_insertions_at_start();
        let mut changes = self.get_text_changes_from_changes();
        // !!! changes for new files
        if self.unmappable_files.is_empty() {
            return (changes, Vec::new());
        }
        let mut unmappable: Vec<RootedFilePath> = Vec::with_capacity(self.unmappable_files.len());
        for file_name in self.unmappable_files.keys().iter() {
            changes.remove(file_name);
            unmappable.push(file_name.clone());
        }
        unmappable.sort();
        (changes, unmappable)
    }

    /// `fromLSPEditRange` converts an LSP range to a source file range. For a
    /// content-mapped file, an original range may have several projections;
    /// this selects the one belonging to `source_file`. A range with no exact
    /// projection cannot be written back and marks the file unmappable.
    pub(crate) fn from_lsp_edit_range(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        lsproto_range: Range,
    ) -> TextRange {
        let n = nodes.snapshot();
        let spans = self.converters.from_lsp_range_for_source_file(
            source_file,
            &n,
            lsproto_range,
            spanmap::Feature::All,
        );
        let mut first_span = None;
        for span in &spans {
            if span.fidelity.is_exact() && span.script.file == source_file {
                return span.span;
            }
            if first_span.is_none() {
                first_span = Some(span.span);
            }
        }
        let file_name = n[source_file]
            .as_source_file()
            .original_file_name(&n)
            .clone();
        drop(n);
        self.unmappable_files.add(file_name);
        if let Some(span) = first_span {
            return span;
        }
        TextRange::new(0, 0)
    }

    /// `toLSPEditRange` converts a source file range to an LSP range. For a
    /// content-mapped file, the range is mapped back to the original document.
    /// If it does not fall entirely within a single verbatim span, the edit
    /// cannot be represented safely: the file is recorded so `get_changes`
    /// drops its edits, and a best-effort range is returned so the accumulated
    /// edits stay well-formed.
    pub(crate) fn to_lsp_edit_range(
        &mut self,
        nodes: &[Node],
        source_file: NodeId,
        text_range: TextRange,
    ) -> Range {
        let (r, fidelity) = self.converters.to_lsp_range(
            &tsc_lsconv::converters::source_file_script(source_file, nodes),
            text_range,
        );
        if !fidelity.is_exact() {
            // The range does not map into a single verbatim span, so the edit
            // cannot be represented safely in the original text. Record the
            // file so get_changes drops its edits, keeping the best-effort
            // range so the accumulated edits stay well-formed.
            self.unmappable_files.add(
                nodes[source_file]
                    .as_source_file()
                    .original_file_name(nodes)
                    .clone(),
            );
        }
        r
    }

    /// `ReplaceNode`.
    pub fn replace_node(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        old_node: NodeId,
        new_node: NodeId,
        options: Option<&NodeOptions>,
    ) {
        // defaults to `useNonAdjustedPositions`
        let default_options;
        let options = match options {
            Some(o) => o.clone(),
            None => {
                default_options = NodeOptions {
                    leading_trivia_option: LeadingTriviaOption::Exclude,
                    trailing_trivia_option: TrailingTriviaOption::Exclude,
                    ..Default::default()
                };
                default_options
            }
        };
        let range = self.get_adjusted_range(
            nodes,
            source_file,
            old_node,
            old_node,
            options.leading_trivia_option,
            options.trailing_trivia_option,
        );
        self.replace_range(nodes, source_file, range, new_node, options);
    }

    /// `ReplaceNodeWithNodes`.
    pub fn replace_node_with_nodes(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        old_node: NodeId,
        new_nodes: Vec<NodeId>,
        options: Option<&NodeOptions>,
    ) {
        let default_options;
        let options = match options {
            Some(o) => o.clone(),
            None => {
                default_options = NodeOptions {
                    leading_trivia_option: LeadingTriviaOption::Exclude,
                    trailing_trivia_option: TrailingTriviaOption::Exclude,
                    ..Default::default()
                };
                default_options
            }
        };
        let range = self.get_adjusted_range(
            nodes,
            source_file,
            old_node,
            old_node,
            options.leading_trivia_option,
            options.trailing_trivia_option,
        );
        self.replace_range_with_nodes(nodes, source_file, range, new_nodes, options);
    }

    /// `ReplaceRange` replaces `text_range` in `source_file` with `new_node`.
    pub fn replace_range(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        text_range: TextRange,
        new_node: NodeId,
        options: NodeOptions,
    ) {
        let _ = self.borrow_nodes(nodes, source_file);
        self.changes.add(
            source_file,
            TrackerEdit {
                kind: TrackerEditKind::ReplaceWithSingleNode,
                range: text_range,
                options,
                node: new_node,
                new_text: String::new(),
                nodes: Vec::new(),
            },
        );
    }

    /// `ReplaceRangeWithText` replaces an LSP range with text. For a
    /// content-mapped file, the LSP range is in the original document; text
    /// may be placed at any exact projection because it does not need
    /// formatting context.
    pub fn replace_range_with_text(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        lsproto_range: Range,
        text: &str,
    ) {
        let range = self.from_lsp_edit_range(nodes, source_file, lsproto_range);
        self.replace_text_range_with_text(nodes, source_file, range, text);
    }

    /// `ReplaceTextRangeWithText` replaces `text_range` in `source_file` with
    /// text. For a content-mapped file, `get_changes` maps the range back to
    /// the original document and drops the file if the edit cannot be
    /// represented there.
    pub fn replace_text_range_with_text(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        text_range: TextRange,
        text: &str,
    ) {
        let _ = self.borrow_nodes(nodes, source_file);
        self.changes.add(
            source_file,
            TrackerEdit {
                kind: TrackerEditKind::Text,
                range: text_range,
                new_text: text.to_string(),
                node: NodeId::NONE,
                nodes: Vec::new(),
                options: NodeOptions::default(),
            },
        );
    }

    /// `ReplaceRangeWithNodes` replaces `text_range` in `source_file` with
    /// `new_nodes`.
    pub fn replace_range_with_nodes(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        text_range: TextRange,
        new_nodes: Vec<NodeId>,
        options: NodeOptions,
    ) {
        if new_nodes.len() == 1 {
            self.replace_range(nodes, source_file, text_range, new_nodes[0], options);
            return;
        }
        let _ = self.borrow_nodes(nodes, source_file);
        self.changes.add(
            source_file,
            TrackerEdit {
                kind: TrackerEditKind::ReplaceWithMultipleNodes,
                range: text_range,
                nodes: new_nodes,
                options,
                new_text: String::new(),
                node: NodeId::NONE,
            },
        );
    }

    /// `insertTextAt` inserts text at an offset in `source_file`.
    pub(crate) fn insert_text_at(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        pos: TextPos,
        text: &str,
    ) {
        self.replace_text_range_with_text(nodes, source_file, TextRange::new(pos, pos), text);
    }

    /// `InsertText` inserts text at an LSP position.
    pub fn insert_text(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        pos: Position,
        text: &str,
    ) {
        self.replace_range_with_text(
            nodes,
            source_file,
            Range {
                start: pos,
                end: pos,
            },
            text,
        );
    }

    /// `InsertNodeAt`.
    pub fn insert_node_at(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        pos: TextPos,
        new_node: NodeId,
        options: NodeOptions,
    ) {
        self.replace_range(
            nodes,
            source_file,
            TextRange::new(pos, pos),
            new_node,
            options,
        );
    }

    /// `InsertNodesAt`.
    pub fn insert_nodes_at(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        pos: TextPos,
        new_nodes: Vec<NodeId>,
        options: NodeOptions,
    ) {
        self.replace_range_with_nodes(
            nodes,
            source_file,
            TextRange::new(pos, pos),
            new_nodes,
            options,
        );
    }

    /// `InsertNodeAfter`.
    pub fn insert_node_after(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        after: NodeId,
        new_node: NodeId,
    ) {
        let end_position = self.end_pos_for_insert_node_after(nodes, source_file, after, new_node);
        let options = self.get_insert_node_after_options(nodes, source_file, after);
        self.insert_node_at(nodes, source_file, end_position, new_node, options);
    }

    /// `InsertNodesAfter`.
    pub fn insert_nodes_after(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        after: NodeId,
        new_nodes: Vec<NodeId>,
    ) {
        let end_position =
            self.end_pos_for_insert_node_after(nodes, source_file, after, new_nodes[0]);
        let options = self.get_insert_node_after_options(nodes, source_file, after);
        self.insert_nodes_at(nodes, source_file, end_position, new_nodes, options);
    }

    /// `InsertNodeBefore`.
    pub fn insert_node_before(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        before: NodeId,
        new_node: NodeId,
        blank_line_between: bool,
        leading_trivia_option: LeadingTriviaOption,
    ) {
        let pos = self.get_adjusted_start_position(
            nodes,
            source_file,
            before,
            leading_trivia_option,
            false,
        );
        let options =
            self.get_options_for_insert_node_before(nodes, before, new_node, blank_line_between);
        self.insert_node_at(nodes, source_file, pos, new_node, options);
    }

    /// `TryInsertTypeAnnotation` inserts a type annotation after the
    /// appropriate position on a node (after the close paren for
    /// function-like, after the name/exclamation/question for variable-like).
    /// Returns true if successful.
    pub fn try_insert_type_annotation(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        type_node: NodeId,
    ) -> bool {
        let mut n = self.borrow_nodes(nodes, source_file);
        let end_node = if ast::is_function_like(Some(node), &n) {
            match astnav::find_child_of_kind(&mut n, source_file, node, Kind::CloseParenToken) {
                Some(t) => Some(t),
                None => {
                    if !ast::is_arrow_function(&n[node]) {
                        return false;
                    }
                    // If no `)`, is an arrow function `x => x`, so use the end
                    // of the first parameter.
                    let params = n[node].parameters();
                    match params {
                        Some(p) if !p.is_empty() => Some(p[0]),
                        _ => return false,
                    }
                }
            }
        } else {
            let end_node = match n[node].kind {
                Kind::VariableDeclaration => n[node].as_variable_declaration().exclamation_token,
                Kind::PropertySignature => {
                    n[node]
                        .as_property_signature_declaration()
                        .named_member_base
                        .postfix_token
                }
                Kind::PropertyDeclaration => {
                    n[node]
                        .as_property_declaration()
                        .named_member_base
                        .postfix_token
                }
                Kind::Parameter => n[node].as_parameter_declaration().question_token,
                _ => None,
            };
            match end_node {
                Some(t) => Some(t),
                None => n[node].name(),
            }
        };
        let Some(end_node) = end_node else {
            return false;
        };
        let end = n[end_node].end();
        drop(n);
        self.insert_node_at(
            nodes,
            source_file,
            end,
            type_node,
            NodeOptions {
                prefix: ": ".to_string(),
                ..Default::default()
            },
        );
        true
    }

    /// `ParenthesizeArrowParameters` wraps the parameters of a paren-less
    /// arrow function in `(` and `)`. This is a no-op if the arrow function
    /// already has parens.
    pub fn parenthesize_arrow_parameters(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        arrow_func: NodeId,
    ) {
        let mut n = self.borrow_nodes(nodes, source_file);
        if astnav::find_child_of_kind(&mut n, source_file, arrow_func, Kind::CloseParenToken)
            .is_some()
        {
            return;
        }
        let params = n[arrow_func].parameters().map(|p| p.to_vec());
        let Some(params) = params.filter(|p| !p.is_empty()) else {
            return;
        };
        let first_param = params[0];
        let last_param = params[params.len() - 1];
        let start_pos = astnav::get_start_of_node(&mut n, source_file, first_param, false);
        let last_end = n[last_param].end();
        drop(n);
        self.insert_text_at(nodes, source_file, start_pos, "(");
        self.insert_text_at(nodes, source_file, last_end, ")");
    }

    /// `InsertModifierBefore` inserts a modifier token (like 'type') before a
    /// node with a trailing space.
    pub fn insert_modifier_before(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        modifier: Kind,
        before: NodeId,
    ) {
        let mut n = self.borrow_nodes(nodes, source_file);
        let pos = astnav::get_start_of_node(&mut n, source_file, before, false);
        let token = self.node_factory(source_file).new_token(&mut n, modifier);
        n[token].loc = TextRange::new(pos, pos);
        n[token].parent = n[before].parent;
        drop(n);
        self.insert_node_at(
            nodes,
            source_file,
            pos,
            token,
            NodeOptions {
                suffix: " ".to_string(),
                ..Default::default()
            },
        );
    }

    /// `Delete` queues a node for deletion with smart handling of list items,
    /// imports, etc. The actual deletion happens in
    /// `finish_delete_declarations` during `get_changes`.
    pub fn delete(&mut self, nodes: &Rc<ArenaCell>, source_file: NodeId, node: NodeId) {
        let _ = self.borrow_nodes(nodes, source_file);
        self.deleted_nodes.push(DeletedNode { source_file, node });
    }

    /// `DeleteRange` deletes a text range from the source file.
    pub fn delete_range(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        text_range: TextRange,
    ) {
        self.replace_text_range_with_text(nodes, source_file, text_range, "");
    }

    /// `DeleteNode` deletes a node immediately with specified trivia options.
    /// Stop! Consider using `delete` instead, which has logic for deleting
    /// nodes from delimited lists.
    pub fn delete_node(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        leading_trivia: LeadingTriviaOption,
        trailing_trivia: TrailingTriviaOption,
    ) {
        let range = self.get_adjusted_range(
            nodes,
            source_file,
            node,
            node,
            leading_trivia,
            trailing_trivia,
        );
        self.replace_text_range_with_text(nodes, source_file, range, "");
    }

    /// `DeleteNodeRange` deletes a range of nodes with specified trivia
    /// options.
    pub fn delete_node_range(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        start_node: NodeId,
        end_node: NodeId,
        leading_trivia: LeadingTriviaOption,
        trailing_trivia: TrailingTriviaOption,
    ) {
        let start_position =
            self.get_adjusted_start_position(nodes, source_file, start_node, leading_trivia, false);
        let end_position =
            self.get_adjusted_end_position(nodes, source_file, end_node, trailing_trivia);
        self.replace_text_range_with_text(
            nodes,
            source_file,
            TextRange::new(start_position, end_position),
            "",
        );
    }

    /// `finishDeleteDeclarations` processes all queued deletions with smart
    /// handling for lists and trailing commas.
    pub(crate) fn finish_delete_declarations(&mut self) {
        let mut deleted_nodes_in_lists: FxHashMap<NodeId, bool> = FxHashMap::default();

        for i in 0..self.deleted_nodes.len() {
            let deleted_source_file = self.deleted_nodes[i].source_file;
            let deleted_node = self.deleted_nodes[i].node;
            // Skip if this node is contained within another deleted node
            let mut is_contained = false;
            for j in 0..self.deleted_nodes.len() {
                let other = &self.deleted_nodes[j];
                if other.source_file == deleted_source_file && other.node != deleted_node {
                    let n = self.nodes_of(deleted_source_file);
                    if range_contains_range_exclusive(n[other.node].loc, n[deleted_node].loc) {
                        is_contained = true;
                        break;
                    }
                }
            }
            if is_contained {
                continue;
            }
            crate::change::delete::delete_declaration(
                self,
                &mut deleted_nodes_in_lists,
                deleted_source_file,
                deleted_node,
            );
        }

        // Handle trailing commas for last elements in lists
        let list_nodes: Vec<NodeId> = deleted_nodes_in_lists.keys().copied().collect();
        for node in list_nodes {
            let Some(source_file) = self.source_file_of(node) else {
                continue;
            };
            let Some(handle) = self
                .arena_handles
                .get(&(source_file.file_index() as u32))
                .cloned()
            else {
                continue;
            };
            let start_of_removed = {
                let mut n = handle.borrow_mut();
                let list = format::get_containing_list(node, source_file, &mut n);
                let mut result = None;
                if let Some(list) = list {
                    if Some(node) == list.nodes.last().copied() {
                        for i in (0..list.nodes.len().saturating_sub(1)).rev() {
                            if !deleted_nodes_in_lists.contains_key(&list.nodes[i]) {
                                result = Some((n[list.nodes[i]].end(), list.nodes[i + 1]));
                                break;
                            }
                        }
                    }
                }
                result
            };
            if let Some((start, removed)) = start_of_removed {
                let end = self.start_position_to_delete_node_in_list(&handle, source_file, removed);
                self.replace_text_range_with_text(
                    &handle,
                    source_file,
                    TextRange::new(start, end),
                    "",
                );
            }
        }
    }

    /// PORT(addition): borrow `file`'s arena without re-registering — for
    /// read-only inspections in `finish_*` where the arena handle is already
    /// recorded.
    pub(crate) fn nodes_of(&self, file: NodeId) -> Rc<ast::NodeArenaBuf> {
        self.arena_handles[&(file.file_index() as u32)].snapshot()
    }

    /// PORT(addition): clone the registered arena `Rc` for `file`'s
    /// `file_index`. Panics if no tracker method has yet touched the file —
    /// every public entry point that registers an edit registers the handle
    /// first.
    pub(crate) fn arena_handle(&self, file: NodeId) -> Rc<ArenaCell> {
        self.arena_handles[&(file.file_index() as u32)].clone()
    }

    /// `ast.GetSourceFileOfNode(node)` — walks `parent` links to the
    /// `Kind::SourceFile` root.
    ///
    /// PORT: needs the arena for `node`'s `file_index`; consults
    /// `arena_handles` so it works for any tracked file.
    pub(crate) fn source_file_of(&self, node: NodeId) -> Option<NodeId> {
        let nodes = self.arena_handles.get(&(node.file_index() as u32))?.clone();
        let nodes = nodes.snapshot();
        ast::get_source_file_of_node(Some(node), &nodes)
    }

    /// `endPosForInsertNodeAfter`.
    pub(crate) fn end_pos_for_insert_node_after(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        after: NodeId,
        new_node: NodeId,
    ) -> TextPos {
        let mut n = self.borrow_nodes(nodes, source_file);
        let after_end = n[after].end();
        let text_len = n[source_file].as_source_file().text().len() as i32;
        let needs_semi = need_semicolon_between(&n, after, new_node)
            && after_end > 0
            && after_end <= text_len
            && n[source_file].as_source_file().text().as_bytes()[(after_end - 1) as usize] != b';';
        if needs_semi {
            // check if previous statement ends with semicolon
            // if not - insert semicolon to preserve the code from changing
            // the meaning due to ASI
            let semicolon = self
                .node_factory(source_file)
                .new_token(&mut n, Kind::SemicolonToken);
            n[semicolon].loc = TextRange::new(after_end, after_end);
            n[semicolon].parent = n[after].parent;
            drop(n);
            self.replace_range(
                nodes,
                source_file,
                TextRange::new(after_end, after_end),
                semicolon,
                NodeOptions::default(),
            );
        } else {
            drop(n);
        }
        self.get_adjusted_end_position(nodes, source_file, after, TrailingTriviaOption::None)
    }

    /// `InsertNodeInListAfter`.
    ///
    /// This function should be used to insert nodes in lists when nodes don't
    /// carry separators as the part of the node range, i.e. arguments in
    /// arguments lists, parameters in parameter lists etc.
    /// Note that separators are part of the node in statements and class
    /// elements.
    pub fn insert_node_in_list_after(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        after: NodeId,
        new_node: NodeId,
        containing_list: Option<&NodeList>,
    ) {
        let mut n = self.borrow_nodes(nodes, source_file);
        let containing_list = match containing_list.cloned() {
            Some(l) => Some(l),
            None => format::get_containing_list(after, source_file, &mut n),
        };
        let Some(containing_list) = containing_list else {
            // Debug.fail("node is not a list element")
            return;
        };
        let index = match containing_list.nodes.iter().position(|&x| x == after) {
            Some(i) => i,
            None => return,
        };
        let end = n[after].end();
        if index != containing_list.nodes.len() - 1 {
            // any element except the last one
            // use next sibling as an anchor
            let next_token = astnav::get_token_at_position(&mut n, source_file, end);
            if let Some(next_token) = next_token {
                if is_separator(&n, after, next_token) {
                    // for list
                    // a, b, c
                    // create change for adding 'e' after 'a' as
                    // - find start of next element after a (it is b)
                    // - use next element start as start and end position in final change
                    // - build text of change by formatting the text of node + whitespace trivia of b
                    //
                    // in multiline case it will work as
                    //   a,
                    //   b,
                    //   c,
                    // result - '*' denotes leading trivia that will be inserted after new text (displayed as '#')
                    //   a,
                    //   insertedtext<separator>#
                    // ###b,
                    //   c,
                    let next_node = containing_list.nodes[index + 1];
                    let start_pos = scanner::skip_trivia_ex(
                        n[source_file].as_source_file().text(),
                        n[next_node].pos(),
                        Some(&scanner::SkipTriviaOptions {
                            stop_after_line_break: false,
                            stop_at_comments: true,
                            ..Default::default()
                        }),
                    );
                    // write separator and leading trivia of the next element as suffix
                    let suffix = format!(
                        "{}{}",
                        scanner::token_to_string(n[next_token].kind),
                        &n[source_file].as_source_file().text()
                            [n[next_token].end() as usize..start_pos as usize]
                    );
                    drop(n);
                    self.insert_nodes_at(
                        nodes,
                        source_file,
                        start_pos,
                        vec![new_node],
                        NodeOptions {
                            suffix,
                            ..Default::default()
                        },
                    );
                }
            }
            return;
        }
        drop(n);

        let after_start = {
            let mut n = self.borrow_nodes(nodes, source_file);
            astnav::get_start_of_node(&mut n, source_file, after, false)
        };
        let after_start_line_position =
            format::get_line_start_position_for_position(after_start, source_file, &nodes.snapshot());

        // insert element after the last element in the list that has more than one item
        // pick the element preceding the after element to:
        // - pick the separator
        // - determine if list is a multiline
        let mut multiline_list = false;
        // if list has only one element then we'll format is as multiline if node has comment in trailing trivia, or as singleline otherwise
        // i.e. var x = 1 // this is x
        //     | new element will be inserted at this position
        let mut separator = Kind::CommaToken; // SyntaxKind.CommaToken | SyntaxKind.SemicolonToken
        {
            let mut n = self.borrow_nodes(nodes, source_file);
            if containing_list.nodes.len() != 1 {
                // otherwise, if list has more than one element, pick separator from the list
                let after_pos = n[after].pos();
                let token_before_insert_position =
                    astnav::find_preceding_token(&mut n, source_file, after_pos);
                separator = match token_before_insert_position {
                    Some(t) if is_separator(&n, after, t) => n[t].kind,
                    _ => Kind::CommaToken,
                };
                // determine if list is multiline by checking lines of after element and element that precedes it.
                let after_minus_one_start = astnav::get_start_of_node(
                    &mut n,
                    source_file,
                    containing_list.nodes[index - 1],
                    false,
                );
                let after_minus_one_start_line_position =
                    format::get_line_start_position_for_position(
                        after_minus_one_start,
                        source_file,
                        &n,
                    );
                multiline_list = after_minus_one_start_line_position != after_start_line_position;
            }
        }
        {
            let n = nodes.snapshot();
            let text = n[source_file].as_source_file().text();
            if has_comments_before_line_break(text, end)
                || !positions_are_on_same_line(
                    containing_list.pos(),
                    containing_list.end(),
                    source_file,
                    &n,
                )
            {
                // in this case we'll always treat containing list as multiline
                multiline_list = true;
            }
        }
        if multiline_list {
            let mut n = self.borrow_nodes(nodes, source_file);
            // insert separator immediately following the 'after' node to preserve comments in trailing trivia
            let separator_token = self.node_factory(source_file).new_token(&mut n, separator);
            let separator_string = scanner::token_to_string(separator).to_string();
            n[separator_token].loc = TextRange::new(end, end + separator_string.len() as i32);
            n[separator_token].parent = n[after].parent;
            drop(n);
            self.replace_range(
                nodes,
                source_file,
                TextRange::new(end, end),
                separator_token,
                NodeOptions::default(),
            );
            // use the same indentation as 'after' item
            let indentation = format::find_first_non_whitespace_column(
                after_start_line_position,
                after_start,
                source_file,
                &self.format_settings,
                &nodes.snapshot(),
            );
            // insert element before the line break on the line that contains 'after' element
            let mut insert_pos = scanner::skip_trivia_ex(
                nodes.snapshot()[source_file].as_source_file().text(),
                end,
                Some(&scanner::SkipTriviaOptions {
                    stop_after_line_break: true,
                    stop_at_comments: false,
                    ..Default::default()
                }),
            );
            // find position before "\n" or "\r\n"
            {
                let n = nodes.snapshot();
                let text = n[source_file].as_source_file().text().as_bytes();
                while insert_pos != end
                    && stringutil::is_line_break(text[(insert_pos - 1) as usize] as char)
                {
                    insert_pos -= 1;
                }
            }
            self.replace_range(
                nodes,
                source_file,
                TextRange::new(insert_pos, insert_pos),
                new_node,
                NodeOptions {
                    indentation: Some(indentation),
                    prefix: self.new_line.clone(),
                    ..Default::default()
                },
            );
        } else {
            let separator_string = scanner::token_to_string(separator);
            let prefix = format!("{} ", separator_string);
            self.replace_range(
                nodes,
                source_file,
                TextRange::new(end, end),
                new_node,
                NodeOptions {
                    prefix,
                    ..Default::default()
                },
            );
        }
    }

    /// `InsertImportSpecifierAtIndex` inserts a new import specifier at the
    /// specified index in a NamedImports list.
    pub fn insert_import_specifier_at_index(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        new_specifier: NodeId,
        named_imports: NodeId,
        index: usize,
    ) {
        let (elements, named_imports_parent_parent) = {
            let n = nodes.snapshot();
            (
                n[named_imports]
                    .as_named_imports()
                    .elements
                    .as_ref()
                    .map(|e| e.nodes.to_vec())
                    .unwrap_or_default(),
                n[named_imports].parent.and_then(|p| n[p].parent),
            )
        };

        let prev_specifier = if index > 0 && index - 1 < elements.len() {
            Some(elements[index - 1])
        } else {
            None
        };
        if let Some(prev_specifier) = prev_specifier {
            self.insert_node_in_list_after(nodes, source_file, prev_specifier, new_specifier, None);
        } else {
            let blank_line_between = {
                let mut n = self.borrow_nodes(nodes, source_file);
                let a = astnav::get_start_of_node(&mut n, source_file, elements[0], false);
                let b = match named_imports_parent_parent {
                    Some(p) => astnav::get_start_of_node(&mut n, source_file, p, false),
                    None => a,
                };
                !positions_are_on_same_line(a, b, source_file, &n)
            };
            self.insert_node_before(
                nodes,
                source_file,
                elements[0],
                new_specifier,
                blank_line_between,
                LeadingTriviaOption::None,
            );
        }
    }

    /// `InsertAtTopOfFile`.
    pub fn insert_at_top_of_file(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        insert: Vec<NodeId>,
        blank_line_between: bool,
    ) {
        if insert.is_empty() {
            return;
        }

        let mut pos = self.get_insertion_position_at_source_file_top(nodes, source_file);
        let mut original_pos = pos;
        // A content mapper may synthesize a header. Advance to the first writable segment so the insertion
        // maps exactly to the original file, and use its original position when deciding leading trivia.
        {
            let n = nodes.snapshot();
            if let Some(span_map) = n[source_file].as_source_file().span_map() {
                for segment in spanmap::SpanMap::segments(Some(&*span_map)) {
                    if segment.kind != spanmap::Kind::Verbatim || segment.virtual_end <= pos {
                        continue;
                    }
                    if segment.virtual_start > pos {
                        pos = segment.virtual_start;
                    }
                    original_pos = segment.original_start + (pos - segment.virtual_start);
                    break;
                }
            }
        }
        let mut options = NodeOptions::default();
        if original_pos != 0 {
            options.prefix = self.new_line.clone();
        }
        {
            let n = nodes.snapshot();
            let text = n[source_file].as_source_file().text();
            if text.is_empty()
                || pos >= text.len() as i32
                || !stringutil::is_line_break(text.as_bytes()[pos as usize] as char)
            {
                options.suffix = self.new_line.clone();
            }
        }
        if blank_line_between {
            options.suffix += &self.new_line;
        }

        if insert.len() == 1 {
            self.insert_node_at(nodes, source_file, pos, insert[0], options);
        } else {
            self.insert_nodes_at(nodes, source_file, pos, insert, options);
        }
    }

    /// `InsertMemberAtStart`.
    pub fn insert_member_at_start(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        new_element: NodeId,
    ) {
        self.insert_node_at_start_worker(nodes, source_file, node, new_element);
    }

    /// `insertNodeAtStartWorker`.
    fn insert_node_at_start_worker(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        new_element: NodeId,
    ) {
        let mut indentation =
            self.try_compute_indentation_from_existing_members(nodes, source_file, node);
        if indentation < 0 {
            indentation = self.try_compute_indentation_for_new_member(nodes, source_file, node);
        }

        let members = get_members_or_properties(&nodes.snapshot(), node);
        let Some(members) = members else {
            return;
        };
        let pos = members.pos();
        let options =
            self.get_insert_node_at_start_insert_options(nodes, source_file, node, indentation);
        self.insert_node_at(nodes, source_file, pos, new_element, options);
    }

    /// `tryComputeIndentationForNewMember`.
    fn try_compute_indentation_for_new_member(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
    ) -> i32 {
        let mut n = self.borrow_nodes(nodes, source_file);
        let node_start = astnav::get_start_of_node(&mut n, source_file, node, false);
        let line_start = format::get_line_start_position_for_position(node_start, source_file, &n);
        let text = n[source_file].as_source_file().text().to_string();

        let mut tab_size = self.format_settings.editor_settings.tab_size;
        if tab_size <= 0 {
            tab_size = 4;
        }

        let mut indent_size = self.format_settings.editor_settings.indent_size;
        if indent_size <= 0 {
            indent_size = 4;
        }
        find_indentation_column(&text, line_start, node_start, tab_size).max(0) + indent_size
    }

    /// `tryComputeIndentationFromExistingMembers`.
    fn try_compute_indentation_from_existing_members(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
    ) -> i32 {
        let mut n = self.borrow_nodes(nodes, source_file);
        let members = get_members_or_properties(&n, node);
        let Some(members) = members else {
            return -1;
        };

        let mut indentation = -1;
        let text = n[source_file].as_source_file().text().to_string();
        let mut tab_size = self.format_settings.editor_settings.tab_size;
        let mut last = node;
        if tab_size <= 0 {
            tab_size = 4;
        }

        for &member in &members.nodes {
            if member == NodeId::NONE {
                continue;
            }
            if range_start_positions_are_on_same_line(&n, n[last].loc, n[member].loc, source_file) {
                return -1;
            }

            let member_start = astnav::get_start_of_node(&mut n, source_file, member, false);
            let line_start =
                format::get_line_start_position_for_position(member_start, source_file, &n);
            let column = find_indentation_column(&text, line_start, member_start, tab_size);
            if column < 0 {
                return -1;
            }

            if indentation >= 0 {
                if indentation != column {
                    return -1;
                }
                last = member;
                continue;
            }

            indentation = column;
            last = member;
        }

        indentation
    }

    /// `getInsertNodeAfterOptions`.
    fn get_insert_node_after_options(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
    ) -> NodeOptions {
        let new_line_char = self.new_line.clone();
        let n = nodes.snapshot();
        let mut options = match n[node].kind {
            Kind::Parameter => NodeOptions::default(),
            Kind::ClassDeclaration | Kind::ModuleDeclaration => NodeOptions {
                prefix: new_line_char.clone(),
                suffix: new_line_char.clone(),
                ..Default::default()
            },
            Kind::VariableDeclaration | Kind::StringLiteral | Kind::Identifier => NodeOptions {
                prefix: ", ".to_string(),
                ..Default::default()
            },
            Kind::PropertyAssignment => NodeOptions {
                suffix: format!(",{}", new_line_char),
                ..Default::default()
            },
            Kind::ExportKeyword => NodeOptions {
                prefix: " ".to_string(),
                ..Default::default()
            },
            _ => {
                if !(ast::is_statement(&n[node], &n) || ast::is_class_or_type_element(&n[node])) {
                    // Else we haven't handled this kind of node yet -- add it
                    panic!(
                        "unimplemented node type {} in changeTracker.getInsertNodeAfterOptions",
                        n[node].kind_string()
                    );
                }
                NodeOptions {
                    suffix: new_line_char.clone(),
                    ..Default::default()
                }
            }
        };
        if n[node].end() == n[source_file].end() && ast::is_statement(&n[node], &n) {
            options.prefix = format!("{}{}", self.new_line, options.prefix);
        }
        options
    }

    /// `getOptionsForInsertNodeBefore`.
    fn get_options_for_insert_node_before(
        &mut self,
        nodes: &Rc<ArenaCell>,
        before: NodeId,
        inserted: NodeId,
        blank_line_between: bool,
    ) -> NodeOptions {
        let n = nodes.snapshot();
        let before_node = &n[before];
        if ast::is_statement(before_node, &n) || ast::is_class_or_type_element(before_node) {
            if blank_line_between {
                return NodeOptions {
                    suffix: format!("{}{}", self.new_line, self.new_line),
                    ..Default::default()
                };
            }
            return NodeOptions {
                suffix: self.new_line.clone(),
                ..Default::default()
            };
        } else if before_node.kind == Kind::VariableDeclaration {
            // insert `x = 1, ` into `const x = 1, y = 2;
            return NodeOptions {
                suffix: ", ".to_string(),
                ..Default::default()
            };
        } else if before_node.kind == Kind::Parameter {
            if n[inserted].kind == Kind::Parameter {
                return NodeOptions {
                    suffix: ", ".to_string(),
                    ..Default::default()
                };
            }
            return NodeOptions::default();
        } else if (before_node.kind == Kind::StringLiteral
            && before_node
                .parent
                .is_some_and(|p| n[p].kind == Kind::ImportDeclaration))
            || before_node.kind == Kind::NamedImports
        {
            return NodeOptions {
                suffix: ", ".to_string(),
                ..Default::default()
            };
        } else if before_node.kind == Kind::ImportSpecifier {
            let mut suffix = ",".to_string();
            if blank_line_between {
                suffix += &self.new_line;
            } else {
                suffix += " ";
            }
            return NodeOptions {
                suffix,
                ..Default::default()
            };
        }
        // We haven't handled this kind of node yet -- add it
        panic!(
            "unimplemented node type {} in changeTracker.getOptionsForInsertNodeBefore",
            before_node.kind_string()
        );
    }

    /// `getInsertNodeAtStartInsertOptions`.
    fn get_insert_node_at_start_insert_options(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        indentation: i32,
    ) -> NodeOptions {
        let has_previous_insertion = self.nodes_with_insertions_at_start.contains_key(&node);
        if !has_previous_insertion {
            self.nodes_with_insertions_at_start
                .insert(node, NodesInsertedAtStartState { node, source_file });
        }

        let n = nodes.snapshot();
        let members = get_members_or_properties(&n, node);
        let is_object_literal = ast::is_object_literal_expression(&n[node]);
        let is_json = ast::is_json_source_file(n[source_file].as_source_file());

        let has_members = members.is_some_and(|m| !m.nodes.is_empty());

        let insert_trailing_comma = is_object_literal && (has_members || !is_json);
        let insert_leading_comma =
            is_object_literal && is_json && !has_members && has_previous_insertion;

        let mut suffix = String::new();
        if insert_trailing_comma {
            suffix = ",".to_string();
        } else if ast::is_interface_declaration(&n[node]) && !has_members {
            suffix = ";".to_string();
        }

        let mut prefix = self.new_line.clone();
        if insert_leading_comma {
            prefix = format!(",{}", prefix);
        }

        NodeOptions {
            indentation: Some(indentation),
            prefix,
            suffix,
            ..Default::default()
        }
    }

    /// `finishNodesWithInsertionsAtStart`.
    pub(crate) fn finish_nodes_with_insertions_at_start(&mut self) {
        let states: Vec<NodesInsertedAtStartState> = self
            .nodes_with_insertions_at_start
            .values()
            .map(|s| NodesInsertedAtStartState {
                node: s.node,
                source_file: s.source_file,
            })
            .collect();
        for state in states {
            let handle = match self
                .arena_handles
                .get(&(state.source_file.file_index() as u32))
            {
                Some(h) => h.clone(),
                None => continue,
            };
            let (open_brace, close_brace) = {
                let mut n = handle.borrow_mut();
                let open_brace = astnav::find_child_of_kind(
                    &mut n,
                    state.source_file,
                    state.node,
                    Kind::OpenBraceToken,
                );
                let Some(open_brace) = open_brace else {
                    continue;
                };
                let close_brace = astnav::find_child_of_kind(
                    &mut n,
                    state.source_file,
                    state.node,
                    Kind::CloseBraceToken,
                );
                let Some(close_brace) = close_brace else {
                    continue;
                };
                (open_brace, close_brace)
            };

            let (is_empty, is_single_line, open_end, close_end) = {
                let n = handle.borrow();
                let members = get_members_or_properties(&n, state.node);
                let is_empty = members.map_or(true, |m| m.nodes.is_empty());
                let is_single_line = positions_are_on_same_line(
                    n[open_brace].end(),
                    n[close_brace].end(),
                    state.source_file,
                    &n,
                );
                (
                    is_empty,
                    is_single_line,
                    n[open_brace].end(),
                    n[close_brace].end(),
                )
            };

            if is_empty && is_single_line && open_end != close_end - 1 {
                self.delete_range(
                    &handle,
                    state.source_file,
                    TextRange::new(open_end, close_end - 1),
                );
            }

            if is_single_line {
                let new_line = self.new_line.clone();
                self.insert_text_at(&handle, state.source_file, close_end - 1, &new_line);
            }
        }
    }
}

/// `getMembersOrProperties`.
pub(crate) fn get_members_or_properties(nodes: &[Node], node: NodeId) -> Option<NodeList> {
    if ast::is_object_literal_expression(&nodes[node]) {
        return nodes[node].property_list().cloned();
    }
    nodes[node].member_list().cloned()
}

/// `rangeContainsRangeExclusive`.
pub(crate) fn range_contains_range_exclusive(outer: TextRange, inner: TextRange) -> bool {
    outer.pos() < inner.pos() && inner.end() < outer.end()
}

/// `isSeparator`.
pub(crate) fn is_separator(nodes: &[Node], node: NodeId, candidate: NodeId) -> bool {
    nodes[node].parent.is_some()
        && (nodes[candidate].kind == Kind::CommaToken
            || (nodes[candidate].kind == Kind::SemicolonToken
                && nodes[node]
                    .parent
                    .is_some_and(|p| nodes[p].kind == Kind::ObjectLiteralExpression)))
}

/// `findIndentationColumn`.
pub(crate) fn find_indentation_column(
    text: &str,
    line_start: i32,
    member_start: i32,
    tab_size: i32,
) -> i32 {
    let mut column = 0i32;
    let bytes = text.as_bytes();
    let mut i = line_start;
    while i < member_start && (i as usize) < bytes.len() {
        let ch = bytes[i as usize] as char;

        if stringutil::is_line_break(ch) {
            return -1;
        }
        if stringutil::is_white_space_single_line(ch) {
            column = advance_indentation_column(column, ch, tab_size);
            i += 1;
            continue;
        }
        return column;
    }
    column
}

/// `advanceIndentationColumn`.
fn advance_indentation_column(column: i32, ch: char, tab_size: i32) -> i32 {
    if ch == '\t' {
        return column + tab_size - (column % tab_size);
    }
    column + 1
}

/// `positionsAreOnSameLine` (delete.go) — shared by tracker.rs and delete.rs.
pub(crate) fn positions_are_on_same_line(
    pos1: i32,
    pos2: i32,
    source_file: NodeId,
    nodes: &[Node],
) -> bool {
    format::get_line_start_position_for_position(pos1, source_file, nodes)
        == format::get_line_start_position_for_position(pos2, source_file, nodes)
}

/// `printer.RangeStartPositionsAreOnSameLine` — `pub(crate)` in the printer
/// crate, so it is reimplemented here over `skip_trivia` +
/// `get_line_start_position_for_position`.
pub(crate) fn range_start_positions_are_on_same_line(
    nodes: &[Node],
    range1: TextRange,
    range2: TextRange,
    source_file: NodeId,
) -> bool {
    // getStartPositionOfRange(r, sourceFile, /*includeComments*/ false)
    let start = |r: TextRange| {
        if r.pos() < 0 {
            return -1;
        }
        scanner::skip_trivia_ex(
            nodes[source_file].as_source_file().text(),
            r.pos(),
            Some(&scanner::SkipTriviaOptions {
                stop_at_comments: false,
                ..Default::default()
            }),
        )
    };
    positions_are_on_same_line(start(range1), start(range2), source_file, nodes)
}
