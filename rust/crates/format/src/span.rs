// Ported from tsc/internal/format/span.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::NodeFactoryHooks;
use tsc_ast::ast::{Node, NodeFactory, NodeList};
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::visitor::{NodeVisitor, NodeVisitorHooks, VisitorCx};
use tsc_astnav::tokens::{find_preceding_token, find_preceding_token_ex};
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_core::textchange::TextChange;
use tsc_lsutil::FormatCodeSettings;
use tsc_scanner::scanner::{get_token_pos_of_node, skip_trivia};
use tsc_stringutil::is_white_space_single_line;

use crate::api::{
    FormatRequestKind, get_format_code_settings_from_context, get_new_line_or_default_from_context,
};
use crate::context::{FormattingContext, with_token_start};
use crate::indent::{
    argument_starts_on_same_line_as_previous_argument,
    child_is_unindented_branch_of_conditional_expression,
    child_starts_on_the_same_line_with_else_in_if_statement, decode_rune_in_string,
    find_first_non_whitespace_character_and_column, find_first_non_whitespace_column,
    node_will_indent_child, should_indent_child_node,
};
use crate::rule::{
    RULE_ACTION_DELETE_SPACE, RULE_ACTION_DELETE_TOKEN, RULE_ACTION_INSERT_NEW_LINE,
    RULE_ACTION_INSERT_SPACE, RULE_ACTION_INSERT_TRAILING_SEMICOLON,
    RULE_ACTION_STOP_PROCESSING_SPACE_ACTIONS, RuleFlags, RuleImpl,
};
use crate::rulesmap::get_rules;
use crate::scanner::{FormattingScanner, TextRangeWithKind, TokenInfo};
use crate::util::get_close_token_for_open_token;
use crate::util::get_open_token_for_list;
use crate::util::{
    end_line_position, get_line_start_position_for_position, is_member_list_element,
    line_and_byte_offset_of_position, line_map, line_of_position,
};

/// `findEnclosingNode` — find node that fully contains given text range
pub(crate) fn find_enclosing_node(r: TextRange, source_file: NodeId, nodes: &[Node]) -> NodeId {
    fn find(n: NodeId, r: TextRange, source_file: NodeId, nodes: &[Node]) -> NodeId {
        let mut candidate: Option<NodeId> = None;
        nodes[n].for_each_child(nodes, &mut |c| {
            if nodes[c].flags.intersects(NodeFlags::REPARSED) {
                return false;
            }
            if r.contained_by(&with_token_start(c, source_file, nodes)) {
                candidate = Some(c);
                return true;
            }
            false
        });
        if let Some(candidate) = candidate {
            let result = find(candidate, r, source_file, nodes);
            if result != candidate {
                return result;
            }
        }

        n
    }
    find(source_file, r, source_file, nodes)
}

/**
 * Start of the original range might fall inside the comment - scanner will not yield appropriate results
 * This function will look for token that is located before the start of target range
 * and return its end as start position for the scanner.
 */
/// `getScanStartPosition`
pub(crate) fn get_scan_start_position(
    enclosing_node: NodeId,
    original_range: TextRange,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> i32 {
    let adjusted = with_token_start(enclosing_node, source_file, nodes);
    let start = adjusted.pos();
    if start == original_range.pos() && nodes[enclosing_node].end() == original_range.end() {
        return start;
    }

    // exclude JSDoc so the scan never starts inside a JSDoc comment
    let preceding_token = find_preceding_token_ex(
        nodes,
        source_file,
        original_range.pos(),
        None, /*startNode*/
        true, /*excludeJSDoc*/
    );
    let Some(preceding_token) = preceding_token else {
        // no preceding token found - start from the beginning of enclosing node
        return nodes[enclosing_node].pos();
    };

    // preceding token ends after the start of original range (i.e when originalRange.pos falls in the middle of literal)
    // start from the beginning of enclosingNode to handle the entire 'originalRange'
    if nodes[preceding_token].end() >= original_range.pos() {
        return nodes[enclosing_node].pos();
    }

    nodes[preceding_token].end()
}

/*
 * For cases like
 * if (a ||
 *     b ||$
 *     c) {...}
 * If we hit Enter at $ we want line '    b ||' to be indented.
 * Formatting will be applied to the last two lines.
 * Node that fully encloses these lines is binary expression 'a ||...'.
 * Initial indentation for this node will be 0.
 * Binary expressions don't introduce new indentation scopes, however it is possible
 * that some parent node on the same line does - like if statement in this case.
 * Note that we are considering parents only from the same line with initial node -
 * if parent is on the different line - its delta was already contributed
 * to the initial indentation.
 */
/// `getOwnOrInheritedDelta`
pub(crate) fn get_own_or_inherited_delta(
    n: Option<NodeId>,
    options: &FormatCodeSettings,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> i32 {
    let mut previous_line = -1;
    let mut child: Option<NodeId> = None;
    let mut n = n;
    while let Some(cur) = n {
        let line = line_of_position(
            nodes,
            source_file,
            with_token_start(cur, source_file, nodes).pos(),
        );
        if previous_line != -1 && line != previous_line {
            break;
        }

        if should_indent_child_node(options, cur, child, Some(source_file), false, nodes) {
            return options.editor_settings.indent_size; // !!! nil check???
        }

        previous_line = line;
        child = Some(cur);
        n = nodes[cur].parent;
    }
    0
}

/// `rangeHasNoErrors`
fn range_has_no_errors(_r: TextRange) -> bool {
    false
}

/// `prepareRangeContainsErrorFunction`
pub(crate) fn prepare_range_contains_error_function(
    errors: &[DiagnosticRef],
    original_range: TextRange,
) -> Box<dyn FnMut(TextRange) -> bool> {
    if errors.is_empty() {
        return Box::new(range_has_no_errors);
    }

    // pick only errors that fall in range
    let mut sorted: Vec<DiagnosticRef> = errors
        .iter()
        .filter(|d| original_range.overlaps(&tsc_ast::diagnostic::lock_diagnostic(d).loc()))
        .cloned()
        .collect();
    if sorted.is_empty() {
        return Box::new(range_has_no_errors);
    }
    sorted.sort_by(|a, b| {
        tsc_ast::diagnostic::lock_diagnostic(a)
            .pos()
            .cmp(&tsc_ast::diagnostic::lock_diagnostic(b).pos())
    });

    let mut index = 0usize;
    Box::new(move |r: TextRange| -> bool {
        // in current implementation sequence of arguments [r1, r2...] is monotonically increasing.
        // 'index' tracks the index of the most recent error that was checked.
        loop {
            if index >= sorted.len() {
                // all errors in the range were already checked -> no error in specified range
                return false;
            }

            let err = &sorted[index];

            if r.end() <= tsc_ast::diagnostic::lock_diagnostic(err).pos() {
                // specified range ends before the error referred by 'index' - no error in range
                return false;
            }

            if r.overlaps(&tsc_ast::diagnostic::lock_diagnostic(err).loc()) {
                // specified range overlaps with error range
                return true;
            }

            index += 1;
        }
    })
}

/// `type formatSpanWorker struct`
///
/// PORT: Go's mutable `*formatSpanWorker` methods become `&self` methods over
/// `Cell`/`RefCell` fields so the `visit_each_child` callbacks (which capture
/// an `Rc<FormatSpanWorker>`) may re-enter the worker without a second
/// `RefCell` borrow. `formattingScanner` is threaded as
/// `&RefCell<FormattingScanner>` because Go's `w.formattingScanner` pointer
/// has the same sharing/mutation shape.
pub(crate) struct FormatSpanWorker {
    pub(crate) ctx: Context,
    pub(crate) original_range: TextRange,
    pub(crate) enclosing_node: NodeId,
    pub(crate) initial_indentation: i32,
    pub(crate) delta: i32,
    #[allow(dead_code)] // Go keeps `requestKind` on the worker after seeding FormattingContext
    pub(crate) request_kind: FormatRequestKind,
    pub(crate) range_contains_error: RefCell<Box<dyn FnMut(TextRange) -> bool>>,
    pub(crate) source_file: NodeId,

    pub(crate) formatting_context: RefCell<FormattingContext>,

    edits: RefCell<Vec<TextChange>>,
    previous_range: Cell<TextRangeWithKind>,
    previous_range_trivia_end: Cell<i32>,
    previous_parent: Cell<Option<NodeId>>,
    previous_range_start_line: Cell<i32>,

    child_context_node: Cell<Option<NodeId>>,
    last_indented_line: Cell<i32>,
    indentation_on_last_indented_line: Cell<i32>,

    visiting_node: Cell<Option<NodeId>>,
    visiting_indenter: RefCell<Option<Rc<RefCell<DynamicIndenter>>>>,
    visiting_node_start_line: Cell<i32>,
    visiting_undecorated_node_start_line: Cell<i32>,

    current_rules: RefCell<Vec<&'static RuleImpl>>,
}

/// `newFormatSpanWorker`
#[allow(clippy::too_many_arguments)]
pub(crate) fn new_format_span_worker(
    ctx: Context,
    original_range: TextRange,
    enclosing_node: NodeId,
    initial_indentation: i32,
    delta: i32,
    request_kind: FormatRequestKind,
    range_contains_error: Box<dyn FnMut(TextRange) -> bool>,
    source_file: NodeId,
) -> FormatSpanWorker {
    let opt = get_format_code_settings_from_context(&ctx);
    FormatSpanWorker {
        ctx,
        original_range,
        enclosing_node,
        initial_indentation,
        delta,
        request_kind,
        range_contains_error: RefCell::new(range_contains_error),
        source_file,
        formatting_context: RefCell::new(FormattingContext::new(source_file, request_kind, opt)),
        edits: RefCell::new(Vec::new()),
        previous_range: Cell::new(TextRangeWithKind::default()),
        previous_range_trivia_end: Cell::new(0),
        previous_parent: Cell::new(None),
        previous_range_start_line: Cell::new(0),
        child_context_node: Cell::new(None),
        last_indented_line: Cell::new(-1),
        indentation_on_last_indented_line: Cell::new(-1),
        visiting_node: Cell::new(None),
        visiting_indenter: RefCell::new(None),
        visiting_node_start_line: Cell::new(0),
        visiting_undecorated_node_start_line: Cell::new(0),
        // increaseInsertionIndex should assert there are no more than 32 rules in a given bucket
        current_rules: RefCell::new(Vec::with_capacity(32)),
    }
}

/// `getNonDecoratorTokenPosOfNode`
fn get_non_decorator_token_pos_of_node(node: NodeId, file: Option<NodeId>, nodes: &[Node]) -> i32 {
    let mut last_decorator: Option<NodeId> = None;
    if tsc_ast::has_decorators(&nodes[node]) {
        last_decorator = nodes[node]
            .modifier_nodes()
            .and_then(|mods| {
                mods.iter()
                    .rev()
                    .find(|&&m| tsc_ast::is_decorator(&nodes[m]))
            })
            .copied();
    }
    let file = file.unwrap_or_else(|| {
        tsc_ast::get_source_file_of_node(Some(node), nodes).expect("source file")
    });
    let Some(last_decorator) = last_decorator else {
        return get_token_pos_of_node(node, nodes[file].as_source_file(), false, nodes);
    };
    skip_trivia(
        &nodes[file].as_source_file().text,
        nodes[last_decorator].end(),
    )
}

impl FormatSpanWorker {
    /// `(w *formatSpanWorker) execute`
    pub(crate) fn execute(
        w: &FormatSpanWorker,
        s: &RefCell<FormattingScanner<'_>>,
        nodes: &mut Vec<Node>,
    ) -> Vec<TextChange> {
        s.borrow_mut().advance();

        if s.borrow().is_on_token() {
            let start_line = line_of_position(
                nodes,
                w.source_file,
                with_token_start(w.enclosing_node, w.source_file, nodes).pos(),
            );
            let mut undecorated_start_line = start_line;
            if tsc_ast::has_decorators(&nodes[w.enclosing_node]) {
                undecorated_start_line = line_of_position(
                    nodes,
                    w.source_file,
                    get_non_decorator_token_pos_of_node(
                        w.enclosing_node,
                        Some(w.source_file),
                        nodes,
                    ),
                );
            }

            Self::process_node(
                w,
                s,
                nodes,
                w.enclosing_node,
                w.enclosing_node,
                start_line,
                undecorated_start_line,
                w.initial_indentation,
                w.delta,
            );
        }

        // Leading trivia items get attached to and processed with the token that proceeds them. If the
        // range ends in the middle of some leading trivia, the token that proceeds them won't be in the
        // range and thus won't get processed. So we process those remaining trivia items here.
        let remaining_trivia: Vec<TextRangeWithKind> =
            s.borrow().get_current_leading_trivia().to_vec();
        if !remaining_trivia.is_empty() {
            let opt = get_format_code_settings_from_context(&w.ctx);
            let mut indentation = w.initial_indentation;
            if node_will_indent_child(
                &w.formatting_context.borrow().options,
                w.enclosing_node,
                None,
                Some(w.source_file),
                false,
                nodes,
            ) {
                indentation += opt.editor_settings.indent_size; // !!! TODO: nil check???
            }

            w.indent_trivia_items(
                &remaining_trivia,
                indentation,
                true,
                &mut |nodes: &mut Vec<Node>, item: TextRangeWithKind| {
                    let (start_line, start_char) =
                        line_and_byte_offset_of_position(nodes, w.source_file, item.loc.pos());
                    w.process_range(
                        nodes,
                        item,
                        start_line,
                        start_char,
                        w.enclosing_node,
                        w.enclosing_node,
                        None,
                    );
                    w.insert_indentation(item.loc.pos(), indentation, false, nodes);
                },
                nodes,
            );

            if opt.editor_settings.trim_trailing_whitespace.is_true() {
                w.trim_trailing_whitespaces_for_remaining_range(&remaining_trivia, nodes);
            }
        }

        if w.previous_range.get() != TextRangeWithKind::new(0, 0, Kind::Unknown)
            && s.borrow().get_token_full_start() >= w.original_range.end()
        {
            // Formatting edits happen by looking at pairs of contiguous tokens (see `processPair`),
            // typically inserting or deleting whitespace between them. The recursive `processNode`
            // logic above bails out as soon as it encounters a token that is beyond the end of the
            // range we're supposed to format (or if we reach the end of the file). But this potentially
            // leaves out an edit that would occur *inside* the requested range but cannot be discovered
            // without looking at one token *beyond* the end of the range: consider the line `x = { }`
            // with a selection from the beginning of the line to the space inside the curly braces,
            // inclusive. We would expect a format-selection would delete the space (if rules apply),
            // but in order to do that, we need to process the pair ["{", "}"], but we stopped processing
            // just before getting there. This block handles this trailing edit.
            let mut token_info = TextRangeWithKind::new(0, 0, Kind::Unknown);
            if s.borrow().is_on_eof() {
                token_info = s.borrow().read_eof_token_range();
            } else if s.borrow().is_on_token() {
                token_info = s
                    .borrow_mut()
                    .read_token_info(w.enclosing_node, nodes)
                    .token;
            }

            if token_info.loc.pos() == w.previous_range_trivia_end.get() {
                // We need to check that tokenInfo and previousRange are contiguous: the `originalRange`
                // may have ended in the middle of a token, which means we will have stopped formatting
                // on that token, leaving `previousRange` pointing to the token before it, but already
                // having moved the formatting scanner (where we just got `tokenInfo`) to the next token.
                // If this happens, our supposed pair [previousRange, tokenInfo] actually straddles the
                // token that intersects the end of the range we're supposed to format, so the pair will
                // produce bogus edits if we try to `processPair`. Recall that the point of this logic is
                // to perform a trailing edit at the end of the selection range: but there can be no valid
                // edit in the middle of a token where the range ended, so if we have a non-contiguous
                // pair here, we're already done and we can ignore it.
                let mut parent = find_preceding_token(nodes, w.source_file, token_info.loc.end())
                    .and_then(|t| nodes[t].parent);
                if parent.is_none() {
                    parent = w.previous_parent.get();
                }
                let line = line_of_position(nodes, w.source_file, token_info.loc.pos());
                w.process_pair(
                    nodes,
                    token_info,
                    line,
                    parent.unwrap_or(NodeId::NONE),
                    w.previous_range.get(),
                    w.previous_range_start_line.get(),
                    w.previous_parent.get().unwrap_or(NodeId::NONE),
                    parent.unwrap_or(NodeId::NONE),
                    None,
                );
            }
        }

        std::mem::take(&mut *w.edits.borrow_mut())
    }

    /// `(w *formatSpanWorker) processChildNode`
    #[allow(clippy::too_many_arguments)]
    fn process_child_node(
        w: &FormatSpanWorker,
        s: &RefCell<FormattingScanner<'_>>,
        nodes: &mut Vec<Node>,
        node: NodeId,
        _indenter: Option<&Rc<RefCell<DynamicIndenter>>>,
        _node_start_line: i32,
        _undecorated_node_start_line: i32,
        child: NodeId,
        inherited_indentation: i32,
        parent: NodeId,
        parent_dynamic_indentation: Option<&Rc<RefCell<DynamicIndenter>>>,
        parent_start_line: i32,
        undecorated_parent_start_line: i32,
        is_list_item: bool,
        is_first_list_item: bool,
    ) -> i32 {
        debug_assert!(!tsc_ast::node_is_synthesized(&nodes[child]));

        let mut inherited_indentation = inherited_indentation;
        if tsc_ast::node_is_missing(Some(child), nodes)
            || nodes[child].flags.intersects(NodeFlags::REPARSED)
        {
            return inherited_indentation;
        }
        let child_start_pos =
            get_token_pos_of_node(child, nodes[w.source_file].as_source_file(), false, nodes);
        let child_start_line = line_of_position(nodes, w.source_file, child_start_pos);

        let mut undecorated_child_start_line = child_start_line;
        if tsc_ast::has_decorators(&nodes[child]) {
            undecorated_child_start_line = line_of_position(
                nodes,
                w.source_file,
                get_non_decorator_token_pos_of_node(child, Some(w.source_file), nodes),
            );
        }

        let is_error_member_list_element = nodes[child]
            .flags
            .intersects(NodeFlags::THIS_NODE_HAS_ERROR)
            && is_member_list_element(parent, child, nodes);
        // if child is a list item - try to get its indentation, only if parent is within the original range.
        let mut child_indentation_amount = -1;

        if !is_error_member_list_element
            && is_list_item
            && nodes[parent].loc.contained_by(&w.original_range)
        {
            child_indentation_amount = w.try_compute_indentation_for_list_item(
                child_start_pos,
                nodes[child].end(),
                parent_start_line,
                w.original_range,
                inherited_indentation,
                nodes,
            );
            if child_indentation_amount != -1 {
                inherited_indentation = child_indentation_amount;
            }
        }

        // child node is outside the target range - do not dive inside
        if !w.original_range.overlaps(&nodes[child].loc) {
            if nodes[child].end() < w.original_range.pos() {
                s.borrow_mut().skip_to_end_of(&nodes[child].loc);
            }
            return inherited_indentation;
        }

        if nodes[child].loc.len() == 0 {
            return inherited_indentation;
        }

        while s.borrow().is_on_token() && s.borrow().get_token_full_start() < w.original_range.end()
        {
            // proceed any parent tokens that are located prior to child.getStart()
            let token_info = s.borrow_mut().read_token_info(node, nodes);
            if token_info.token.loc.end() > w.original_range.end() {
                return inherited_indentation;
            }
            if token_info.token.loc.end() > child_start_pos {
                if token_info.token.loc.pos() > child_start_pos {
                    s.borrow_mut().skip_to_start_of(&nodes[child].loc);
                }
                // stop when formatting scanner advances past the beginning of the child
                break;
            }

            w.consume_token_and_advance_scanner(
                s,
                nodes,
                &token_info,
                node,
                parent_dynamic_indentation,
                node,
                false,
            );
        }

        if !s.borrow().is_on_token() || s.borrow().get_token_full_start() >= w.original_range.end()
        {
            return inherited_indentation;
        }

        if nodes[child].kind.is_token_kind() {
            // if child node is a token, it does not impact indentation, proceed it using parent indentation scope rules
            let token_info = s.borrow_mut().read_token_info(child, nodes);
            // JSX text shouldn't affect indenting
            if nodes[child].kind != Kind::JsxText {
                debug_assert!(
                    token_info.token.loc.end() == nodes[child].loc.end(),
                    "Token end is child end"
                );
                w.consume_token_and_advance_scanner(
                    s,
                    nodes,
                    &token_info,
                    node,
                    parent_dynamic_indentation,
                    child,
                    false,
                );
                return inherited_indentation;
            }
        }

        let mut effective_parent_start_line = undecorated_parent_start_line;
        if nodes[child].kind == Kind::Decorator {
            effective_parent_start_line = child_start_line;
        }
        let (child_indentation, delta) = if is_error_member_list_element {
            (
                w.get_current_indentation_at_position(child_start_pos, nodes),
                0,
            )
        } else {
            w.compute_indentation(
                nodes,
                child,
                child_start_line,
                child_indentation_amount,
                node,
                parent_dynamic_indentation,
                effective_parent_start_line,
            )
        };

        Self::process_node(
            w,
            s,
            nodes,
            child,
            w.child_context_node.get().unwrap_or(NodeId::NONE),
            child_start_line,
            undecorated_child_start_line,
            child_indentation,
            delta,
        );

        w.child_context_node.set(Some(node));

        if is_first_list_item
            && nodes[parent].kind == Kind::ArrayLiteralExpression
            && inherited_indentation == -1
        {
            inherited_indentation = child_indentation;
        }

        inherited_indentation
    }

    /// `(w *formatSpanWorker) processChildNodes`
    #[allow(clippy::too_many_arguments)]
    fn process_child_nodes(
        w: &FormatSpanWorker,
        s: &RefCell<FormattingScanner<'_>>,
        nodes: &mut Vec<Node>,
        node: NodeId,
        indenter: Option<&Rc<RefCell<DynamicIndenter>>>,
        node_start_line: i32,
        undecorated_node_start_line: i32,
        list: &NodeList,
        parent: NodeId,
        parent_start_line: i32,
        parent_dynamic_indentation: Option<&Rc<RefCell<DynamicIndenter>>>,
    ) {
        debug_assert!(!tsc_ast::position_is_synthesized(list.loc.pos()));
        debug_assert!(!tsc_ast::position_is_synthesized(list.loc.end()));

        let list_start_token = get_open_token_for_list(parent, list, nodes);

        let mut list_dynamic_indentation = parent_dynamic_indentation.cloned();
        let mut start_line = parent_start_line;

        // node range is outside the target range - do not dive inside
        if !w.original_range.overlaps(&list.loc) {
            if list.loc.end() < w.original_range.pos()
                && (list.nodes.is_empty()
                    || !nodes[list.nodes[0]].flags.intersects(NodeFlags::REPARSED))
            {
                s.borrow_mut().skip_to_end_of(&list.loc);
            }
            return;
        }

        if list_start_token != Kind::Unknown {
            // introduce a new indentation scope for lists (including list start and end tokens)
            while s.borrow().is_on_token()
                && s.borrow().get_token_full_start() < w.original_range.end()
            {
                let token_info = s.borrow_mut().read_token_info(parent, nodes);
                if token_info.token.loc.end() > list.loc.pos() {
                    // stop when formatting scanner moves past the beginning of node list
                    break;
                } else if token_info.token.kind == list_start_token {
                    // consume list start token
                    start_line = line_of_position(nodes, w.source_file, token_info.token.loc.pos());

                    w.consume_token_and_advance_scanner(
                        s,
                        nodes,
                        &token_info,
                        parent,
                        parent_dynamic_indentation,
                        parent,
                        false,
                    );

                    let indentation_on_list_start_token =
                        if w.indentation_on_last_indented_line.get() != -1 {
                            // scanner just processed list start token so consider last indentation as list indentation
                            // function foo(): { // last indentation was 0, list item will be indented based on this value
                            //   foo: number;
                            // }: {};
                            w.indentation_on_last_indented_line.get()
                        } else {
                            w.get_current_indentation_at_position(token_info.token.loc.pos(), nodes)
                        };

                    list_dynamic_indentation = Some(
                        w.get_dynamic_indentation(
                            parent,
                            parent_start_line,
                            indentation_on_list_start_token,
                            w.formatting_context
                                .borrow()
                                .options
                                .editor_settings
                                .indent_size,
                        ),
                    );
                } else {
                    // consume any tokens that precede the list as child elements of 'node' using its indentation scope
                    w.consume_token_and_advance_scanner(
                        s,
                        nodes,
                        &token_info,
                        parent,
                        parent_dynamic_indentation,
                        parent,
                        false,
                    );
                }
            }
        }

        let mut inherited_indentation = -1;
        for i in 0..list.nodes.len() {
            let child = list.nodes[i];
            inherited_indentation = Self::process_child_node(
                w,
                s,
                nodes,
                node,
                indenter,
                node_start_line,
                undecorated_node_start_line,
                child,
                inherited_indentation,
                node,
                list_dynamic_indentation.as_ref(),
                start_line,
                start_line,
                true,
                i == 0,
            );
        }

        let list_end_token = get_close_token_for_open_token(list_start_token);
        if list_end_token != Kind::Unknown
            && s.borrow().is_on_token()
            && s.borrow().get_token_full_start() < w.original_range.end()
        {
            let mut token_info = s.borrow_mut().read_token_info(parent, nodes);
            if token_info.token.kind == Kind::CommaToken {
                // consume the comma
                w.consume_token_and_advance_scanner(
                    s,
                    nodes,
                    &token_info,
                    parent,
                    list_dynamic_indentation.as_ref(),
                    parent,
                    false,
                );
                if s.borrow().is_on_token() {
                    token_info = s.borrow_mut().read_token_info(parent, nodes);
                } else {
                    return;
                }
            }

            // consume the list end token only if it is still belong to the parent
            // there might be the case when current token matches end token but does not considered as one
            // function (x: function) <--
            // without this check close paren will be interpreted as list end token for function expression which is wrong
            if token_info.token.kind == list_end_token
                && token_info.token.loc.contained_by(&nodes[parent].loc)
            {
                // consume list end token
                w.consume_token_and_advance_scanner(
                    s,
                    nodes,
                    &token_info,
                    parent,
                    list_dynamic_indentation.as_ref(),
                    parent, /*isListEndToken*/
                    true,
                );
            }
        }
    }

    /// `(w *formatSpanWorker) executeProcessNodeVisitor`
    fn execute_process_node_visitor(
        w: &FormatSpanWorker,
        s: &RefCell<FormattingScanner<'_>>,
        nodes: &mut Vec<Node>,
        node: NodeId,
        indenter: Option<Rc<RefCell<DynamicIndenter>>>,
        node_start_line: i32,
        undecorated_node_start_line: i32,
    ) {
        let old_node = w.visiting_node.get();
        let old_indenter = w.visiting_indenter.borrow().clone();
        let old_start = w.visiting_node_start_line.get();
        let old_undecorated_start = w.visiting_undecorated_node_start_line.get();
        w.visiting_node.set(Some(node));
        *w.visiting_indenter.borrow_mut() = indenter;
        w.visiting_node_start_line.set(node_start_line);
        w.visiting_undecorated_node_start_line
            .set(undecorated_node_start_line);

        let visitor = NodeVisitor::new(
            Box::new(
                move |_v: &NodeVisitor, cx: &mut VisitorCx, child: NodeId| -> Option<NodeId> {
                    let (
                        visiting_node,
                        visiting_indenter,
                        visiting_node_start_line,
                        visiting_undecorated_node_start_line,
                    ) = {
                        (
                            w.visiting_node.get(),
                            w.visiting_indenter.borrow().clone(),
                            w.visiting_node_start_line.get(),
                            w.visiting_undecorated_node_start_line.get(),
                        )
                    };
                    Self::process_child_node(
                        w,
                        s,
                        cx.nodes,
                        visiting_node.unwrap_or(NodeId::NONE),
                        visiting_indenter.as_ref(),
                        visiting_node_start_line,
                        visiting_undecorated_node_start_line,
                        child,
                        -1,
                        visiting_node.unwrap_or(NodeId::NONE),
                        visiting_indenter.as_ref(),
                        visiting_node_start_line,
                        visiting_undecorated_node_start_line,
                        false,
                        false,
                    );
                    Some(child)
                },
            ),
            NodeVisitorHooks {
                visit_nodes: Some(Box::new(
                    move |cx: &mut VisitorCx,
                          list: Option<NodeList>,
                          _v: &NodeVisitor|
                          -> Option<NodeList> {
                        if let Some(l) = &list {
                            let (
                                visiting_node,
                                visiting_indenter,
                                visiting_node_start_line,
                                visiting_undecorated_node_start_line,
                            ) = {
                                (
                                    w.visiting_node.get(),
                                    w.visiting_indenter.borrow().clone(),
                                    w.visiting_node_start_line.get(),
                                    w.visiting_undecorated_node_start_line.get(),
                                )
                            };
                            Self::process_child_nodes(
                                w,
                                s,
                                cx.nodes,
                                visiting_node.unwrap_or(NodeId::NONE),
                                visiting_indenter.as_ref(),
                                visiting_node_start_line,
                                visiting_undecorated_node_start_line,
                                l,
                                visiting_node.unwrap_or(NodeId::NONE),
                                visiting_node_start_line,
                                visiting_indenter.as_ref(),
                            );
                        }
                        list
                    },
                )),
                ..Default::default()
            },
        );
        {
            let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
            let mut cx = VisitorCx::new(nodes, &mut factory);
            visitor.visit_each_child(&mut cx, node);
        }

        w.visiting_node.set(old_node);
        *w.visiting_indenter.borrow_mut() = old_indenter;
        w.visiting_node_start_line.set(old_start);
        w.visiting_undecorated_node_start_line
            .set(old_undecorated_start);
    }

    /// `(w *formatSpanWorker) getCurrentIndentationAtPosition`
    fn get_current_indentation_at_position(&self, pos: i32, nodes: &[Node]) -> i32 {
        let start_line_position =
            get_line_start_position_for_position(pos, self.source_file, nodes);
        find_first_non_whitespace_column(
            start_line_position,
            pos,
            self.source_file,
            &self.formatting_context.borrow().options,
            nodes,
        )
    }

    /// `(w *formatSpanWorker) computeIndentation`
    fn compute_indentation(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        start_line: i32,
        inherited_indentation: i32,
        parent: NodeId,
        parent_dynamic_indentation: Option<&Rc<RefCell<DynamicIndenter>>>,
        effective_parent_start_line: i32,
    ) -> (i32, i32) {
        let mut delta = 0;
        if should_indent_child_node(
            &self.formatting_context.borrow().options,
            node,
            None,
            None,
            false,
            nodes,
        ) {
            delta = self
                .formatting_context
                .borrow()
                .options
                .editor_settings
                .indent_size;
        }

        let pdi = parent_dynamic_indentation.expect("parentDynamicIndentation");

        if effective_parent_start_line == start_line {
            // if node is located on the same line with the parent
            // - inherit indentation from the parent
            // - push children if either parent of node itself has non-zero delta
            let mut indentation = self.indentation_on_last_indented_line.get();
            if start_line != self.last_indented_line.get() {
                indentation = pdi.borrow().get_indentation();
            }
            delta = std::cmp::min(
                self.formatting_context
                    .borrow()
                    .options
                    .editor_settings
                    .indent_size,
                pdi.borrow().get_delta(Some(node), nodes) + delta,
            );
            (indentation, delta)
        } else if inherited_indentation == -1 {
            if nodes[node].kind == Kind::OpenParenToken
                && start_line == self.last_indented_line.get()
            {
                // the is used for chaining methods formatting
                // - we need to get the indentation on last line and the delta of parent
                (
                    self.indentation_on_last_indented_line.get(),
                    pdi.borrow().get_delta(Some(node), nodes),
                )
            } else if child_starts_on_the_same_line_with_else_in_if_statement(
                parent,
                node,
                start_line,
                self.source_file,
                nodes,
            ) || child_is_unindented_branch_of_conditional_expression(
                parent,
                node,
                start_line,
                self.source_file,
                nodes,
            ) || argument_starts_on_same_line_as_previous_argument(
                parent,
                node,
                start_line,
                self.source_file,
                nodes,
            ) {
                (pdi.borrow().get_indentation(), delta)
            } else {
                let i = pdi.borrow().get_indentation();
                if i == -1 {
                    (pdi.borrow().get_indentation(), delta)
                } else {
                    (i + pdi.borrow().get_delta(Some(node), nodes), delta)
                }
            }
        } else {
            (inherited_indentation, delta)
        }
    }

    /** Tries to compute the indentation for a list element.
     * If list element is not in range then
     * function will pick its actual indentation
     * so it can be pushed downstream as inherited indentation.
     * If list element is in the range - its indentation will be equal
     * to inherited indentation from its predecessors.
     */
    /// `tryComputeIndentationForListItem`
    fn try_compute_indentation_for_list_item(
        &self,
        start_pos: i32,
        end_pos: i32,
        parent_start_line: i32,
        r: TextRange,
        inherited_indentation: i32,
        nodes: &mut Vec<Node>,
    ) -> i32 {
        let r2 = TextRange::new(start_pos, end_pos);
        if r.overlaps(&r2) || r2.contained_by(&r) {
            /* Not to miss zero-range nodes e.g. JsxText */
            if inherited_indentation != -1 {
                return inherited_indentation;
            }
        } else {
            let start_line = line_of_position(nodes, self.source_file, start_pos);
            let column = self.get_current_indentation_at_position(start_pos, nodes);
            if start_line != parent_start_line || start_pos == column {
                // Use the base indent size if it is greater than
                // the indentation of the inherited predecessor.
                let base_indent_size = self
                    .formatting_context
                    .borrow()
                    .options
                    .editor_settings
                    .base_indent_size;
                if base_indent_size > column {
                    return base_indent_size;
                }
                return column;
            }
        }
        -1
    }

    /// `(w *formatSpanWorker) processNode`
    #[allow(clippy::too_many_arguments)]
    fn process_node(
        w: &FormatSpanWorker,
        s: &RefCell<FormattingScanner<'_>>,
        nodes: &mut Vec<Node>,
        node: NodeId,
        context_node: NodeId,
        node_start_line: i32,
        undecorated_node_start_line: i32,
        indentation: i32,
        delta: i32,
    ) {
        if !w
            .original_range
            .overlaps(&with_token_start(node, w.source_file, nodes))
        {
            return;
        }

        let node_dynamic_indentation =
            w.get_dynamic_indentation(node, node_start_line, indentation, delta);

        // a useful observations when tracking context node
        //        /
        //      [a]
        //   /   |   \
        //  [b] [c] [d]
        // node 'a' is a context node for nodes 'b', 'c', 'd'
        // except for the leftmost leaf token in [b] - in this case context node ('e') is located somewhere above 'a'
        // this rule can be applied recursively to child nodes of 'a'.
        //
        // context node is set to parent node value after processing every child node
        // context node is set to parent of the token after processing every token

        w.child_context_node.set(Some(context_node));

        // if there are any tokens that logically belong to node and interleave child nodes
        // such tokens will be consumed in processChildNode for the child that follows them
        Self::execute_process_node_visitor(
            w,
            s,
            nodes,
            node,
            Some(node_dynamic_indentation.clone()),
            node_start_line,
            undecorated_node_start_line,
        );

        // proceed any tokens in the node that are located after child nodes
        while s.borrow().is_on_token() && s.borrow().get_token_full_start() < w.original_range.end()
        {
            let token_info = s.borrow_mut().read_token_info(node, nodes);
            if token_info.token.loc.end() > std::cmp::min(nodes[node].end(), w.original_range.end())
            {
                break;
            }
            w.consume_token_and_advance_scanner(
                s,
                nodes,
                &token_info,
                node,
                Some(&node_dynamic_indentation),
                node,
                false,
            );
        }
    }

    /// `(w *formatSpanWorker) processPair`
    #[allow(clippy::too_many_arguments)]
    fn process_pair(
        &self,
        nodes: &mut Vec<Node>,
        current_item: TextRangeWithKind,
        current_start_line: i32,
        current_parent: NodeId,
        previous_item: TextRangeWithKind,
        previous_start_line: i32,
        previous_parent: NodeId,
        context_node: NodeId,
        dynamic_indentation: Option<Rc<RefCell<DynamicIndenter>>>,
    ) -> LineAction {
        {
            let mut fc = self.formatting_context.borrow_mut();
            fc.update_context(
                previous_item,
                previous_parent,
                current_item,
                current_parent,
                context_node,
            );
        }

        {
            let mut rules = self.current_rules.borrow_mut();
            rules.clear();
            let mut fc = self.formatting_context.borrow_mut();
            get_rules(&mut *fc, &mut *rules, nodes);
        }

        let mut trim_trailing_whitespaces = !self
            .formatting_context
            .borrow()
            .options
            .editor_settings
            .trim_trailing_whitespace
            .is_false();
        let mut line_action = LineAction::None;

        let rules_snapshot: Vec<&'static RuleImpl> = self.current_rules.borrow().clone();
        if !rules_snapshot.is_empty() {
            // Apply rules in reverse order so that higher priority rules (which are first in the array)
            // win in a conflict with lower priority rules.
            for &rule in rules_snapshot.iter().rev() {
                line_action = self.apply_rule_edits(
                    nodes,
                    rule,
                    previous_item,
                    previous_start_line,
                    current_item,
                    current_start_line,
                );
                if let Some(di) = &dynamic_indentation {
                    match line_action {
                        LineAction::LineRemoved => {
                            // Handle the case where the next line is moved to be the end of this line.
                            // In this case we don't indent the next line in the next pass.
                            if get_token_pos_of_node(
                                current_parent,
                                nodes[self.source_file].as_source_file(),
                                false,
                                nodes,
                            ) == current_item.loc.pos()
                            {
                                di.borrow_mut().recompute_indentation(
                                    false, /*lineAddedByFormatting*/
                                    context_node,
                                    nodes,
                                );
                            }
                        }
                        LineAction::LineAdded => {
                            // Handle the case where token2 is moved to the new line.
                            // In this case we indent token2 in the next pass but we set
                            // sameLineIndent flag to notify the indenter that the indentation is within the line.
                            if get_token_pos_of_node(
                                current_parent,
                                nodes[self.source_file].as_source_file(),
                                false,
                                nodes,
                            ) == current_item.loc.pos()
                            {
                                di.borrow_mut().recompute_indentation(
                                    true, /*lineAddedByFormatting*/
                                    context_node,
                                    nodes,
                                );
                            }
                        }
                        _ => {
                            debug_assert!(line_action == LineAction::None);
                        }
                    }
                }

                // We need to trim trailing whitespace between the tokens if they were on different lines, and no rule was applied to put them on the same line
                trim_trailing_whitespaces = trim_trailing_whitespaces
                    && (rule.action() & RULE_ACTION_DELETE_SPACE == 0)
                    && rule.flags() != RuleFlags::CanDeleteNewLines;
            }
        } else {
            trim_trailing_whitespaces =
                trim_trailing_whitespaces && current_item.kind != Kind::EndOfFile;
        }

        if current_start_line != previous_start_line && trim_trailing_whitespaces {
            // We need to trim trailing whitespace between the tokens if they were on different lines, and no rule was applied to put them on the same line
            self.trim_trailing_whitespaces_for_lines(
                previous_start_line,
                current_start_line,
                previous_item,
                nodes,
            );
        }

        line_action
    }

    /// `(w *formatSpanWorker) applyRuleEdits`
    fn apply_rule_edits(
        &self,
        nodes: &mut Vec<Node>,
        rule: &RuleImpl,
        previous_range: TextRangeWithKind,
        previous_start_line: i32,
        current_range: TextRangeWithKind,
        current_start_line: i32,
    ) -> LineAction {
        let on_later_line = current_start_line != previous_start_line;
        match rule.action() {
            RULE_ACTION_STOP_PROCESSING_SPACE_ACTIONS => {
                // no action required
                LineAction::None
            }
            RULE_ACTION_DELETE_SPACE => {
                if previous_range.loc.end() != current_range.loc.pos() {
                    // delete characters starting from t1.end up to t2.pos exclusive
                    self.record_delete(
                        previous_range.loc.end(),
                        current_range.loc.pos() - previous_range.loc.end(),
                    );
                    if on_later_line {
                        return LineAction::LineRemoved;
                    }
                    LineAction::None
                } else {
                    LineAction::None
                }
            }
            RULE_ACTION_DELETE_TOKEN => {
                self.record_delete(previous_range.loc.pos(), previous_range.loc.len());
                LineAction::None
            }
            RULE_ACTION_INSERT_NEW_LINE => {
                // exit early if we on different lines and rule cannot change number of newlines
                // if line1 and line2 are on subsequent lines then no edits are required - ok to exit
                // if line1 and line2 are separated with more than one newline - ok to exit since we cannot delete extra new lines
                if rule.flags() != RuleFlags::CanDeleteNewLines
                    && previous_start_line != current_start_line
                {
                    return LineAction::None;
                }

                // edit should not be applied if we have one line feed between elements
                let line_delta = current_start_line - previous_start_line;
                if line_delta != 1 {
                    self.record_replace(
                        previous_range.loc.end(),
                        current_range.loc.pos() - previous_range.loc.end(),
                        &get_new_line_or_default_from_context(&self.ctx),
                    );
                    if on_later_line {
                        return LineAction::None;
                    }
                    LineAction::LineAdded
                } else {
                    LineAction::None
                }
            }
            RULE_ACTION_INSERT_SPACE => {
                // exit early if we on different lines and rule cannot change number of newlines
                if rule.flags() != RuleFlags::CanDeleteNewLines
                    && previous_start_line != current_start_line
                {
                    return LineAction::None;
                }

                let pos_delta = current_range.loc.pos() - previous_range.loc.end();
                if pos_delta != 1
                    || !nodes[self.source_file].as_source_file().text
                        [previous_range.loc.end() as usize..]
                        .starts_with(' ')
                {
                    self.record_replace(previous_range.loc.end(), pos_delta, " ");
                    if on_later_line {
                        return LineAction::LineRemoved;
                    }
                    LineAction::None
                } else {
                    LineAction::None
                }
            }
            RULE_ACTION_INSERT_TRAILING_SEMICOLON => {
                self.record_insert(previous_range.loc.end(), ";");
                LineAction::None
            }
            _ => LineAction::None,
        }
    }

    /// `(w *formatSpanWorker) processRange`
    fn process_range(
        &self,
        nodes: &mut Vec<Node>,
        r: TextRangeWithKind,
        range_start_line: i32,
        _range_start_character: i32,
        parent: NodeId,
        context_node: NodeId,
        dynamic_indentation: Option<&Rc<RefCell<DynamicIndenter>>>,
    ) -> LineAction {
        let range_has_error = (self.range_contains_error.borrow_mut())(r.loc);
        let mut line_action = LineAction::None;
        if !range_has_error {
            if self.previous_range.get() == TextRangeWithKind::new(0, 0, Kind::Unknown) {
                // trim whitespaces starting from the beginning of the span up to the current line
                let original_start_line =
                    line_of_position(nodes, self.source_file, self.original_range.pos());
                self.trim_trailing_whitespaces_for_lines(
                    original_start_line,
                    range_start_line,
                    TextRangeWithKind::new(0, 0, Kind::Unknown),
                    nodes,
                );
            } else {
                line_action = self.process_pair(
                    nodes,
                    r,
                    range_start_line,
                    parent,
                    self.previous_range.get(),
                    self.previous_range_start_line.get(),
                    self.previous_parent.get().unwrap_or(NodeId::NONE),
                    context_node,
                    dynamic_indentation.cloned(),
                );
            }
        }

        self.previous_range.set(r);
        self.previous_range_trivia_end.set(r.loc.end());
        self.previous_parent.set(Some(parent));
        self.previous_range_start_line.set(range_start_line);

        line_action
    }

    /// `(w *formatSpanWorker) processTrivia`
    fn process_trivia(
        &self,
        nodes: &mut Vec<Node>,
        trivia: &[TextRangeWithKind],
        parent: NodeId,
        context_node: NodeId,
        dynamic_indentation: Option<&Rc<RefCell<DynamicIndenter>>>,
    ) {
        for trivia_item in trivia {
            if is_comment(trivia_item.kind) && trivia_item.loc.contained_by(&self.original_range) {
                let (trivia_item_start_line, trivia_item_start_character) =
                    line_and_byte_offset_of_position(
                        nodes,
                        self.source_file,
                        trivia_item.loc.pos(),
                    );
                self.process_range(
                    nodes,
                    *trivia_item,
                    trivia_item_start_line,
                    trivia_item_start_character,
                    parent,
                    context_node,
                    dynamic_indentation,
                );
            }
        }
    }

    /**
     * Trimming will be done for lines after the previous range.
     * Exclude comments as they had been previously processed.
     */
    /// `trimTrailingWhitespacesForRemainingRange`
    fn trim_trailing_whitespaces_for_remaining_range(
        &self,
        trivias: &[TextRangeWithKind],
        nodes: &mut Vec<Node>,
    ) {
        let mut start_pos = self.original_range.pos();
        if self.previous_range.get() != TextRangeWithKind::new(0, 0, Kind::Unknown) {
            start_pos = self.previous_range.get().loc.end();
        }

        for trivia in trivias {
            if is_comment(trivia.kind) {
                if start_pos < trivia.loc.pos() {
                    self.trim_trailing_witespaces_for_positions(
                        start_pos,
                        trivia.loc.pos() - 1,
                        self.previous_range.get(),
                        nodes,
                    );
                }

                start_pos = trivia.loc.end() + 1;
            }
        }

        if start_pos < self.original_range.end() {
            self.trim_trailing_witespaces_for_positions(
                start_pos,
                self.original_range.end(),
                self.previous_range.get(),
                nodes,
            );
        }
    }

    /// `trimTrailingWitespacesForPositions` (Go typo preserved)
    fn trim_trailing_witespaces_for_positions(
        &self,
        start_pos: i32,
        end_pos: i32,
        previous_range: TextRangeWithKind,
        nodes: &mut Vec<Node>,
    ) {
        let start_line = line_of_position(nodes, self.source_file, start_pos);
        let end_line = line_of_position(nodes, self.source_file, end_pos);

        self.trim_trailing_whitespaces_for_lines(start_line, end_line + 1, previous_range, nodes);
    }

    /// `trimTrailingWhitespacesForLines`
    fn trim_trailing_whitespaces_for_lines(
        &self,
        line1: i32,
        line2: i32,
        r: TextRangeWithKind,
        nodes: &[Node],
    ) {
        let line_starts = line_map(nodes, self.source_file);
        for line in line1..line2 {
            let line_start_position = line_starts[line as usize];
            let line_end_position = end_line_position(nodes, self.source_file, line);

            // do not trim whitespaces in comments or template expression
            if r != TextRangeWithKind::new(0, 0, Kind::Unknown)
                && (is_comment(r.kind)
                    || is_string_or_regular_expression_or_template_literal(r.kind))
                && r.loc.pos() <= line_end_position
                && r.loc.end() > line_end_position
            {
                continue;
            }

            let whitespace_start = self.get_trailing_whitespace_start_position(
                line_start_position,
                line_end_position,
                nodes,
            );
            if whitespace_start != -1 {
                if whitespace_start != line_start_position {
                    let (ch, _) = decode_rune_in_string(
                        &nodes[self.source_file].as_source_file().text.as_bytes()
                            [(whitespace_start - 1) as usize..],
                    );
                    debug_assert!(!is_white_space_single_line(ch));
                }
                self.record_delete(whitespace_start, line_end_position + 1 - whitespace_start);
            }
        }
    }

    /**
     * @param start The position of the first character in range
     * @param end The position of the last character in range
     */
    /// `getTrailingWhitespaceStartPosition`
    fn get_trailing_whitespace_start_position(&self, start: i32, end: i32, nodes: &[Node]) -> i32 {
        let mut pos = end;
        let text = &nodes[self.source_file].as_source_file().text;
        while pos >= start {
            let (ch, size) = decode_rune_in_string(&text.as_bytes()[pos as usize..]);
            if size == 0 {
                pos -= 1; // multibyte character, rewind more
                continue;
            }
            if !is_white_space_single_line(ch) {
                break;
            }
            pos -= 1;
        }
        if pos != end {
            return pos + 1;
        }
        -1
    }

    /// `(w *formatSpanWorker) insertIndentation`
    fn insert_indentation(&self, pos: i32, indentation: i32, line_added: bool, nodes: &[Node]) {
        let indentation_string =
            get_indentation_string(indentation, &self.formatting_context.borrow().options);
        if line_added {
            // new line is added before the token by the formatting rules
            // insert indentation string at the very beginning of the token
            self.record_replace(pos, 0, &indentation_string);
        } else {
            let (token_start_line, token_start_character) =
                line_and_byte_offset_of_position(nodes, self.source_file, pos);
            let start_line_position = line_map(nodes, self.source_file)[token_start_line as usize];
            if indentation
                != self.character_to_column(start_line_position, token_start_character, nodes)
                || self.indentation_is_different(&indentation_string, start_line_position, nodes)
            {
                self.record_replace(
                    start_line_position,
                    token_start_character,
                    &indentation_string,
                );
            }
        }
    }

    /// `(w *formatSpanWorker) characterToColumn`
    fn character_to_column(
        &self,
        start_line_position: i32,
        character_in_line: i32,
        nodes: &[Node],
    ) -> i32 {
        let mut column = 0;
        for i in 0..character_in_line {
            if nodes[self.source_file].as_source_file().text.as_bytes()
                [(start_line_position + i) as usize]
                == b'\t'
            {
                let tab_size = self
                    .formatting_context
                    .borrow()
                    .options
                    .editor_settings
                    .tab_size;
                if tab_size > 0 {
                    column += tab_size - (column % tab_size);
                }
            } else {
                column += 1;
            }
        }
        column
    }

    /// `(w *formatSpanWorker) indentationIsDifferent`
    fn indentation_is_different(
        &self,
        indentation_string: &str,
        start_line_position: i32,
        nodes: &[Node],
    ) -> bool {
        let text = &nodes[self.source_file].as_source_file().text;
        let end = start_line_position as usize + indentation_string.len();
        if end > text.len() {
            return true;
        }
        indentation_string != &text[start_line_position as usize..end]
    }

    /// `(w *formatSpanWorker) indentTriviaItems`
    fn indent_trivia_items(
        &self,
        trivia: &[TextRangeWithKind],
        comment_indentation: i32,
        indent_next_token_or_trivia: bool,
        indent_single_line: &mut dyn FnMut(&mut Vec<Node>, TextRangeWithKind),
        nodes: &mut Vec<Node>,
    ) -> bool {
        let mut indent_next_token_or_trivia = indent_next_token_or_trivia;
        for trivia_item in trivia {
            let trivia_in_range = trivia_item.loc.contained_by(&self.original_range);
            match trivia_item.kind {
                Kind::MultiLineCommentTrivia => {
                    if trivia_in_range {
                        self.indent_multiline_comment(
                            trivia_item.loc,
                            comment_indentation,
                            !indent_next_token_or_trivia,
                            true,
                            nodes,
                        );
                    }
                    indent_next_token_or_trivia = false;
                }
                Kind::SingleLineCommentTrivia => {
                    if indent_next_token_or_trivia && trivia_in_range {
                        indent_single_line(nodes, *trivia_item);
                    }
                    indent_next_token_or_trivia = false;
                }
                Kind::NewLineTrivia => {
                    indent_next_token_or_trivia = true;
                }
                _ => {}
            }
        }
        indent_next_token_or_trivia
    }

    /// `(w *formatSpanWorker) indentMultilineComment`
    fn indent_multiline_comment(
        &self,
        comment_range: TextRange,
        indentation: i32,
        first_line_is_indented: bool,
        indent_final_line: bool,
        nodes: &[Node],
    ) {
        // split comment in lines
        let mut start_line = line_of_position(nodes, self.source_file, comment_range.pos());
        let end_line = line_of_position(nodes, self.source_file, comment_range.end());

        if start_line == end_line {
            if !first_line_is_indented {
                // treat as single line comment
                self.insert_indentation(comment_range.pos(), indentation, false, nodes);
            }
            return;
        }

        let mut parts: Vec<TextRange> = Vec::with_capacity(
            nodes[self.source_file].as_source_file().text
                [comment_range.pos() as usize..comment_range.end() as usize]
                .matches('\n')
                .count(),
        );
        let mut start_pos = comment_range.pos();
        for line in start_line..end_line {
            let end_of_line = end_line_position(nodes, self.source_file, line);
            parts.push(TextRange::new(start_pos, end_of_line));
            start_pos = line_map(nodes, self.source_file)[(line + 1) as usize];
        }

        if indent_final_line {
            parts.push(TextRange::new(start_pos, comment_range.end()));
        }

        if parts.is_empty() {
            return;
        }

        let start_line_pos = line_map(nodes, self.source_file)[start_line as usize];

        let (non_whitespace_in_first_part_character, non_whitespace_in_first_part_column) =
            find_first_non_whitespace_character_and_column(
                start_line_pos,
                parts[0].pos(),
                self.source_file,
                &self.formatting_context.borrow().options,
                nodes,
            );

        let mut start_index = 0;

        if first_line_is_indented {
            start_index = 1;
            start_line += 1;
        }

        // shift all parts on the delta size
        let delta = indentation - non_whitespace_in_first_part_column;
        for i in start_index..parts.len() {
            let start_line_pos = line_map(nodes, self.source_file)[start_line as usize];
            let mut non_whitespace_character = non_whitespace_in_first_part_character;
            let mut non_whitespace_column = non_whitespace_in_first_part_column;
            if i != 0 {
                let (c, col) = find_first_non_whitespace_character_and_column(
                    parts[i].pos(),
                    parts[i].end(),
                    self.source_file,
                    &self.formatting_context.borrow().options,
                    nodes,
                );
                non_whitespace_character = c;
                non_whitespace_column = col;
            }
            let new_indentation = non_whitespace_column + delta;
            if new_indentation > 0 {
                let indentation_string = get_indentation_string(
                    new_indentation,
                    &self.formatting_context.borrow().options,
                );
                self.record_replace(
                    start_line_pos,
                    non_whitespace_character,
                    &indentation_string,
                );
            } else {
                self.record_delete(start_line_pos, non_whitespace_character);
            }

            start_line += 1;
        }
    }

    /// `recordDelete`
    fn record_delete(&self, start: i32, length: i32) {
        if length != 0 {
            self.edits
                .borrow_mut()
                .push(create_text_change_from_start_length(start, length, ""));
        }
    }

    /// `recordReplace`
    fn record_replace(&self, start: i32, length: i32, new_text: &str) {
        if length != 0 || !new_text.is_empty() {
            self.edits
                .borrow_mut()
                .push(create_text_change_from_start_length(
                    start, length, new_text,
                ));
        }
    }

    /// `recordInsert`
    fn record_insert(&self, start: i32, text: &str) {
        if !text.is_empty() {
            self.edits
                .borrow_mut()
                .push(create_text_change_from_start_length(start, 0, text));
        }
    }

    /// `(w *formatSpanWorker) consumeTokenAndAdvanceScanner`
    fn consume_token_and_advance_scanner(
        &self,
        s: &RefCell<FormattingScanner<'_>>,
        nodes: &mut Vec<Node>,
        current_token_info: &TokenInfo,
        parent: NodeId,
        dynamic_indenation: Option<&Rc<RefCell<DynamicIndenter>>>,
        container: NodeId,
        is_list_end_token: bool,
    ) {
        // assert(currentTokenInfo.token.Loc.ContainedBy(parent.Loc)) // !!!
        let last_trivia_was_new_line = s.borrow().last_trailing_trivia_was_new_line();
        let mut indent_token = false;

        if !current_token_info.leading_trivia.is_empty() {
            self.process_trivia(
                nodes,
                &current_token_info.leading_trivia,
                parent,
                self.child_context_node.get().unwrap_or(NodeId::NONE),
                dynamic_indenation,
            );
        }

        let mut line_action = LineAction::None;
        let is_token_in_range = current_token_info
            .token
            .loc
            .contained_by(&self.original_range);

        let (token_start_line, token_start_char) = line_and_byte_offset_of_position(
            nodes,
            self.source_file,
            current_token_info.token.loc.pos(),
        );

        if is_token_in_range {
            let range_has_error =
                (self.range_contains_error.borrow_mut())(current_token_info.token.loc);
            // save previousRange since processRange will overwrite this value with current one
            let save_previous_range = self.previous_range.get();
            line_action = self.process_range(
                nodes,
                current_token_info.token,
                token_start_line,
                token_start_char,
                parent,
                self.child_context_node.get().unwrap_or(NodeId::NONE),
                dynamic_indenation,
            );
            // do not indent comments\token if token range overlaps with some error
            if !range_has_error {
                if line_action == LineAction::None {
                    // indent token only if end line of previous range does not match start line of the token
                    if save_previous_range != TextRangeWithKind::new(0, 0, Kind::Unknown) {
                        let prev_end_line = line_of_position(
                            nodes,
                            self.source_file,
                            save_previous_range.loc.end(),
                        );
                        indent_token =
                            last_trivia_was_new_line && token_start_line != prev_end_line;
                    } else {
                        // When there's no previous range (first token), TS sets prevEndLine to undefined.
                        // tokenStart.line !== undefined is always true in JS, so indentToken = lastTriviaWasNewLine.
                        indent_token = last_trivia_was_new_line;
                    }
                } else {
                    indent_token = line_action == LineAction::LineAdded;
                }
            }
        }

        if !current_token_info.trailing_trivia.is_empty() {
            self.previous_range_trivia_end
                .set(current_token_info.trailing_trivia.last().unwrap().loc.end());
            // If any trailing comment trivia extends past the original range, it won't be
            // processed by processTrivia (which skips comments not contained by originalRange).
            // Cap previousRangeTriviaEnd before such comments so the trailing edit contiguity
            // check in execute() won't pair across unprocessed comment content.
            for trivia in &current_token_info.trailing_trivia {
                if is_comment(trivia.kind) && !trivia.loc.contained_by(&self.original_range) {
                    self.previous_range_trivia_end.set(trivia.loc.pos());
                    break;
                }
            }
            self.process_trivia(
                nodes,
                &current_token_info.trailing_trivia,
                parent,
                self.child_context_node.get().unwrap_or(NodeId::NONE),
                dynamic_indenation,
            );
        }

        if indent_token {
            let mut token_indentation = -1;
            if is_token_in_range
                && !(self.range_contains_error.borrow_mut())(current_token_info.token.loc)
            {
                token_indentation = dynamic_indenation
                    .expect("dynamicIndenation")
                    .borrow()
                    .get_indentation_for_token(
                        token_start_line,
                        current_token_info.token.kind,
                        container,
                        is_list_end_token,
                        nodes,
                    );
            }
            let mut indent_next_token_or_trivia = true;
            if !current_token_info.leading_trivia.is_empty() {
                let comment_indentation = dynamic_indenation
                    .expect("dynamicIndenation")
                    .borrow()
                    .get_indentation_for_comment(
                        current_token_info.token.kind,
                        token_indentation,
                        container,
                        nodes,
                    );
                indent_next_token_or_trivia = self.indent_trivia_items(
                    &current_token_info.leading_trivia,
                    comment_indentation,
                    indent_next_token_or_trivia,
                    &mut |nodes: &mut Vec<Node>, item: TextRangeWithKind| {
                        self.insert_indentation(item.loc.pos(), comment_indentation, false, nodes);
                    },
                    nodes,
                );
            }

            // indent token only if is it is in target range and does not overlap with any error ranges
            if token_indentation != -1 && indent_next_token_or_trivia {
                self.insert_indentation(
                    current_token_info.token.loc.pos(),
                    token_indentation,
                    line_action == LineAction::LineAdded,
                    nodes,
                );

                self.last_indented_line.set(token_start_line);
                self.indentation_on_last_indented_line
                    .set(token_indentation);
            }
        }

        s.borrow_mut().advance();

        self.child_context_node.set(Some(parent));
    }

    /// `(w *formatSpanWorker) getDynamicIndentation`
    fn get_dynamic_indentation(
        &self,
        node: NodeId,
        node_start_line: i32,
        indentation: i32,
        delta: i32,
    ) -> Rc<RefCell<DynamicIndenter>> {
        Rc::new(RefCell::new(DynamicIndenter {
            node,
            node_start_line,
            indentation,
            delta,
            options: self.formatting_context.borrow().options.clone(),
            source_file: self.source_file,
        }))
    }
}

/// `type LineAction int`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum LineAction {
    #[default]
    None,
    LineAdded,
    LineRemoved,
}

/// `type dynamicIndenter struct`
pub(crate) struct DynamicIndenter {
    node: NodeId,
    node_start_line: i32,
    indentation: i32,
    delta: i32,

    options: FormatCodeSettings,
    source_file: NodeId,
}

impl DynamicIndenter {
    /// `(i *dynamicIndenter) getIndentationForComment`
    fn get_indentation_for_comment(
        &self,
        kind: Kind,
        token_indentation: i32,
        container: NodeId,
        nodes: &mut Vec<Node>,
    ) -> i32 {
        match kind {
            // preceding comment to the token that closes the indentation scope inherits the indentation from the scope
            // ..  {
            //     // comment
            // }
            Kind::CloseBraceToken | Kind::CloseBracketToken | Kind::CloseParenToken => {
                self.indentation + self.get_delta(Some(container), nodes)
            }
            _ => {
                if token_indentation != -1 {
                    token_indentation
                } else {
                    self.indentation
                }
            }
        }
    }

    // if list end token is LessThanToken '>' then its delta should be explicitly suppressed
    // so that LessThanToken as a binary operator can still be indented.
    // foo.then
    //
    //	<
    //	    number,
    //	    string,
    //	>();
    //
    // vs
    // var a = xValue
    //
    //	> yValue;
    /// `(i *dynamicIndenter) getIndentationForToken`
    fn get_indentation_for_token(
        &self,
        line: i32,
        kind: Kind,
        container: NodeId,
        suppress_delta: bool,
        nodes: &mut Vec<Node>,
    ) -> i32 {
        if !suppress_delta && self.should_add_delta(line, kind, container, nodes) {
            return self.indentation + self.get_delta(Some(container), nodes);
        }
        self.indentation
    }

    /// `(i *dynamicIndenter) getIndentation`
    fn get_indentation(&self) -> i32 {
        self.indentation
    }

    /// `(i *dynamicIndenter) getDelta`
    fn get_delta(&self, child: Option<NodeId>, nodes: &mut Vec<Node>) -> i32 {
        // Delta value should be zero when the node explicitly prevents indentation of the child node
        if node_will_indent_child(
            &self.options,
            self.node,
            child,
            Some(self.source_file),
            true,
            nodes,
        ) {
            return self.delta;
        }
        0
    }

    /// `(i *dynamicIndenter) recomputeIndentation`
    fn recompute_indentation(&mut self, line_added: bool, parent: NodeId, nodes: &mut Vec<Node>) {
        if should_indent_child_node(
            &self.options,
            parent,
            Some(self.node),
            Some(self.source_file),
            false,
            nodes,
        ) {
            if line_added {
                self.indentation += self.options.editor_settings.indent_size; // !!! no nil check???
            } else {
                self.indentation -= self.options.editor_settings.indent_size; // !!! no nil check???
            }
            if should_indent_child_node(&self.options, self.node, None, None, false, nodes) {
                self.delta = self.options.editor_settings.indent_size;
            } else {
                self.delta = 0;
            }
        }
    }

    /// `(i *dynamicIndenter) shouldAddDelta`
    fn should_add_delta(
        &self,
        line: i32,
        kind: Kind,
        container: NodeId,
        nodes: &mut Vec<Node>,
    ) -> bool {
        match kind {
            // open and close brace, 'else' and 'while' (in do statement) tokens has indentation of the parent
            Kind::OpenBraceToken
            | Kind::CloseBraceToken
            | Kind::CloseParenToken
            | Kind::ElseKeyword
            | Kind::WhileKeyword
            | Kind::AtToken => return false,
            Kind::SlashToken | Kind::GreaterThanToken => match nodes[container].kind {
                Kind::JsxOpeningElement | Kind::JsxClosingElement | Kind::JsxSelfClosingElement => {
                    return false;
                }
                _ => {}
            },
            Kind::OpenBracketToken | Kind::CloseBracketToken => {
                if nodes[container].kind != Kind::MappedType {
                    return false;
                }
            }
            _ => {}
        }
        // if token line equals to the line of containing node (this is a first token in the node) - use node indentation
        self.node_start_line != line &&
            // if this token is the first token following the list of decorators, we do not need to indent
            !(tsc_ast::has_decorators(&nodes[self.node]) && kind == get_first_non_decorator_token_of_node(self.node, nodes))
    }
}

/// `getFirstNonDecoratorTokenOfNode`
fn get_first_non_decorator_token_of_node(node: NodeId, nodes: &mut Vec<Node>) -> Kind {
    if tsc_ast::can_have_modifiers(&nodes[node]) {
        if let Some(modifier_nodes) = nodes[node].modifier_nodes() {
            let decorator_index = modifier_nodes
                .iter()
                .position(|&m| tsc_ast::is_decorator(&nodes[m]));
            if let Some(idx) = decorator_index {
                let modifier = modifier_nodes[idx..]
                    .iter()
                    .find(|&&m| tsc_ast::is_modifier(&nodes[m]));
                if let Some(&modifier) = modifier {
                    return nodes[modifier].kind;
                }
            }
        }
    }

    match nodes[node].kind {
        Kind::ClassDeclaration => Kind::ClassKeyword,
        Kind::InterfaceDeclaration => Kind::InterfaceKeyword,
        Kind::FunctionDeclaration => Kind::FunctionKeyword,
        Kind::EnumDeclaration => Kind::EnumDeclaration,
        Kind::GetAccessor => Kind::GetKeyword,
        Kind::SetAccessor => Kind::SetKeyword,
        Kind::MethodDeclaration => {
            if nodes[node]
                .as_method_declaration()
                .function_like_with_body_base
                .body_base
                .asterisk_token
                .is_some()
            {
                return Kind::AsteriskToken;
            }
            first_non_decorator_token_fallthrough(node, nodes)
        }
        _ => first_non_decorator_token_fallthrough(node, nodes),
    }
}

/// Fallthrough of `getFirstNonDecoratorTokenOfNode` for
/// `Kind::PropertyDeclaration | Kind::Parameter`.
fn first_non_decorator_token_fallthrough(node: NodeId, nodes: &mut Vec<Node>) -> Kind {
    match nodes[node].kind {
        Kind::PropertyDeclaration | Kind::Parameter | Kind::MethodDeclaration => {
            let name = tsc_ast::get_name_of_declaration(Some(node), nodes);
            if let Some(name) = name {
                return nodes[name].kind;
            }
        }
        _ => {}
    }

    Kind::Unknown
}

/// `isStringOrRegularExpressionOrTemplateLiteral`
pub(crate) fn is_string_or_regular_expression_or_template_literal(kind: Kind) -> bool {
    kind == Kind::StringLiteral
        || kind == Kind::RegularExpressionLiteral
        || tsc_ast::is_template_literal_kind(kind)
}

/// `isComment`
pub(crate) fn is_comment(kind: Kind) -> bool {
    kind == Kind::SingleLineCommentTrivia || kind == Kind::MultiLineCommentTrivia
}

/// `getIndentationString`
fn get_indentation_string(indentation: i32, options: &FormatCodeSettings) -> String {
    // go's `strings.Repeat` already has static, global caching for repeated tabs and spaces, so there's no need to cache here like in strada
    if !options.editor_settings.convert_tabs_to_spaces.is_true() {
        if options.editor_settings.tab_size == 0 {
            return String::new();
        }
        let tabs = indentation / options.editor_settings.tab_size;
        let spaces = indentation - (tabs * options.editor_settings.tab_size);
        let mut res = "\t".repeat(tabs.max(0) as usize);
        if spaces > 0 {
            res.push_str(&" ".repeat(spaces as usize));
        }

        res
    } else {
        " ".repeat(indentation.max(0) as usize)
    }
}

/// `createTextChangeFromStartLength`
fn create_text_change_from_start_length(start: i32, length: i32, new_text: &str) -> TextChange {
    TextChange {
        new_text: new_text.to_string(),
        text_range: TextRange::new(start, start + length),
    }
}
