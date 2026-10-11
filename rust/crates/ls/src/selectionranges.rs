// Ported from tsc/internal/ls/selectionranges.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::ast::{Node, NodeFactory, NodeFactoryHooks, NodeList};
use tsc_ast::kind_generated::Kind;
use tsc_ast::visitor::{NodeVisitor, NodeVisitorHooks, VisitorCx};
use tsc_ast::{self as ast, NodeId};
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto::{self as lsproto};
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::languageservice::LanguageService;
use crate::utilities::get_children_from_non_jsdoc_node;

const MAX_SELECTION_RANGE_DEPTH: usize = 1000;

struct SelectionRangeBuilder {
    ranges: Vec<lsproto::Range>,
    oldest_index: usize,
}

impl SelectionRangeBuilder {
    fn new(capacity: usize) -> SelectionRangeBuilder {
        SelectionRangeBuilder {
            ranges: Vec::with_capacity(capacity),
            oldest_index: 0,
        }
    }

    fn push(&mut self, selection_range: lsproto::Range) {
        if self.ranges.len() < self.ranges.capacity() {
            self.ranges.push(selection_range);
            return;
        }

        self.ranges[self.oldest_index] = selection_range;
        self.oldest_index = (self.oldest_index + 1) % self.ranges.len();
    }

    fn build(
        self,
        result: Option<Box<lsproto::SelectionRange>>,
    ) -> Option<Box<lsproto::SelectionRange>> {
        let mut result = result;
        for i in 0..self.ranges.len() {
            let index = (self.oldest_index + i) % self.ranges.len();
            result = Some(Box::new(lsproto::SelectionRange {
                range: self.ranges[index].clone(),
                parent: result,
            }));
        }
        result
    }
}

impl<'h> LanguageService<'h> {
    /// `ProvideSelectionRanges`.
    pub fn provide_selection_ranges(
        &self,
        _ctx: &Context,
        params: &lsproto::SelectionRangeParams,
    ) -> Result<lsproto::SelectionRangeResponse, Error> {
        let (program, source_file) = self.get_program_and_file(&params.text_document.uri);

        let positions = params.positions.as_deref().unwrap_or_default();
        let mut results: Vec<lsproto::SelectionRange> = Vec::with_capacity(positions.len());
        for position in positions {
            let (script_file, script_position) = {
                let nodes = program.nodes(source_file.file_index());
                let positions = self.converters.from_lsp_position_for_source_file(
                    source_file,
                    &nodes,
                    *position,
                    Feature::SelectionRanges,
                );
                if positions.len() != 1 || !positions[0].fidelity.is_single_segment() {
                    return Ok(lsproto::SelectionRangesOrNull::default());
                }
                (positions[0].script.file, positions[0].position)
            };
            if let Some(selection_range) =
                self.get_smart_selection_range(script_file, script_position)
            {
                results.push(*selection_range);
            }
        }

        Ok(lsproto::SelectionRangesOrNull {
            selection_ranges: Some(results),
        })
    }

    /// `getSmartSelectionRange`.
    fn get_smart_selection_range(
        &self,
        file: NodeId,
        pos: i32,
    ) -> Option<Box<lsproto::SelectionRange>> {
        let program = self.get_program();
        // Traversal discovers ranges from broadest to most specific, so retain the newest ranges nearest to the cursor
        let state = Rc::new(RefCell::new(SmartSelectionState {
            ranges: SelectionRangeBuilder::new(MAX_SELECTION_RANGE_DEPTH - 1),
            last_range: lsproto::Range::default(),
            next: None,
        }));
        let mut root: Option<Box<lsproto::SelectionRange>> = None;
        {
            let nodes = program.nodes(file.file_index());
            if nodes[file].as_source_file().content_mapper().is_empty() {
                let script = source_file_script(file, &nodes);
                let (full_range, _) = self.converters.to_lsp_range(
                    &script,
                    TextRange::new(nodes[file].pos(), nodes[file].end()),
                );
                root = Some(Box::new(lsproto::SelectionRange {
                    range: full_range.clone(),
                    parent: None,
                }));
                state.borrow_mut().last_range = full_range;
            }
        }

        let mut nodes = program.nodes_mut(file.file_index());
        let mut factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());

        let mut current = Some(file);
        while let Some(current_node) = current {
            let parent = current_node;

            // Visit JSDoc nodes first if they exist
            for jsdoc in ast::js_doc(&mut nodes, current_node, Some(file)) {
                visit_smart_selection(
                    self,
                    &state,
                    &mut nodes,
                    &mut factory,
                    file,
                    pos,
                    parent,
                    jsdoc,
                );
            }

            let visit = {
                let state = Rc::clone(&state);
                move |_v: &NodeVisitor, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    let mut st = state.borrow_mut();
                    visit_smart_selection_cx(self, &mut st, cx, file, pos, parent, node);
                    Some(node)
                }
            };
            let visit_nodes = {
                let state = Rc::clone(&state);
                move |cx: &mut VisitorCx<'_, '_>,
                      list: Option<NodeList>,
                      v: &NodeVisitor|
                      -> Option<NodeList> {
                    if let Some(list) = &list
                        && !list.nodes.is_empty()
                    {
                        let should_skip_list = ast::is_variable_declaration_list(&cx.nodes[parent])
                            || ast::is_template_expression(&cx.nodes[parent]);
                        if !should_skip_list {
                            let start = tsc_astnav::tokens::get_start_of_node(
                                cx.nodes,
                                file,
                                list.nodes[0],
                                false, /*includeJSDoc*/
                            );
                            let end = cx.nodes[*list.nodes.last().expect("nonempty list")].end();
                            if start <= pos && pos < end {
                                let mut st = state.borrow_mut();
                                push_selection_range(
                                    self, &mut st, cx, file, pos, start, end,
                                );
                            }
                        }
                    }
                    v.visit_nodes(cx, list)
                }
            };

            let temp_visitor = NodeVisitor::new(
                Box::new(visit),
                NodeVisitorHooks {
                    visit_nodes: Some(Box::new(visit_nodes)),
                    ..Default::default()
                },
            );

            {
                let mut cx = VisitorCx::new(&mut nodes, &mut factory);
                temp_visitor.visit_each_child(&mut cx, current_node);
            }
            current = state.borrow().next;
            state.borrow_mut().next = None;
        }

        // PORT: `next` is reset each outer iteration; the last `current` read
        // above already cleared it, matching Go's `var next *ast.Node`.
        let state = match Rc::try_unwrap(state) {
            Ok(s) => s.into_inner(),
            Err(_) => panic!("selection state still shared"),
        };
        state.ranges.build(root)
    }
}

/// Shared mutable state for the selection-range traversal (`next`, `ranges`,
/// `lastRange` in Go's closures).
struct SmartSelectionState {
    ranges: SelectionRangeBuilder,
    last_range: lsproto::Range,
    next: Option<NodeId>,
}

/// `nodeContainsPosition`.
fn node_contains_position(
    nodes: &[Node],
    file: NodeId,
    node: Option<NodeId>,
    pos: i32,
) -> bool {
    let Some(node) = node else {
        return false;
    };
    let start = tsc_scanner::scanner::get_token_pos_of_node(
        node,
        nodes[file].as_source_file(),
        true, /*includeJSDoc*/
        nodes,
    );
    let end = nodes[node].end();
    start <= pos && pos < end
}

/// `positionShouldSnapToNode`.
fn position_should_snap_to_node(
    nodes: &mut Vec<Node>,
    file: NodeId,
    node: NodeId,
    pos: i32,
) -> bool {
    if pos < nodes[node].end() {
        return true;
    }
    if nodes[node].end() == pos {
        let touching_property_name =
            tsc_astnav::tokens::get_touching_property_name(nodes, file, pos);
        return touching_property_name
            .is_some_and(|name| nodes[name].pos() < nodes[node].end());
    }
    false
}

/// `pushSelectionRange`.
fn push_selection_range(
    l: &LanguageService,
    st: &mut SmartSelectionState,
    cx: &VisitorCx<'_, '_>,
    file: NodeId,
    pos: i32,
    start: i32,
    end: i32,
) {
    if start == end {
        return;
    }

    if !(start <= pos && pos <= end) {
        return;
    }

    let script = source_file_script(file, cx.nodes);
    let (lsp_range, fidelity) = l.converters.to_lsp_range_for_feature(
        &script,
        TextRange::new(start, end),
        Feature::SelectionRanges,
    );
    if fidelity.is_none() {
        return;
    }

    if st.last_range == lsp_range {
        return;
    }
    st.last_range = lsp_range.clone();

    st.ranges.push(lsp_range);
}

/// `pushSelectionCommentRange`.
fn push_selection_comment_range(
    l: &LanguageService,
    st: &mut SmartSelectionState,
    cx: &VisitorCx<'_, '_>,
    file: NodeId,
    pos: i32,
    start: i32,
    end: i32,
) {
    push_selection_range(l, st, cx, file, pos, start, end);

    let mut comment_pos = start;
    let text = cx.nodes[file].as_source_file().text.clone();
    let bytes = text.as_bytes();
    while comment_pos < end
        && (comment_pos as usize) < bytes.len()
        && bytes[comment_pos as usize] == b'/'
    {
        comment_pos += 1;
    }
    push_selection_range(l, st, cx, file, pos, comment_pos, end);
}

/// `positionsAreOnSameLine`.
fn positions_are_on_same_line(nodes: &[Node], file: NodeId, pos1: i32, pos2: i32) -> bool {
    if pos1 == pos2 {
        return true;
    }
    let line_starts = nodes[file].as_source_file().ecma_line_map();
    tsc_scanner::scanner::compute_line_of_position(line_starts, pos1)
        == tsc_scanner::scanner::compute_line_of_position(line_starts, pos2)
}

/// `shouldSkipNode`.
fn should_skip_node(nodes: &[Node], node: NodeId, parent: NodeId) -> bool {
    if ast::is_block(&nodes[node]) {
        return true;
    }

    if ast::is_template_span(&nodes[node])
        || ast::is_template_head(&nodes[node])
        || ast::is_template_tail(&nodes[node])
    {
        return true;
    }

    if ast::is_variable_declaration_list(&nodes[node]) && ast::is_variable_statement(&nodes[parent])
    {
        return true;
    }

    // Skip lone variable declarations
    if ast::is_variable_declaration(&nodes[node])
        && ast::is_variable_declaration_list(&nodes[parent])
    {
        let decl = nodes[parent].as_variable_declaration_list();
        if decl
            .declarations
            .as_ref()
            .is_some_and(|d| d.nodes.len() == 1)
        {
            return true;
        }
    }

    if ast::is_js_doc_type_expression(&nodes[node])
        || ast::is_js_doc_signature(&nodes[node])
        || ast::is_js_doc_type_literal(&nodes[node])
    {
        return true;
    }

    false
}

/// `getSelectionChildren`.
fn get_selection_children(
    nodes: &mut Vec<Node>,
    factory: &mut NodeFactory,
    node: NodeId,
    source_file: NodeId,
) -> Vec<NodeId> {
    if !ast::is_mapped_type_node(&nodes[node]) {
        return get_children_from_non_jsdoc_node(nodes, node, source_file);
    }

    let children = get_children_from_non_jsdoc_node(nodes, node, source_file);
    if children.len() < 2 {
        return children;
    }

    let open_brace_token = children[0];
    let close_brace_token = children[children.len() - 1];
    if nodes[open_brace_token].kind != Kind::OpenBraceToken
        || nodes[close_brace_token].kind != Kind::CloseBraceToken
    {
        return children;
    }

    let (readonly_token, question_token) = {
        let mapped_type = nodes[node].as_mapped_type_node();
        (mapped_type.readonly_token, mapped_type.question_token)
    };
    let children = children[1..children.len() - 1].to_vec();

    // Group `-/+readonly` and `-/+?`.
    let grouped_with_plus_minus_tokens =
        group_children(nodes, factory, &children, &mut |nodes, child| {
            Some(child) == readonly_token
                || nodes[child].kind == Kind::ReadonlyKeyword
                || Some(child) == question_token
                || nodes[child].kind == Kind::QuestionToken
        });

    // Group the type parameter with its surrounding brackets.
    let grouped_with_brackets = group_children(
        nodes,
        factory,
        &grouped_with_plus_minus_tokens,
        &mut |nodes, child| {
            nodes[child].kind == Kind::OpenBracketToken
                || nodes[child].kind == Kind::TypeParameter
                || nodes[child].kind == Kind::CloseBracketToken
        },
    );

    // Go exposes the trailing semicolon directly, so keep it in the right-hand
    // group to produce the same effective selection tree as Strada.
    let split = split_children(
        nodes,
        factory,
        &grouped_with_brackets,
        &mut |nodes, child| nodes[child].kind == Kind::ColonToken,
        false, /*separateTrailingSemicolon*/
    );
    vec![
        open_brace_token,
        create_syntax_list(factory, nodes, &split),
        close_brace_token,
    ]
}

/// `groupChildren`.
fn group_children(
    nodes: &mut Vec<Node>,
    factory: &mut NodeFactory,
    children: &[NodeId],
    group_on: &mut dyn FnMut(&[Node], NodeId) -> bool,
) -> Vec<NodeId> {
    let mut result: Vec<NodeId> = Vec::new();
    let mut group: Vec<NodeId> = Vec::new();
    for &child in children {
        if group_on(nodes, child) {
            group.push(child);
        } else {
            if !group.is_empty() {
                result.push(create_syntax_list(factory, nodes, &group));
                group = Vec::new();
            }
            result.push(child);
        }
    }
    if !group.is_empty() {
        result.push(create_syntax_list(factory, nodes, &group));
    }
    result
}

/// `splitChildren`.
fn split_children(
    nodes: &mut Vec<Node>,
    factory: &mut NodeFactory,
    children: &[NodeId],
    pivot_on: &mut dyn FnMut(&[Node], NodeId) -> bool,
    separate_trailing_semicolon: bool,
) -> Vec<NodeId> {
    if children.len() < 2 {
        return children.to_vec();
    }

    let mut split_token_index: i32 = -1;
    for (i, &child) in children.iter().enumerate() {
        if pivot_on(nodes, child) {
            split_token_index = i as i32;
            break;
        }
    }
    if split_token_index == -1 {
        return children.to_vec();
    }
    let split_token_index = split_token_index as usize;

    let left_children = &children[..split_token_index];
    let split_token = children[split_token_index];
    let last_token = children[children.len() - 1];
    let separate_last_token =
        separate_trailing_semicolon && nodes[last_token].kind == Kind::SemicolonToken;
    let mut right_end = children.len();
    if separate_last_token {
        right_end -= 1;
    }
    let right_children = &children[split_token_index + 1..right_end];

    let mut result: Vec<NodeId> = Vec::with_capacity(4);
    if !left_children.is_empty() {
        result.push(create_syntax_list(factory, nodes, left_children));
    }
    result.push(split_token);
    if !right_children.is_empty() {
        result.push(create_syntax_list(factory, nodes, right_children));
    }
    if separate_last_token {
        result.push(last_token);
    }
    result
}

/// `createSyntaxList`.
fn create_syntax_list(
    factory: &mut NodeFactory,
    nodes: &mut Vec<Node>,
    children: &[NodeId],
) -> NodeId {
    let list = factory.new_syntax_list(nodes, children);
    nodes[list].loc = TextRange::new(
        nodes[children[0]].pos(),
        nodes[children[children.len() - 1]].end(),
    );
    list
}

/// `visit` — the per-child callback inside `getSmartSelectionRange`, usable
/// both through the `NodeVisitor` and directly for JSDoc children.
fn visit_smart_selection(
    l: &LanguageService,
    state: &Rc<RefCell<SmartSelectionState>>,
    nodes: &mut Vec<Node>,
    factory: &mut NodeFactory,
    file: NodeId,
    pos: i32,
    parent: NodeId,
    node: NodeId,
) {
    let mut st = state.borrow_mut();
    let mut cx = VisitorCx {
        nodes,
        factory,
    };
    visit_smart_selection_cx(l, &mut st, &mut cx, file, pos, parent, node);
}

/// Body of the `visit` closure.
fn visit_smart_selection_cx(
    l: &LanguageService,
    st: &mut SmartSelectionState,
    cx: &mut VisitorCx<'_, '_>,
    file: NodeId,
    pos: i32,
    parent: NodeId,
    node: NodeId,
) {
    if st.next.is_none() {
        let text = cx.nodes[file].as_source_file().text.clone();
        let found_comment = tsc_scanner::scanner::get_trailing_comment_ranges(
            cx.factory,
            &text,
            cx.nodes[node].end(),
        )
        .into_iter()
        .next();
        if let Some(found_comment) = found_comment
            && found_comment.kind == Kind::SingleLineCommentTrivia
        {
            push_selection_comment_range(
                l,
                st,
                cx,
                file,
                pos,
                found_comment.text_range.pos(),
                found_comment.text_range.end(),
            );
        }

        if node_contains_position(cx.nodes, file, Some(node), pos) {
            // Add range for multi-line function bodies before skipping the block
            if ast::is_block(&cx.nodes[node])
                && ast::is_function_like_declaration(Some(parent), cx.nodes)
            {
                let block_start = tsc_astnav::tokens::get_start_of_node(
                    cx.nodes,
                    file,
                    node,
                    false, /*includeJSDoc*/
                );
                let block_end = cx.nodes[node].end();
                if !positions_are_on_same_line(cx.nodes, file, block_start, block_end) {
                    push_selection_range(l, st, cx, file, pos, block_start, block_end);
                }
            }

            // Synthesize a stop for '${ ... }' since '${' and '}' actually belong to siblings.
            if ast::is_template_span(&cx.nodes[parent]) {
                let template_span = cx.nodes[parent].as_template_span();
                if let Some(literal) = template_span.literal {
                    // Start from just before the '${' and end after the '}'
                    // The '${' is 2 characters before the expression start
                    let span_start = cx.nodes[node].pos() - 2;
                    // The '}' is the first character of the template literal (middle or tail)
                    let span_end = tsc_astnav::tokens::get_start_of_node(
                        cx.nodes,
                        file,
                        literal,
                        false, /*includeJSDoc*/
                    ) + 1;
                    // Validate the positions are reasonable
                    let text = cx.nodes[file].as_source_file().text.clone();
                    if span_start >= 0
                        && span_end <= text.len() as i32
                        && span_start < span_end
                    {
                        push_selection_range(l, st, cx, file, pos, span_start, span_end);
                    }
                }
            }

            if !should_skip_node(cx.nodes, node, parent) {
                let start = tsc_astnav::tokens::get_start_of_node(
                    cx.nodes,
                    file,
                    node,
                    false, /*includeJSDoc*/
                );
                let end = cx.nodes[node].end();
                push_selection_range(l, st, cx, file, pos, start, end);

                if ast::is_mapped_type_node(&cx.nodes[node]) {
                    let mut selection_parent = node;
                    loop {
                        let mut selection_child: Option<NodeId> = None;
                        for child in get_selection_children(
                            cx.nodes,
                            cx.factory,
                            selection_parent,
                            file,
                        ) {
                            let child_start = tsc_scanner::scanner::get_token_pos_of_node(
                                child,
                                cx.nodes[file].as_source_file(),
                                true, /*includeJSDoc*/
                                cx.nodes,
                            );
                            if child_start > pos {
                                break;
                            }
                            if position_should_snap_to_node(cx.nodes, file, child, pos) {
                                push_selection_range(
                                    l,
                                    st,
                                    cx,
                                    file,
                                    pos,
                                    child_start,
                                    cx.nodes[child].end(),
                                );
                                selection_child = Some(child);
                                break;
                            }
                        }
                        let Some(selection_child) = selection_child else {
                            break;
                        };
                        if !ast::is_syntax_list(&cx.nodes[selection_child]) {
                            break;
                        }
                        selection_parent = selection_child;
                    }
                }

                // String literals should have a stop both inside and outside their quotes.
                if ast::is_string_literal(&cx.nodes[node])
                    || cx.nodes[node].kind == Kind::TemplateExpression
                    || cx.nodes[node].kind == Kind::NoSubstitutionTemplateLiteral
                {
                    // Only add inner content range if there's actually content (handles unterminated literals)
                    if start + 1 < end - 1 {
                        push_selection_range(l, st, cx, file, pos, start + 1, end - 1);
                    }
                }
            }

            st.next = Some(node);
        }
    }
}
