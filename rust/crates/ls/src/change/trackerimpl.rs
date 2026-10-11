// Ported from tsc/internal/ls/change/trackerimpl.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{ArenaCell, Kind, Node, NodeId, self as ast};
use tsc_astnav::tokens as astnav;
use tsc_core::text::{TextPos, TextRange};
use tsc_format as format;
use tsc_lsproto::{self as lsproto, Position, Range, TextEdit};
use tsc_lsutil as lsutil;
use tsc_lsutil::FormatCodeSettings;
use tsc_parser as parser;
use tsc_printer as printer;
use tsc_scanner::scanner;
use tsc_spanmap as spanmap;
use tsc_stringutil as stringutil;
use tsc_tspath::RootedFilePath;

use super::tracker::{
    LeadingTriviaOption, NodeOptions, Tracker, TrackerEdit, TrackerEditKind, TrailingTriviaOption,
    positions_are_on_same_line,
};

impl<'a, 'c> Tracker<'a, 'c> {
    /// `getTextChangesFromChanges`.
    pub(crate) fn get_text_changes_from_changes(
        &mut self,
    ) -> FxHashMap<RootedFilePath, Vec<TextEdit>> {
        let mut changes: FxHashMap<RootedFilePath, Vec<TextEdit>> = FxHashMap::default();
        // A content-mapped file can have several projections, each keyed separately in t.changes but
        // all sharing one original file. Their edits are collected together before being ordered and checked,
        // so duplicate edits are emitted once and conflicting edits are rejected regardless of map iteration
        // order.
        let mut projections: FxHashMap<RootedFilePath, usize> = FxHashMap::default();
        // PORT: clone the entries so the arena borrows inside the loop do not
        // conflict with `&mut self` (Go mutates no maps here either).
        let entries: Vec<(NodeId, Vec<TrackerEdit>)> = self
            .changes
            .m
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        for (source_file, changes_in_file) in entries {
            let Some(handle) = self
                .arena_handles
                .get(&(source_file.file_index() as u32))
                .cloned()
            else {
                continue;
            };
            let file_name = {
                let n = handle.borrow();
                n[source_file]
                    .as_source_file()
                    .original_file_name(&n)
                    .clone()
            };
            if self.unmappable_files.has(&file_name) {
                continue;
            }
            // For a content-mapped file, a mapper may reorder source text relative to the original document.
            // Convert first, then sort and check for overlap in the space where edits are actually applied.
            let text_changes: Vec<TextEdit> = changes_in_file
                .iter()
                .map(|change| {
                    // !!! targetSourceFile
                    let new_text = self.compute_new_text(change, source_file, source_file, &handle);
                    // span := createTextSpanFromRange(c.Range)
                    // !!!
                    // Filter out redundant changes.
                    // if (span.length == newText.length && stringContainsAt(targetSourceFile.text, newText, span.start)) { return nil }
                    let range = {
                        let n = handle.borrow();
                        self.to_lsp_edit_range(&n, source_file, change.range)
                    };
                    TextEdit { new_text, range }
                })
                .collect();

            if !text_changes.is_empty() {
                changes
                    .entry(file_name.clone())
                    .or_default()
                    .extend(text_changes);
                *projections.entry(file_name).or_insert(0) += 1;
            }
        }

        for (file_name, text_changes) in changes.iter_mut() {
            // Converting the edits above may have found that this file cannot be represented in its original
            // text. GetChanges drops it, so its order does not matter, and the best-effort ranges left behind
            // may overlap in ways the check below would refuse.
            if self.unmappable_files.has(file_name) {
                continue;
            }
            // order changes by start position
            // If the start position is the same, put the shorter range first, since an empty range (x, x) may precede (x, y) but not vice-versa.
            text_changes.sort_by(|a, b| lsproto::compare_ranges(&a.range, &b.range).cmp(&0));
            let multiple = projections.get(file_name).copied().unwrap_or(0) > 1;
            if multiple {
                *text_changes = dedupe_identical_edits(std::mem::take(text_changes));
            }
            // verify that change intervals do not overlap, except possibly at end points.
            for i in 0..text_changes.len().saturating_sub(1) {
                if text_edits_conflict(&text_changes[i], &text_changes[i + 1], multiple) {
                    if multiple {
                        // Projections of one original range disagree about how to edit it. That is a property of
                        // the mapper's output rather than a bug here, so drop the file instead of failing.
                        let file_name = file_name.clone();
                        self.unmappable_files.add(file_name);
                        break;
                    }
                    // assert change[i].End <= change[i + 1].Start
                    panic!(
                        "changes overlap: {:?} and {:?}",
                        text_changes[i].range,
                        text_changes[i + 1].range
                    );
                }
            }
        }
        changes
    }

    /// `computeNewText`.
    fn compute_new_text(
        &mut self,
        change: &TrackerEdit,
        target_source_file: NodeId,
        source_file: NodeId,
        handle: &Rc<ArenaCell>,
    ) -> String {
        match change.kind {
            TrackerEditKind::Remove => return String::new(),
            TrackerEditKind::Text => return change.new_text.clone(),
            _ => {}
        }

        let projections_and_pos: Vec<(NodeId, TextPos)> = {
            let n = handle.borrow();
            let start = self.to_lsp_edit_range(&n, source_file, change.range).start;
            self.converters
                .from_lsp_position_for_source_file(source_file, &n, start, spanmap::Feature::All)
                .iter()
                .filter(|m| m.fidelity.is_exact())
                .map(|m| (m.script.file, m.position))
                .collect()
        };
        let mut result = String::new();
        let mut found = false;
        // The original range may have multiple verbatim copies; it is safe to
        // lose their identity only when formatting at every exact projection
        // produces the same edit.
        for (projection, pos) in projections_and_pos {
            let text = match change.kind {
                TrackerEditKind::ReplaceWithMultipleNodes => {
                    let joiner = if change.options.joiner.is_empty() {
                        self.new_line.clone()
                    } else {
                        change.options.joiner.clone()
                    };
                    change
                        .nodes
                        .iter()
                        .map(|&n| {
                            let formatted = self.get_formatted_text_of_node(
                                n,
                                target_source_file,
                                projection,
                                pos,
                                &change.options,
                                handle,
                            );
                            match formatted.strip_suffix(&self.new_line) {
                                Some(s) => s.to_string(),
                                None => formatted,
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(&joiner)
                }
                TrackerEditKind::ReplaceWithSingleNode => self.get_formatted_text_of_node(
                    change.node,
                    target_source_file,
                    projection,
                    pos,
                    &change.options,
                    handle,
                ),
                kind => panic!("change kind {:?} should have been handled earlier", kind),
            };
            // Strip initial indentation if text will be inserted in the middle of the line.
            let no_indent_owned;
            let mut no_indent = text.as_str();
            if !(change.options.indentation.is_some()
                || format::get_line_start_position_for_position(pos, projection, &handle.borrow())
                    == pos)
            {
                no_indent_owned = text.trim_start().to_string();
                no_indent = &no_indent_owned;
            }
            let candidate = format!(
                "{}{}{}",
                change.options.prefix,
                no_indent,
                if no_indent.ends_with(&change.options.suffix) {
                    ""
                } else {
                    &change.options.suffix
                }
            );
            if found && candidate != result {
                let file_name = {
                    let n = handle.borrow();
                    n[source_file]
                        .as_source_file()
                        .original_file_name(&n)
                        .clone()
                };
                self.unmappable_files.add(file_name);
                return String::new();
            }
            result = candidate;
            found = true;
        }
        if !found {
            let file_name = {
                let n = handle.borrow();
                n[source_file]
                    .as_source_file()
                    .original_file_name(&n)
                    .clone()
            };
            self.unmappable_files.add(file_name);
        }
        self.reindent_inserted_lines(source_file, change, &result, handle)
    }

    /// `reindentInsertedLines` fixes the indentation of a line an insertion
    /// introduces into the document the edit is applied to. The inserted text
    /// forms its own line when it ends in a newline, and that line has to pick
    /// up the indentation of the line it is being spliced into. Where the
    /// indentation goes depends on which side of the insertion point it
    /// already sits on:
    ///
    ///   - Inserting after a line's indentation (`\t\tfoo` with the point
    ///     before `foo`) leaves the inserted text indented but pushes the rest
    ///     of the line down bare, so the indentation is repeated after the
    ///     text.
    ///   - Inserting at the very start of a line leaves the existing text
    ///     indented but puts the inserted text at column zero, so the
    ///     indentation is emitted before the text.
    ///
    /// The indentation is read from the original text at the edit's original
    /// position, so it holds for a content-mapped file whose projection is
    /// indented differently from the document the edit is applied to.
    /// Edits carrying an explicit indentation option are left alone.
    fn reindent_inserted_lines(
        &mut self,
        source_file: NodeId,
        change: &TrackerEdit,
        text: &str,
        handle: &Rc<ArenaCell>,
    ) -> String {
        if text.is_empty()
            || change.range.pos() != change.range.end()
            || change.options.indentation.is_some()
        {
            return text.to_string();
        }
        if !text.ends_with(&self.new_line) {
            return text.to_string();
        }
        let (original, span_map) = {
            let n = handle.borrow();
            let sf = n[source_file].as_source_file();
            (sf.original_text().to_string(), sf.span_map())
        };
        let mut pos = change.range.pos();
        if let Some(spans) = span_map {
            let (mapped, fidelity) =
                spanmap::SpanMap::virtual_to_original_position(Some(&spans), pos);
            if !fidelity.is_exact() {
                return text.to_string();
            }
            pos = mapped;
        }
        if pos < 0 || pos as usize > original.len() {
            return text.to_string();
        }
        let line_start = original[..pos as usize]
            .rfind(|c| c == '\r' || c == '\n')
            .map(|i| i + 1)
            .unwrap_or(0);
        let before_point = &original[line_start..pos as usize];
        if before_point.is_empty() {
            // At the start of a line: the existing text keeps its indentation, and the inserted line needs it —
            // but only when the formatter left the text at column zero. Where the formatter already indented it
            // (inserting into a multi-line list, say), that indentation is the correct one.
            if !leading_indentation(text).is_empty() {
                return text.to_string();
            }
            return format!("{}{}", leading_indentation(&original[line_start..]), text);
        }
        if leading_indentation(before_point) != before_point {
            return text.to_string();
        }
        // Just past the indentation: the inserted line already has it, the text pushed down needs it back.
        format!("{}{}", text, before_point)
    }

    /// `getFormattedTextOfNode`.
    fn get_formatted_text_of_node(
        &mut self,
        node_in: NodeId,
        target_source_file: NodeId,
        source_file: NodeId,
        pos: TextPos,
        options: &NodeOptions,
        handle: &Rc<ArenaCell>,
    ) -> String {
        let (text, source_file_like) =
            self.get_nonformatted_text(node_in, target_source_file, handle);
        // !!! if (validate) validate(node, text);
        let mut n = handle.borrow_mut();
        let format_options = get_format_code_settings_for_writing(
            self.format_settings.clone(),
            target_source_file,
            &mut n,
        );

        let initial_indentation;
        let mut delta = 0;
        match options.indentation {
            None => {
                let assume = options.prefix == self.new_line
                    || format::get_line_start_position_for_position(pos, source_file, &n) == pos;
                initial_indentation =
                    format::get_indentation(pos, source_file, &format_options, assume, &mut n);
            }
            Some(i) => initial_indentation = i,
        }

        if let Some(d) = options.delta {
            delta = d;
        } else if format_options.editor_settings.indent_size != 0
            && format::should_indent_child_node(&format_options, node_in, None, None, false, &mut n)
        {
            delta = format_options.editor_settings.indent_size;
        }

        let language_variant = n[target_source_file].as_source_file().language_variant;
        let changes = format::format_node_given_indentation(
            &self.ctx,
            source_file_like,
            source_file_like,
            language_variant,
            initial_indentation,
            delta,
            &mut n,
        );
        drop(n);
        tsc_core::textchange::apply_bulk_edits(&text, &changes)
    }

    /// `getNonformattedText`.
    fn get_nonformatted_text(
        &mut self,
        node: NodeId,
        source_file: NodeId,
        handle: &Rc<ArenaCell>,
    ) -> (String, NodeId) {
        let mut n = handle.borrow_mut();
        // PORT: Go passes `t.NodeFactory` — i.e. the emitContext's factory —
        // to both printer helpers. Rust cannot mutably borrow `emit_context`
        // and `emit_context.factory` simultaneously; a scratch
        // `ast::NodeFactory` (its `file_index` bound to this arena) is used
        // for the position-assignment clones instead. Its `on_clone`/
        // `on_update` hooks are unused: the emit tracking they would record
        // has no consumer after printing, since the returned text and the
        // synthetic file only feed the formatter.
        let mut factory = ast::NodeFactory::new(ast::NodeFactoryHooks::default());
        factory.set_file_index(source_file.file_index() as u32);
        let (text, node_out) = printer::print_and_position_node(
            &mut n,
            &mut factory,
            node,
            Some(source_file),
            &self.new_line,
            self.format_settings.editor_settings.indent_size,
            &mut self.emit_context,
        );
        let parse_options = ast::parseoptions::SourceFileParseOptions {
            file_name: n[source_file].as_source_file().file_name().clone(),
            path_key: n[source_file].as_source_file().path_key().clone(),
            ..Default::default()
        };
        let source_file_like = printer::create_synthetic_source_file(
            &mut n,
            &mut factory,
            node_out,
            &text,
            &parse_options,
        );
        (text, source_file_like)
    }

    /// `GetAdjustedRange` computes the adjusted range for a node in a source
    /// file, accounting for trivia.
    pub fn get_adjusted_range(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        start_node: NodeId,
        end_node: NodeId,
        leading_option: LeadingTriviaOption,
        trailing_option: TrailingTriviaOption,
    ) -> TextRange {
        TextRange::new(
            self.get_adjusted_start_position(nodes, source_file, start_node, leading_option, false),
            self.get_adjusted_end_position(nodes, source_file, end_node, trailing_option),
        )
    }

    /// `getAdjustedStartPosition`.
    pub(crate) fn get_adjusted_start_position(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        leading_option: LeadingTriviaOption,
        has_trailing_comment: bool,
    ) -> TextPos {
        let mut n = self.borrow_nodes(nodes, source_file);
        if leading_option == LeadingTriviaOption::JSDoc {
            let js_doc_comments = parser::get_jsdoc_comment_ranges(
                &self.emit_context.factory,
                Vec::new(),
                node,
                n[source_file].as_source_file().text(),
                &n,
            );
            if let Some(first) = js_doc_comments.first() {
                return format::get_line_start_position_for_position(
                    first.text_range.pos(),
                    source_file,
                    &n,
                );
            }
        }

        let start = astnav::get_start_of_node(&mut n, source_file, node, false);
        let start_of_line_pos =
            format::get_line_start_position_for_position(start, source_file, &n);

        match leading_option {
            LeadingTriviaOption::Exclude => return start,
            LeadingTriviaOption::StartLine => {
                if n[node].loc.contains_inclusive(start_of_line_pos) {
                    return start_of_line_pos;
                }
                return start;
            }
            _ => {}
        }

        let full_start = n[node].pos();
        if full_start == start {
            return start;
        }
        let line_starts = n[source_file].as_source_file().ecma_line_map();
        let full_start_line_index = scanner::compute_line_of_position(line_starts, full_start);
        let full_start_line_pos = line_starts[full_start_line_index as usize];
        if start_of_line_pos == full_start_line_pos {
            // full start and start of the node are on the same line
            //   a,     b;
            //    ^     ^
            //    |   start
            // fullstart
            // when b is replaced - we usually want to keep the leading trivia
            // when b is deleted - we delete it
            if leading_option == LeadingTriviaOption::IncludeAll {
                return full_start;
            }
            return start;
        }

        // if node has a trailing comments, use comment end position as the text has already been included.
        if has_trailing_comment {
            // Check first for leading comments as if the node is the first import, we want to exclude the trivia;
            // otherwise we get the trailing comments.
            let mut comments = scanner::get_leading_comment_ranges(
                &self.emit_context.factory,
                n[source_file].as_source_file().text(),
                full_start,
            );
            if comments.is_empty() {
                comments = scanner::get_trailing_comment_ranges(
                    &self.emit_context.factory,
                    n[source_file].as_source_file().text(),
                    full_start,
                );
            }
            if let Some(first) = comments.first() {
                return scanner::skip_trivia_ex(
                    n[source_file].as_source_file().text(),
                    first.text_range.end(),
                    Some(&scanner::SkipTriviaOptions {
                        stop_after_line_break: true,
                        stop_at_comments: true,
                        ..Default::default()
                    }),
                );
            }
        }

        // get start position of the line following the line that contains fullstart position
        // (but only if the fullstart isn't the very beginning of the file)
        let next_line_start = if full_start > 0 { 1 } else { 0 };
        let adjusted_start_position =
            line_starts[(full_start_line_index + next_line_start) as usize];
        // skip whitespaces/newlines
        let adjusted_start_position = scanner::skip_trivia_ex(
            n[source_file].as_source_file().text(),
            adjusted_start_position,
            Some(&scanner::SkipTriviaOptions {
                stop_at_comments: true,
                ..Default::default()
            }),
        );
        line_starts
            [scanner::compute_line_of_position(line_starts, adjusted_start_position) as usize]
    }

    /// `getEndPositionOfMultilineTrailingComment` — return the end position of
    /// a multiline comment if it is on another line; otherwise returns 0 (Go's
    /// -1 sentinel is 0 here as callers only check `!= 0`).
    fn get_end_position_of_multiline_trailing_comment(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        trailing_opt: TrailingTriviaOption,
    ) -> TextPos {
        if trailing_opt == TrailingTriviaOption::Include {
            // If the trailing comment is a multiline comment that extends to the next lines,
            // return the end of the comment and track it for the next nodes to adjust.
            let n = nodes.snapshot();
            let line_starts = n[source_file].as_source_file().ecma_line_map();
            let node_end_line = scanner::compute_line_of_position(line_starts, n[node].end());
            for comment in scanner::get_trailing_comment_ranges(
                &self.emit_context.factory,
                n[source_file].as_source_file().text(),
                n[node].end(),
            ) {
                // Single line can break the loop as trivia will only be this line.
                // Comments on subsequent lines are also ignored.
                if comment.kind == Kind::SingleLineCommentTrivia
                    || scanner::compute_line_of_position(line_starts, comment.text_range.pos())
                        > node_end_line
                {
                    break;
                }

                // Get the end line of the comment and compare against the end line of the node.
                // If the comment end line position and the multiline comment extends to multiple lines,
                // then is safe to return the end position.
                let comment_end_line =
                    scanner::compute_line_of_position(line_starts, comment.text_range.end());
                if comment_end_line > node_end_line {
                    return scanner::skip_trivia_ex(
                        n[source_file].as_source_file().text(),
                        comment.text_range.end(),
                        Some(&scanner::SkipTriviaOptions {
                            stop_after_line_break: true,
                            stop_at_comments: true,
                            ..Default::default()
                        }),
                    );
                }
            }
        }

        0
    }

    /// `getAdjustedEndPosition`.
    pub(crate) fn get_adjusted_end_position(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        trailing_option: TrailingTriviaOption,
    ) -> TextPos {
        if trailing_option == TrailingTriviaOption::Exclude {
            return self.borrow_nodes(nodes, source_file)[node].end();
        }
        let mut n = self.borrow_nodes(nodes, source_file);
        if trailing_option == TrailingTriviaOption::ExcludeWhitespace {
            let mut comments = scanner::get_trailing_comment_ranges(
                &self.emit_context.factory,
                n[source_file].as_source_file().text(),
                n[node].end(),
            );
            comments.extend(scanner::get_leading_comment_ranges(
                &self.emit_context.factory,
                n[source_file].as_source_file().text(),
                n[node].end(),
            ));
            if let Some(last) = comments.last() {
                let real_end = last.text_range.end();
                if real_end != 0 {
                    return real_end;
                }
            }
            return n[node].end();
        }

        let node_end = n[node].end();
        drop(n);
        let multiline_end_position = self.get_end_position_of_multiline_trailing_comment(
            nodes,
            source_file,
            node,
            trailing_option,
        );
        let mut n = self.borrow_nodes(nodes, source_file);
        if multiline_end_position != 0 {
            return multiline_end_position;
        }

        let new_end = scanner::skip_trivia_ex(
            n[source_file].as_source_file().text(),
            node_end,
            Some(&scanner::SkipTriviaOptions {
                stop_after_line_break: true,
                ..Default::default()
            }),
        );

        if new_end != node_end
            && (trailing_option == TrailingTriviaOption::Include
                || new_end > 0
                    && is_line_break_at(n[source_file].as_source_file().text(), new_end - 1))
        {
            return new_end;
        }
        node_end
    }

    /// `getInsertionPositionAtSourceFileTop`.
    pub(crate) fn get_insertion_position_at_source_file_top(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
    ) -> TextPos {
        let mut n = self.borrow_nodes(nodes, source_file);
        let mut last_prologue: Option<NodeId> = None;
        for &node in n[source_file]
            .as_source_file()
            .statements
            .as_ref()
            .map(|l| &l.nodes[..])
            .unwrap_or_default()
            .iter()
        {
            if ast::is_prologue_directive(&n[node], &n) {
                last_prologue = Some(node);
            } else {
                break;
            }
        }

        let mut position: TextPos = 0;
        let text = n[source_file].as_source_file().text().to_string();
        macro_rules! advance_past_line_break {
            () => {
                if position < text.len() as i32 {
                    let char = text.as_bytes()[position as usize] as char;
                    if stringutil::is_line_break(char) {
                        position += 1;
                        if (position as usize) < text.len()
                            && char == '\r'
                            && text.as_bytes()[position as usize] == b'\n'
                        {
                            position += 1;
                        }
                    }
                }
            };
        }
        if let Some(last_prologue) = last_prologue {
            position = n[last_prologue].end();
            advance_past_line_break!();
            return position;
        }

        let shebang = scanner::get_shebang(&text);
        if !shebang.is_empty() {
            position = shebang.len() as i32;
            advance_past_line_break!();
        }

        let ranges =
            scanner::get_leading_comment_ranges(&self.emit_context.factory, &text, position);
        if ranges.is_empty() {
            return position;
        }
        // Find the first attached comment to the first node and add before it
        let mut last_comment: Option<ast::CommentRange> = None;
        let mut pinned_or_triple_slash = false;
        let mut first_node_line: i32 = -1;

        let len_statements = n[source_file]
            .as_source_file()
            .statements
            .as_ref()
            .map(|l| l.nodes.len())
            .unwrap_or(0);
        let line_map: Vec<TextPos> = n[source_file].as_source_file().ecma_line_map().to_vec();
        for r in ranges {
            if r.kind == Kind::MultiLineCommentTrivia {
                if printer::is_pinned_comment(&text, r) {
                    last_comment = Some(r);
                    pinned_or_triple_slash = true;
                    continue;
                }
            } else if printer::is_recognized_triple_slash_comment(&text, r) {
                last_comment = Some(r);
                pinned_or_triple_slash = true;
                continue;
            }

            if let Some(lc) = last_comment {
                // Always insert after pinned or triple slash comments
                if pinned_or_triple_slash {
                    break;
                }

                // There was a blank line between the last comment and this comment.
                // This comment is not part of the copyright comments
                let comment_line = scanner::compute_line_of_position(&line_map, r.text_range.pos());
                let last_comment_end_line =
                    scanner::compute_line_of_position(&line_map, lc.text_range.end());
                if comment_line >= last_comment_end_line + 2 {
                    break;
                }
            }

            if len_statements > 0 {
                if first_node_line == -1 {
                    let first_statement = n[source_file]
                        .as_source_file()
                        .statements
                        .as_ref()
                        .unwrap()
                        .nodes[0];
                    first_node_line = scanner::compute_line_of_position(
                        &line_map,
                        astnav::get_start_of_node(&mut n, source_file, first_statement, false),
                    );
                }
                let comment_end_line =
                    scanner::compute_line_of_position(&line_map, r.text_range.end());
                if first_node_line < comment_end_line + 2 {
                    break;
                }
            }
            last_comment = Some(r);
            pinned_or_triple_slash = false;
        }

        if let Some(lc) = last_comment {
            position = lc.text_range.end();
            advance_past_line_break!();
        }
        position
    }
}

/// `dedupeIdenticalEdits` drops exact duplicates from a sorted slice of edits.
/// When a mapper copies one span of the original into more than one
/// projection, an edit computed against each projection describes the same
/// change to the same original range; emitting it once per projection would
/// apply it repeatedly.
fn dedupe_identical_edits(edits: Vec<TextEdit>) -> Vec<TextEdit> {
    let mut deduped: Vec<TextEdit> = Vec::with_capacity(edits.len());
    for edit in edits {
        if let Some(last) = deduped.last() {
            if last.range == edit.range && last.new_text == edit.new_text {
                continue;
            }
        }
        deduped.push(edit);
    }
    deduped
}

/// `textEditsConflict`.
fn text_edits_conflict(a: &TextEdit, b: &TextEdit, multiple_projections: bool) -> bool {
    if lsproto::compare_positions(&a.range.end, &b.range.start) > 0 {
        return true;
    }
    // Different insertions at the same position are ambiguous when they may come from different projections.
    multiple_projections
        && a.range.start == a.range.end
        && a.range == b.range
        && a.new_text != b.new_text
}

/// `leadingIndentation`.
fn leading_indentation(text: &str) -> &str {
    let mut end = 0;
    let bytes = text.as_bytes();
    while end < bytes.len() && (bytes[end] == b' ' || bytes[end] == b'\t') {
        end += 1;
    }
    &text[..end]
}

/// `GetFormatCodeSettingsForWriting`.
pub fn get_format_code_settings_for_writing(
    mut options: FormatCodeSettings,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> FormatCodeSettings {
    let should_auto_detect_semicolon_preference =
        options.semicolons == lsutil::SemicolonPreference::IGNORE;
    let should_remove_semicolons = options.semicolons == lsutil::SemicolonPreference::REMOVE
        || should_auto_detect_semicolon_preference
            && !lsutil::probably_uses_semicolons(nodes, source_file);
    if should_remove_semicolons {
        options.semicolons = lsutil::SemicolonPreference::REMOVE;
    }
    options
}

/// `hasCommentsBeforeLineBreak`.
pub(crate) fn has_comments_before_line_break(text: &str, start: TextPos) -> bool {
    for ch in text[start as usize..].chars() {
        if !stringutil::is_white_space_single_line(ch) {
            return ch == '/';
        }
    }
    false
}

/// `needSemicolonBetween`.
pub(crate) fn need_semicolon_between(nodes: &[Node], a: NodeId, b: NodeId) -> bool {
    (ast::is_property_signature_declaration(&nodes[a]) || ast::is_property_declaration(&nodes[a]))
        && ast::is_class_or_type_element(&nodes[b])
        && nodes[b]
            .name()
            .is_some_and(|name| nodes[name].kind == Kind::ComputedPropertyName)
        || ast::is_statement_but_not_declaration(&nodes[a])
            && ast::is_statement_but_not_declaration(&nodes[b])
    // TODO: only if b would start with a `(` or `[`
}

/// `isLineBreakAt` — `stringutil.IsLineBreak(rune(text[pos]))` at a byte
/// offset (Go indexes strings by byte).
fn is_line_break_at(text: &str, pos: TextPos) -> bool {
    pos >= 0
        && (pos as usize) < text.len()
        && stringutil::is_line_break(text.as_bytes()[pos as usize] as char)
}

/// `startPositionToDeleteNodeInList` finds the first non-whitespace position
/// in the leading trivia of the node.
impl<'a, 'c> Tracker<'a, 'c> {
    pub(crate) fn start_position_to_delete_node_in_list(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
    ) -> TextPos {
        let start = self.get_adjusted_start_position(
            nodes,
            source_file,
            node,
            LeadingTriviaOption::IncludeAll,
            false,
        );
        let n = nodes.snapshot();
        scanner::skip_trivia_ex(
            n[source_file].as_source_file().text(),
            start,
            Some(&scanner::SkipTriviaOptions {
                stop_after_line_break: false,
                stop_at_comments: true,
                ..Default::default()
            }),
        )
    }

    /// `endPositionToDeleteNodeInList`.
    pub(crate) fn end_position_to_delete_node_in_list(
        &mut self,
        nodes: &Rc<ArenaCell>,
        source_file: NodeId,
        node: NodeId,
        prev_node: Option<NodeId>,
        next_node: NodeId,
    ) -> TextPos {
        let end = self.start_position_to_delete_node_in_list(nodes, source_file, next_node);
        let node_end_adjusted =
            self.get_adjusted_end_position(nodes, source_file, node, TrailingTriviaOption::Include);
        {
            let n = nodes.snapshot();
            if prev_node.is_none()
                || positions_are_on_same_line(node_end_adjusted, end, source_file, &n)
            {
                return end;
            }
        }
        let (token, prev_token, token_end, prev_start, token_start) = {
            let mut n = nodes.cow();
            let next_start = astnav::get_start_of_node(&mut n, source_file, next_node, false);
            let token = astnav::find_preceding_token(&mut n, source_file, next_start);
            if let Some(token) = token {
                if !super::tracker::is_separator(&n, node, token) {
                    return end;
                }
                let node_start = astnav::get_start_of_node(&mut n, source_file, node, false);
                let prev_token = astnav::find_preceding_token(&mut n, source_file, node_start);
                if let Some(prev_token) = prev_token {
                    if !super::tracker::is_separator(&n, prev_node.unwrap(), prev_token) {
                        return end;
                    }
                    let prev_start =
                        astnav::get_start_of_node(&mut n, source_file, prev_token, false);
                    let token_start = astnav::get_start_of_node(&mut n, source_file, token, false);
                    (
                        Some(token),
                        Some(prev_token),
                        n[token].end(),
                        prev_start,
                        token_start,
                    )
                } else {
                    (Some(token), None, n[token].end(), 0, 0)
                }
            } else {
                (None, None, 0, 0, 0)
            }
        };
        if token.is_none() || prev_token.is_none() {
            return end;
        }
        let n = nodes.snapshot();
        let text = n[source_file].as_source_file().text().to_string();
        let pos = scanner::skip_trivia_ex(
            &text,
            token_end,
            Some(&scanner::SkipTriviaOptions {
                stop_after_line_break: true,
                stop_at_comments: true,
                ..Default::default()
            }),
        );
        if positions_are_on_same_line(prev_start, token_start, source_file, &n) {
            if pos > 0 && is_line_break_at(&text, pos - 1) {
                return pos - 1;
            }
            return pos;
        }
        if is_line_break_at(&text, pos) {
            return pos;
        }
        end
    }
}
