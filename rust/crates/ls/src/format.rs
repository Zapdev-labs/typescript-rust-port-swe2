// Ported from tsc/internal/ls/format.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::{CommentRange, Node, NodeFactory, NodeFactoryHooks};
use tsc_ast::kind_generated::Kind;
use tsc_ast::{self as ast, NodeId};
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_core::textchange::TextChange;
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto::{self as lsproto};
use tsc_lsutil::formatcodeoptions::from_ls_format_options;
use tsc_lsutil::userpreferences_generated::FormatCodeSettings;
use tsc_spanmap::{Feature, SpanMap};

use crate::api::Error;
use crate::languageservice::LanguageService;
use crate::utilities::{get_leading_comment_ranges_of_node, is_in_comment};

impl<'h> LanguageService<'h> {
    /// `toLSProtoTextEdits`.
    fn to_lsp_text_edits(
        &self,
        nodes: &[Node],
        file: NodeId,
        changes: &[TextChange],
    ) -> Option<Vec<lsproto::TextEdit>> {
        let mut result: Vec<lsproto::TextEdit> = Vec::with_capacity(changes.len());
        for c in changes {
            let script = source_file_script(file, nodes);
            let (lsp_range, fidelity) = self
                .converters
                .to_lsp_range(&script, TextRange::new(c.pos(), c.end()));
            if !fidelity.is_exact() {
                return None;
            }
            result.push(lsproto::TextEdit {
                new_text: c.new_text.clone(),
                range: lsp_range,
            });
        }
        Some(result)
    }

    /// `ProvideFormatDocument`.
    pub fn provide_format_document(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
        options: &lsproto::FormattingOptions,
    ) -> Result<lsproto::DocumentFormattingResponse, Error> {
        if self.user_preferences().format_enabled.is_false() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let (program, file) = self.get_program_and_file(&document_uri);
        let format_opts = from_ls_format_options(self.format_options(), options);
        let edits = {
            let mut nodes = program.nodes_mut(file.file_index());
            if nodes[file].as_source_file().content_mapper().is_empty() {
                let changes = self.get_formatting_edits_for_document(
                    ctx,
                    &mut nodes,
                    file,
                    format_opts,
                );
                self.to_lsp_text_edits(&nodes, file, &changes)
                    .unwrap_or_default()
            } else {
                let original_range = TextRange::new(
                    0,
                    nodes[file].as_source_file().original_text().len() as i32,
                );
                self.get_formatting_edits_for_mapped_range(
                    ctx,
                    &mut nodes,
                    &program,
                    file,
                    format_opts,
                    original_range,
                )
            }
        };
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    /// `getFormattingEditsForMappedRange` formats each formatting-enabled verbatim intersection with originalRange.
    /// Duplicate formatting projections are unsupported. If mappings overlap anyway, each original-text position
    /// is formatted only once, preferring the earliest and then longest applicable mapping.
    fn get_formatting_edits_for_mapped_range(
        &self,
        ctx: &Context,
        nodes: &mut Vec<Node>,
        program: &std::rc::Rc<tsc_compiler::program::Program>,
        file: NodeId,
        options: FormatCodeSettings,
        original_range: TextRange,
    ) -> Vec<lsproto::TextEdit> {
        let mut projections: Vec<NodeId> = vec![file];
        projections.extend_from_slice(
            nodes[file].as_source_file().supplemental_source_files(),
        );
        let mut candidates: Vec<MappedFormattingRange> = Vec::new();
        for projection in projections {
            // PORT: supplemental projections may live in a different AST arena;
            // resolve each through its own `file_index` (`NodeId`s are
            // process-global, not arena-relative).
            let span_map = if projection.file_index() == file.file_index() {
                nodes[projection].as_source_file().span_map()
            } else {
                let projection_nodes = program.nodes(projection.file_index());
                projection_nodes[projection].as_source_file().span_map()
            };
            let Some(span_map) = span_map else {
                continue;
            };
            for segment in SpanMap::segments(Some(&span_map)) {
                if segment.kind != tsc_spanmap::Kind::Verbatim
                    || (segment.features & Feature::Formatting).0 == 0
                {
                    continue;
                }
                let original_start = original_range.pos().max(segment.original_start);
                let original_end = original_range.end().min(segment.original_end);
                if original_start >= original_end {
                    continue;
                }
                candidates.push(MappedFormattingRange {
                    projection,
                    segment,
                    original_range: TextRange::new(original_start, original_end),
                });
            }
        }

        let mut edits: Vec<lsproto::TextEdit> = Vec::new();
        for candidate in non_overlapping_formatting_ranges(candidates) {
            let virtual_range = TextRange::new(
                candidate.segment.virtual_start + candidate.original_range.pos()
                    - candidate.segment.original_start,
                candidate.segment.virtual_start + candidate.original_range.end()
                    - candidate.segment.original_start,
            );
            // The candidate may live in a supplemental (different-arena) file.
            let changes = {
                let mut projection_nodes =
                    program.nodes_mut(candidate.projection.file_index());
                self.get_formatting_edits_for_range(
                    ctx,
                    &mut projection_nodes,
                    candidate.projection,
                    options.clone(),
                    virtual_range,
                )
            };
            for change in changes {
                if change.pos() < virtual_range.pos() || change.end() > virtual_range.end() {
                    continue;
                }
                let (lsp_range, fidelity) = {
                    let projection_nodes =
                        program.nodes(candidate.projection.file_index());
                    let script = source_file_script(candidate.projection, &projection_nodes);
                    self.converters.to_lsp_range_for_feature(
                        &script,
                        TextRange::new(change.pos(), change.end()),
                        Feature::Formatting,
                    )
                };
                if !fidelity.is_exact() {
                    continue;
                }
                edits.push(lsproto::TextEdit {
                    range: lsp_range,
                    new_text: change.new_text,
                });
            }
        }
        edits.sort_by(|a, b| {
            let c = lsproto::compare_ranges(&a.range, &b.range);
            if c != 0 {
                return c.cmp(&0);
            }
            a.new_text.cmp(&b.new_text)
        });
        edits
    }

    /// `ProvideFormatDocumentRange`.
    pub fn provide_format_document_range(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
        options: &lsproto::FormattingOptions,
        r: lsproto::Range,
    ) -> Result<lsproto::DocumentRangeFormattingResponse, Error> {
        if self.user_preferences().format_enabled.is_false() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let (program, file) = self.get_program_and_file(&document_uri);
        let format_opts = from_ls_format_options(self.format_options(), options);
        let mut nodes = program.nodes_mut(file.file_index());
        if !nodes[file].as_source_file().content_mapper().is_empty() {
            let script = source_file_script(file, &nodes);
            let original_range = self.converters.from_lsp_range_to_original(&script, r);
            let edits = self.get_formatting_edits_for_mapped_range(
                ctx,
                &mut nodes,
                &program,
                file,
                format_opts,
                original_range,
            );
            return Ok(lsproto::TextEditsOrNull {
                text_edits: Some(edits),
            });
        }
        let ranges = self.converters.from_lsp_range_for_source_file(
            file,
            &nodes,
            r,
            Feature::Formatting,
        );
        if ranges.len() != 1 || !ranges[0].fidelity.is_exact() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let file = ranges[0].script.file;
        let span = ranges[0].span;
        // The mapped projection may be a supplemental file in a different arena.
        let changes = {
            drop(ranges);
            drop(nodes);
            let mut nodes = program.nodes_mut(file.file_index());
            self.get_formatting_edits_for_range(
                ctx,
                &mut nodes,
                file,
                format_opts,
                span,
            )
        };
        let nodes = program.nodes(file.file_index());
        let edits = self
            .to_lsp_text_edits(&nodes, file, &changes)
            .unwrap_or_default();
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    /// `ProvideFormatDocumentOnType`.
    pub fn provide_format_document_on_type(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
        options: &lsproto::FormattingOptions,
        position: lsproto::Position,
        character: &str,
    ) -> Result<lsproto::DocumentOnTypeFormattingResponse, Error> {
        if self.user_preferences().format_enabled.is_false() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let (program, file) = self.get_program_and_file(&document_uri);
        let format_opts = from_ls_format_options(self.format_options(), options);
        let nodes = program.nodes_mut(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            position,
            Feature::Formatting,
        );
        if positions.len() != 1 || !positions[0].fidelity.is_exact() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let file = positions[0].script.file;
        let position = positions[0].position;
        // The mapped projection may be a supplemental file in a different arena.
        let changes = {
            drop(positions);
            drop(nodes);
            let mut nodes = program.nodes_mut(file.file_index());
            self.get_formatting_edits_after_keystroke(
                ctx,
                &mut nodes,
                file,
                format_opts,
                position,
                character,
            )
        };
        let nodes = program.nodes(file.file_index());
        let edits = self
            .to_lsp_text_edits(&nodes, file, &changes)
            .unwrap_or_default();
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    /// `getFormattingEditsForRange`.
    fn get_formatting_edits_for_range(
        &self,
        ctx: &Context,
        nodes: &mut Vec<Node>,
        file: NodeId,
        options: FormatCodeSettings,
        r: TextRange,
    ) -> Vec<TextChange> {
        let ctx =
            tsc_format::with_format_code_settings(
                ctx,
                options.clone(),
                &options.editor_settings.new_line_character,
            );
        tsc_format::format_selection(&ctx, file, r.pos(), r.end(), nodes)
    }

    /// `getFormattingEditsForDocument`.
    fn get_formatting_edits_for_document(
        &self,
        ctx: &Context,
        nodes: &mut Vec<Node>,
        file: NodeId,
        options: FormatCodeSettings,
    ) -> Vec<TextChange> {
        let ctx =
            tsc_format::with_format_code_settings(
                ctx,
                options.clone(),
                &options.editor_settings.new_line_character,
            );
        tsc_format::format_document(&ctx, file, nodes)
    }

    /// `getFormattingEditsAfterKeystroke`.
    fn get_formatting_edits_after_keystroke(
        &self,
        ctx: &Context,
        nodes: &mut Vec<Node>,
        file: NodeId,
        options: FormatCodeSettings,
        position: i32,
        key: &str,
    ) -> Vec<TextChange> {
        let ctx =
            tsc_format::with_format_code_settings(
                ctx,
                options.clone(),
                &options.editor_settings.new_line_character,
            );

        let token_at_position =
            tsc_astnav::tokens::get_token_at_position(nodes, file, position);
        if is_in_comment(nodes, file, position, token_at_position).is_none() {
            match key {
                "{" => return tsc_format::format_on_opening_curly(&ctx, file, position, nodes),
                "}" => return tsc_format::format_on_closing_curly(&ctx, file, position, nodes),
                ";" => return tsc_format::format_on_semicolon(&ctx, file, position, nodes),
                "\n" => return tsc_format::format_on_enter(&ctx, file, position, nodes),
                _ => return Vec::new(),
            }
        }
        Vec::new()
    }
}

/// `mappedFormattingRange`.
struct MappedFormattingRange {
    projection: NodeId,
    segment: tsc_spanmap::Segment,
    original_range: TextRange,
}

/// `nonOverlappingFormattingRanges` chooses at most one formatting projection for each original-text position.
/// Candidates are ordered by original start and then descending end, so a longer mapping wins when several
/// mappings start together:
///
/// ```text
/// candidates:  [---------- A ----------)
///              [---- B ----)
/// result:      [---------- A ----------)
/// ```
///
/// Since starts are ordered, a candidate can only overlap the end of the last accepted range. Its start is
/// trimmed to that end, preserving any uncovered suffix:
///
/// ```text
/// candidates:  [------- A -------)
///                  [------- B ----------)
/// result:      [------- A -------)[-- B' --)
/// ```
///
/// Fully covered candidates have no suffix and are discarded. The segment itself is retained so callers can
/// translate a trimmed original range to the corresponding offset in its virtual projection.
fn non_overlapping_formatting_ranges(
    mut candidates: Vec<MappedFormattingRange>,
) -> Vec<MappedFormattingRange> {
    candidates.sort_by(|a, b| {
        let c = a.original_range.pos().cmp(&b.original_range.pos());
        if c != std::cmp::Ordering::Equal {
            return c;
        }
        b.original_range.end().cmp(&a.original_range.end())
    });

    let mut result: Vec<MappedFormattingRange> = Vec::with_capacity(candidates.len());
    for mut candidate in candidates {
        if let Some(last) = result.last() {
            candidate.original_range = candidate.original_range.with_pos(
                candidate.original_range.pos().max(last.original_range.end()),
            );
        }
        if candidate.original_range.len() > 0 {
            result.push(candidate);
        }
    }
    result
}

/// `getRangeOfEnclosingComment` — unlike the TS implementation, this function *will not* compute
/// default values for `preceding_token` and `token_at_position`.
/// It is the caller's responsibility to call `astnav.GetTokenAtPosition` to compute a default `tokenAtPosition`,
/// or `astnav.FindPrecedingToken` to compute a default `precedingToken`.
pub(crate) fn get_range_of_enclosing_comment(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
    preceding_token: Option<NodeId>,
    token_at_position: Option<NodeId>,
) -> Option<CommentRange> {
    let mut token_at_position = token_at_position;
    let jsdoc = ast::find_ancestor(token_at_position, nodes, &mut |n, _nodes| {
        ast::is_js_doc(n)
    });
    if let Some(jsdoc) = jsdoc {
        token_at_position = nodes[jsdoc].parent;
    }
    let token_at_position = token_at_position?;
    let token_start = tsc_astnav::tokens::get_start_of_node(
        nodes,
        file,
        token_at_position,
        false, /*includeJSDoc*/
    );
    if token_start <= position && position < nodes[token_at_position].end() {
        return None;
    }

    // Between two consecutive tokens, all comments are either trailing on the former
    // or leading on the latter (and none are in both lists).
    let mut comment_ranges: Vec<CommentRange> = Vec::new();
    if let Some(preceding_token) = preceding_token {
        let factory = NodeFactory::<'static>::new(NodeFactoryHooks::default());
        comment_ranges.extend(tsc_scanner::scanner::get_trailing_comment_ranges(
            &factory,
            &nodes[file].as_source_file().text,
            nodes[preceding_token].end(),
        ));
    }
    comment_ranges.extend(get_leading_comment_ranges_of_node(
        nodes,
        token_at_position,
        file,
    ));

    for comment_range in comment_ranges {
        // The end marker of a single-line comment does not include the newline character.
        // In the following case where the cursor is at `^`, we are inside a comment:
        //
        //    // asdf   ^\n
        //
        // But for closed multi-line comments, we don't want to be inside the comment in the following case:
        //
        //    /* asdf */^
        //
        // Internally, we represent the end of the comment prior to the newline and at the '/', respectively.
        //
        // However, unterminated multi-line comments lack a `/`, end at the end of the file, and *do* contain their end.
        if comment_range.text_range.contains_exclusive(position)
            || (position == comment_range.text_range.end()
                && (comment_range.kind == Kind::SingleLineCommentTrivia
                    || position == nodes[file].as_source_file().text.len() as i32))
        {
            return Some(comment_range);
        }
    }
    None
}
