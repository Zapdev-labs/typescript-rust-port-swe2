// Ported from tsc/internal/ls/linkedediting.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::{self as ast, NodeFlags};
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto::{self as lsproto};
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::autoinsert::JSX_TAG_WORD_PATTERN;
use crate::languageservice::LanguageService;

impl<'h> LanguageService<'h> {
    /// `ProvideLinkedEditingRange`.
    pub fn provide_linked_editing_range(
        &self,
        _ctx: &Context,
        params: &lsproto::LinkedEditingRangeParams,
    ) -> Result<lsproto::LinkedEditingRangeResponse, Error> {
        let (program, source_file) = self.get_program_and_file(&params.text_document.uri);
        let (file, position) = {
            let nodes = program.nodes(source_file.file_index());
            let positions = self.converters.from_lsp_position_for_source_file(
                source_file,
                &nodes,
                params.position,
                Feature::LinkedEditing,
            );
            if positions.len() != 1 || !positions[0].fidelity.is_exact() {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }
            (positions[0].script.file, positions[0].position)
        };

        let token = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::find_preceding_token(&mut nodes, file, position)
        };
        let Some(token) = token else {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        };

        let nodes = program.nodes(file.file_index());
        if nodes[token]
            .parent
            .is_none_or(|p| nodes[p].kind == ast::Kind::SourceFile)
        {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        }

        let grandparent = nodes[token].parent.and_then(|p| nodes[p].parent);
        if grandparent.is_some_and(|gp| ast::is_jsx_fragment(&nodes[gp])) {
            let fragment = nodes[grandparent.unwrap()].as_jsx_fragment();
            let open_fragment = fragment.opening_fragment;
            let close_fragment = fragment.closing_fragment;
            if open_fragment.is_some_and(|f| {
                nodes[f]
                    .flags
                    .intersects(NodeFlags::THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR)
            }) || close_fragment.is_some_and(|f| {
                nodes[f]
                    .flags
                    .intersects(NodeFlags::THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR)
            }) {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }
            drop(nodes);

            let (open_pos, close_pos) = {
                let mut nodes = program.nodes_mut(file.file_index());
                (
                    tsc_astnav::tokens::get_start_of_node(
                        &mut nodes,
                        file,
                        open_fragment.expect("openFragment"),
                        false, /*includeJSDoc*/
                    ) + "<".len() as i32,
                    tsc_astnav::tokens::get_start_of_node(
                        &mut nodes,
                        file,
                        close_fragment.expect("closeFragment"),
                        false, /*includeJSDoc*/
                    ) + "</".len() as i32,
                )
            };

            // only allows linked editing right after opening bracket: [cursor] [closing bracket][cursor]
            if position != open_pos && position != close_pos {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }

            let nodes = program.nodes(file.file_index());
            let script = source_file_script(file, &nodes);
            let (open_line_char, open_fidelity) = self.converters.to_lsp_position_for_feature(
                &script,
                open_pos,
                Feature::LinkedEditing,
            );
            let (close_line_char, close_fidelity) = self.converters.to_lsp_position_for_feature(
                &script,
                close_pos,
                Feature::LinkedEditing,
            );
            if !open_fidelity.is_exact() || !close_fidelity.is_exact() {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }
            return Ok(lsproto::LinkedEditingRangeResponse {
                linked_editing_ranges: Some(lsproto::LinkedEditingRanges {
                    ranges: Some(vec![
                        // only return start position for opening tag since the length of a fragment is always 3 and it is unlikely user will type in the middle of a fragment tag
                        lsproto::Range {
                            start: open_line_char,
                            end: open_line_char,
                        },
                        lsproto::Range {
                            start: close_line_char,
                            end: close_line_char,
                        },
                    ]),
                    word_pattern: Some(JSX_TAG_WORD_PATTERN.to_string()),
                }),
            });
        }

        // determines if the cursor is in an element tag
        let tag = ast::find_ancestor(nodes[token].parent, &nodes, &mut |n, _nodes| {
            ast::is_jsx_opening_element(n) || ast::is_jsx_closing_element(n)
        });
        let Some(tag) = tag else {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        };
        debug_assert!(
            ast::is_jsx_opening_element(&nodes[tag]) || ast::is_jsx_closing_element(&nodes[tag]),
            "tag should be opening or closing element"
        );

        let jsx_element = nodes[nodes[tag].parent.expect("tag parent")].as_jsx_element();
        let open_tag = jsx_element.opening_element.expect("openingElement");
        let close_tag = jsx_element.closing_element.expect("closingElement");
        let open_tag_name = nodes[open_tag].tag_name().expect("open tag name");
        let close_tag_name = nodes[close_tag].tag_name().expect("close tag name");
        drop(nodes);

        let (open_tag_name_start, close_tag_name_start, open_tag_start, close_tag_start) = {
            let mut nodes = program.nodes_mut(file.file_index());
            (
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes,
                    file,
                    open_tag_name,
                    false, /*includeJSDoc*/
                ),
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes,
                    file,
                    close_tag_name,
                    false, /*includeJSDoc*/
                ),
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes,
                    file,
                    open_tag,
                    false, /*includeJSDoc*/
                ),
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes,
                    file,
                    close_tag,
                    false, /*includeJSDoc*/
                ),
            )
        };

        let nodes = program.nodes(file.file_index());
        let open_tag_name_end = nodes[open_tag_name].end();
        let close_tag_name_end = nodes[close_tag_name].end();
        // do not return linked cursors if tags are not well-formed
        if open_tag_name_start == open_tag_start
            || close_tag_name_start == close_tag_start
            || open_tag_name_end == nodes[open_tag].end()
            || close_tag_name_end == nodes[close_tag].end()
        {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        }
        // only return linked cursors if the cursor is within a tag name
        if !(open_tag_name_start <= position && position <= open_tag_name_end
            || close_tag_name_start <= position && position <= close_tag_name_end)
        {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        }

        // only return linked cursors if text in both tags is identical
        let opening_tag_text =
            tsc_scanner::utilities::get_text_of_node(open_tag_name, &nodes);
        if opening_tag_text != tsc_scanner::utilities::get_text_of_node(close_tag_name, &nodes) {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        }

        let script = source_file_script(file, &nodes);
        let (open_range, open_fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(open_tag_name_start, open_tag_name_end),
            Feature::LinkedEditing,
        );
        let (close_range, close_fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(close_tag_name_start, close_tag_name_end),
            Feature::LinkedEditing,
        );
        if !open_fidelity.is_exact() || !close_fidelity.is_exact() {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        }

        Ok(lsproto::LinkedEditingRangeResponse {
            linked_editing_ranges: Some(lsproto::LinkedEditingRanges {
                ranges: Some(vec![open_range, close_range]),
                word_pattern: Some(JSX_TAG_WORD_PATTERN.to_string()),
            }),
        })
    }
}