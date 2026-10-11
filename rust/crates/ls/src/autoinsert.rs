// Ported from tsc/internal/ls/autoinsert.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::{self as ast, NodeFlags, NodeId};
use tsc_core::context::Context;
use tsc_lsproto::{self as lsproto};
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::languageservice::LanguageService;

// allow the client to match more than valid tag names. This allows linked editing when typing is in progress or tag name is incomplete
/// `jsxTagWordPattern` — shared with `linkedediting.rs` (which defines the
/// same string for `WordPattern`).
pub(crate) const JSX_TAG_WORD_PATTERN: &str = "[a-zA-Z0-9:\\-\\._$]*";

/// `escapeSnippetText` — PORT(sibling): a private copy; the canonical port
/// lives in sibling-owned `completions.rs`.
fn escape_snippet_text(text: &str) -> String {
    text.replace('$', "\\$")
}

impl<'h> LanguageService<'h> {
    /// `ProvideOnAutoInsert`.
    pub fn provide_on_auto_insert(
        &self,
        _ctx: &Context,
        params: &lsproto::VSOnAutoInsertParams,
    ) -> Result<lsproto::VSOnAutoInsertResponse, Error> {
        if self.user_preferences().auto_closing_tags.is_false() {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        }
        if params.vs_ch != ">" {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        }

        let (program, source_file) = self.get_program_and_file(&params.vs_text_document.uri);
        let (file, position) = {
            let nodes = program.nodes(source_file.file_index());
            let positions = self.converters.from_lsp_position_for_source_file(
                source_file,
                &nodes,
                params.vs_position,
                Feature::AutoInsert,
            );
            if positions.len() != 1 || !positions[0].fidelity.is_exact() {
                return Ok(lsproto::VSOnAutoInsertResponse::default());
            }
            (positions[0].script.file, positions[0].position)
        };

        let token = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::find_preceding_token(&mut nodes, file, position)
        };
        let Some(token) = token else {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        };

        let nodes = program.nodes(file.file_index());
        let mut closing_text = String::new();
        let mut element: Option<NodeId> = None;
        if nodes[token].kind == ast::Kind::GreaterThanToken
            && ast::is_jsx_opening_element(&nodes[nodes[token].parent.expect("token parent")])
        {
            element = nodes[nodes[token].parent.unwrap()].parent;
        } else if ast::is_jsx_text(&nodes[token])
            && ast::is_jsx_element(&nodes[nodes[token].parent.expect("jsxText parent")])
        {
            element = nodes[token].parent;
        }

        if let Some(element) = element
            && is_unclosed_tag(element, &nodes)
        {
            let tag_name_node = nodes[element]
                .as_jsx_element()
                .opening_element
                .and_then(|oe| nodes[oe].tag_name());
            // Slight divergence from Strada - we don't use the verbatim text from the opening tag.
            if let Some(tag_name_node) = tag_name_node {
                closing_text = format!(
                    "</{}>",
                    ast::entity_name_to_string(
                        tag_name_node,
                        &nodes,
                        Some(&mut |nodes, n| {
                            tsc_scanner::utilities::get_text_of_node(n, nodes)
                        }),
                    )
                );
            }
        } else {
            let mut fragment: Option<NodeId> = None;
            if nodes[token].kind == ast::Kind::GreaterThanToken
                && ast::is_jsx_opening_fragment(
                    &nodes[nodes[token].parent.expect("token parent")]
                )
            {
                fragment = nodes[nodes[token].parent.unwrap()].parent;
            } else if ast::is_jsx_text(&nodes[token])
                && ast::is_jsx_fragment(&nodes[nodes[token].parent.expect("jsxText parent")])
            {
                fragment = nodes[token].parent;
            }

            if let Some(fragment) = fragment
                && is_unclosed_fragment(fragment, &nodes)
            {
                closing_text = "</>".to_string();
            }
        }

        if closing_text.is_empty() {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        }

        Ok(lsproto::VSOnAutoInsertResponse {
            vs_on_auto_insert_response_item: Some(lsproto::VSOnAutoInsertResponseItem {
                vs_text_edit_format: lsproto::InsertTextFormat::Snippet,
                vs_text_edit: Some(lsproto::TextEdit {
                    range: lsproto::Range {
                        start: params.vs_position,
                        end: params.vs_position,
                    },
                    // Tag names can contain `$` (valid JSX identifier characters), so
                    // escape the closing text to avoid being interpreted as a snippet
                    // placeholder/variable.
                    new_text: format!("$0{}", escape_snippet_text(&closing_text)),
                }),
            }),
        })
    }
}

/// `isUnclosedTag` — `node` is the `*ast.JsxElement` node id.
fn is_unclosed_tag(node: NodeId, nodes: &[tsc_ast::Node]) -> bool {
    let jsx = nodes[node].as_jsx_element();
    let opening_element = jsx.opening_element;
    let closing_element = jsx.closing_element;
    let (Some(opening_element), Some(closing_element)) = (opening_element, closing_element)
    else {
        // PORT: Go dereferences both unconditionally; a missing element is
        // unreachable in practice. Treat missing tags as unclosed rather
        // than panic.
        return true;
    };
    if !ast::tag_names_are_equivalent(
        nodes[opening_element].tag_name().expect("opening tag name"),
        nodes[closing_element].tag_name().expect("closing tag name"),
        nodes,
    ) {
        return true;
    }

    let Some(parent) = nodes[node].parent else {
        return false;
    };
    if ast::is_jsx_element(&nodes[parent]) {
        let parent_jsx = nodes[parent].as_jsx_element();
        return ast::tag_names_are_equivalent(
            nodes[opening_element].tag_name().expect("opening tag name"),
            nodes[parent_jsx.opening_element.expect("parent opening")]
                .tag_name()
                .expect("parent opening tag name"),
            nodes,
        ) && is_unclosed_tag(parent, nodes);
    }

    false
}

/// `isUnclosedFragment` — `node` is the `*ast.JsxFragment` node id.
fn is_unclosed_fragment(node: NodeId, nodes: &[tsc_ast::Node]) -> bool {
    let closing_fragment = nodes[node].as_jsx_fragment().closing_fragment;
    if closing_fragment.is_some_and(|cf| {
        nodes[cf].flags.intersects(NodeFlags::THIS_NODE_HAS_ERROR)
    }) {
        return true;
    }

    if let Some(parent) = nodes[node].parent
        && ast::is_jsx_fragment(&nodes[parent])
        && is_unclosed_fragment(parent, nodes)
    {
        return true;
    }

    false
}
