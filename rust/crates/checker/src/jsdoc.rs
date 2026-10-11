// Ported from tsc/internal/checker/jsdoc.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// JSDoc checking helpers.
//
// PORT notes:
// - `*ast.Node` → `NodeId` plus an explicit `nodes: &mut Vec<ast::Node>`
//   arena parameter (the node arena lives outside `Checker`, so `&mut self`
//   and `&mut Vec<Node>` cannot be one borrow).
// - `getAllJSDocTags` is a faithful free-function port.
// - `checkUnmatchedJSDocParameters` is fully ported but routes through the
//   `PORT(deferred)` checker stubs (`contains_arguments_reference`, `error`,
//   `error_or_suggestion`, `is_array_type`, `get_type_from_type_node`) — it
//   is reachable only once those land with checker.go. Call sites (also
//   deferred) use `c.check_unmatched_js_doc_parameters(nodes, node)`.

use tsc_ast::{self as ast, NodeId};
use tsc_collections::Set;
use tsc_diagnostics as diagnostics;

use crate::checker_core::Checker;

impl Checker {
    /// `(c *Checker) checkUnmatchedJSDocParameters`. PORT(deferred):
    /// depends on deferred checker diagnostics/type methods (see header).
    pub fn check_unmatched_js_doc_parameters(&mut self, nodes: &mut Vec<ast::Node>, node: NodeId) {
        let mut jsdoc_parameters: Vec<NodeId> = Vec::new();
        for tag in get_all_jsdoc_tags(nodes, node) {
            if nodes[tag].kind == ast::Kind::JSDocParameterTag {
                let name = nodes[tag].as_js_doc_parameter_or_property_tag().name;
                if let Some(name) = name {
                    // `ast.IsIdentifier(name) && len(name.Text()) == 0`.
                    if ast::is_identifier(&nodes[name]) && nodes[name].text(nodes).is_empty() {
                        continue;
                    }
                }
                jsdoc_parameters.push(tag);
            }
        }

        if jsdoc_parameters.is_empty() {
            return;
        }

        let is_js = ast::is_in_js_file(Some(node), nodes);
        let mut parameters: Set<String> = Set::new();
        let mut excluded_parameters: Set<usize> = Set::new();

        for (i, param) in nodes[node]
            .parameters()
            .unwrap_or(&[])
            .to_vec()
            .iter()
            .enumerate()
        {
            let param = *param;
            let name = nodes[param].as_parameter_declaration().name;
            if let Some(name) = name {
                if ast::is_identifier(&nodes[name]) {
                    parameters.add(nodes[name].text(nodes).into_owned());
                }
                if ast::is_binding_pattern(&nodes[name]) {
                    excluded_parameters.add(i);
                }
            }
        }
        if self.contains_arguments_reference(node) {
            if is_js {
                let last_jsdoc_param_index = jsdoc_parameters.len() - 1;
                let last_jsdoc_param_tag = jsdoc_parameters[last_jsdoc_param_index];
                let last_jsdoc_param =
                    nodes[last_jsdoc_param_tag].as_js_doc_parameter_or_property_tag();
                let Some(last_jsdoc_param_name) = last_jsdoc_param.name else {
                    return;
                };
                if !ast::is_identifier(&nodes[last_jsdoc_param_name]) {
                    return;
                }
                if excluded_parameters.has(&last_jsdoc_param_index)
                    || parameters.has(nodes[last_jsdoc_param_name].text(nodes).as_ref())
                {
                    return;
                }
                let Some(type_expression) = last_jsdoc_param.type_expression else {
                    return;
                };
                let Some(type_node) = nodes[type_expression].as_js_doc_type_expression().type_
                else {
                    return;
                };
                let t = self.get_type_from_type_node(type_node);
                if self.is_array_type(t) {
                    return;
                }
                // PORT(borrowck): resolve diagnostics against `nodes` — the
                // caller's arena may be a scratch clone whose lazily-parsed
                // JSDoc ids don't exist in the program arena.
                let d = crate::utilities::new_diagnostic_for_node(
                    Some(last_jsdoc_param_name),
                    nodes,
                    &diagnostics::JSDoc_param_tag_has_name_0_but_there_is_no_parameter_with_that_name_It_would_match_arguments_if_it_had_an_array_type,
                    &[nodes[last_jsdoc_param_name].text(nodes).into_owned()],
                );
                self.add_diagnostic(&d);
            }
        } else {
            for (index, tag) in jsdoc_parameters.iter().enumerate() {
                let tag = *tag;
                let data = nodes[tag].as_js_doc_parameter_or_property_tag();
                let name = data.name;
                let is_name_first = data.is_name_first;

                let name_is_known_parameter = name.is_some_and(|name| {
                    ast::is_identifier(&nodes[name])
                        && parameters.has(nodes[name].text(nodes).as_ref())
                });
                if excluded_parameters.has(&index) || name_is_known_parameter {
                    continue;
                }

                if let Some(name) = name {
                    if ast::is_qualified_name(&nodes[name]) {
                        if is_js {
                            let left = nodes[name].as_qualified_name().left.unwrap();
                            let d = crate::utilities::new_diagnostic_for_node(
                                Some(name),
                                nodes,
                                &diagnostics::Qualified_name_0_is_not_allowed_without_a_leading_param_object_1,
                                &[
                                    ast::entity_name_to_string(name, nodes, None),
                                    ast::entity_name_to_string(left, nodes, None),
                                ],
                            );
                            self.add_diagnostic(&d);
                        }
                    } else if !is_name_first {
                        let d = crate::utilities::new_diagnostic_for_node(
                            Some(name),
                            nodes,
                            &diagnostics::JSDoc_param_tag_has_name_0_but_there_is_no_parameter_with_that_name,
                            &[nodes[name].text(nodes).into_owned()],
                        );
                        self.add_error_or_suggestion(is_js, &d);
                    }
                }
            }
        }
    }
}

/// `getAllJSDocTags` — walks `GetNextJSDocCommentLocation` owners until a
/// node with JSDoc tags is found.
pub fn get_all_jsdoc_tags(nodes: &mut Vec<ast::Node>, node: NodeId) -> Vec<NodeId> {
    // `node.Flags&ast.NodeFlagsJSDoc == 0` — don't look for JSDoc on nodes
    // already inside a JSDoc comment.
    if !nodes[node].flags.intersects(ast::NodeFlags::JSDOC) {
        let mut current = Some(node);
        while let Some(cur) = current {
            let jsdocs = ast::js_doc(nodes, cur, None);
            if jsdocs.is_empty() {
                current = ast::get_next_js_doc_comment_location(cur, nodes);
                continue;
            }
            let last_jsdoc = *jsdocs.last().unwrap();
            if let Some(tags) = &nodes[last_jsdoc].as_js_doc().tags {
                return tags.nodes.to_vec();
            }
            current = ast::get_next_js_doc_comment_location(cur, nodes);
        }
    }
    Vec::new()
}

/// `GetJSDocDeprecatedTag` (tsc/internal/ast/utilities.go:1223) — checker-local
/// copy; the ast-level version is PORT(deferred) (needs `Node::JSDoc`/
/// `file.jsdocCache`), reachable here via `ast::js_doc` with the mutable arena.
pub fn get_jsdoc_deprecated_tag(nodes: &mut Vec<ast::Node>, node: NodeId) -> Option<NodeId> {
    let jsdocs = ast::js_doc(nodes, node, None);
    for jsdoc in jsdocs {
        if let Some(tags) = &nodes[jsdoc].as_js_doc().tags {
            for &tag in &tags.nodes {
                if ast::is_js_doc_deprecated_tag(&nodes[tag]) {
                    return Some(tag);
                }
            }
        }
    }
    None
}

/// `IsDeprecatedDeclarationWithCachedFlags` (tsc/internal/ast/utilities.go:1246)
/// — checker-local copy (see `get_jsdoc_deprecated_tag`).
pub fn is_deprecated_declaration_with_cached_flags(
    nodes: &mut Vec<ast::Node>,
    declaration: NodeId,
    combined_flags: ast::NodeFlags,
) -> bool {
    if !combined_flags.intersects(ast::NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG) {
        return false;
    }
    // Walk up to find the node that directly has the flag, since JSDoc is
    // attached to that node (e.g. VariableStatement, not VariableDeclaration).
    let mut n = Some(declaration);
    while let Some(cur) = n {
        if nodes[cur]
            .flags
            .intersects(ast::NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG)
        {
            return get_jsdoc_deprecated_tag(nodes, cur).is_some();
        }
        n = nodes[cur].parent;
    }
    false
}
