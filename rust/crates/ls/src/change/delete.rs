// Ported from tsc/internal/ls/change/delete.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{ArenaCell, Kind, Node, NodeId, self as ast};
use tsc_astnav::tokens as astnav;
use tsc_core::text::{TextPos, TextRange};
use tsc_format as format;
use tsc_scanner::scanner;
use tsc_stringutil as stringutil;

use super::tracker::{LeadingTriviaOption, Tracker, TrailingTriviaOption};

/// `deleteDeclaration` deletes a node with smart handling for different node
/// types. This handles special cases like import specifiers in lists,
/// parameters, etc.
///
/// PORT: Go's `deletedNodesInLists map[*ast.Node]bool` is
/// `FxHashMap<NodeId, bool>`; arena access flows through the tracker's
/// registered `Rc<ArenaCell>` handles (the arena for
/// `source_file.file_index()`), so `t` stays free for `&mut` calls while a
/// borrow is held.
pub(crate) fn delete_declaration(
    t: &mut Tracker<'_, '_>,
    deleted_nodes_in_lists: &mut FxHashMap<NodeId, bool>,
    source_file: NodeId,
    node: NodeId,
) {
    let handle = t.arena_handle(source_file);
    let node_kind = handle.borrow()[node].kind;
    match node_kind {
        Kind::Parameter => {
            let mut n = handle.borrow_mut();
            let old_function = n[node].parent.unwrap_or(NodeId::NONE);
            if n[old_function].kind == Kind::ArrowFunction
                && n[old_function].parameters().map_or(0, |p| p.len()) == 1
                && astnav::find_child_of_kind(
                    &mut n,
                    source_file,
                    old_function,
                    Kind::OpenParenToken,
                )
                .is_none()
            {
                // Lambdas with exactly one parameter are special because,
                // after removal, there must be an empty parameter list (i.e.
                // `()`) and this won't necessarily be the case if the
                // parameter is simply removed (e.g. in `x => 1`).
                drop(n);
                let range = t.get_adjusted_range(
                    &handle,
                    source_file,
                    node,
                    node,
                    LeadingTriviaOption::IncludeAll,
                    TrailingTriviaOption::Include,
                );
                t.replace_text_range_with_text(&handle, source_file, range, "()");
            } else {
                drop(n);
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            }
        }

        Kind::ImportDeclaration | Kind::ImportEqualsDeclaration => {
            let is_first_import = {
                let n = handle.borrow();
                let imports = n[source_file].as_source_file().imports();
                (!imports.is_empty() && n[imports[0]].parent == Some(node))
                    || n[source_file]
                        .as_source_file()
                        .statements
                        .as_ref()
                        .and_then(|l| {
                            l.nodes
                                .iter()
                                .copied()
                                .find(|s| ast::is_any_import_syntax(&n[*s]))
                        })
                        == Some(node)
            };
            // For first import, leave header comment in place, otherwise only
            // delete JSDoc comments
            let mut leading_trivia = LeadingTriviaOption::StartLine;
            if is_first_import {
                leading_trivia = LeadingTriviaOption::Exclude;
            } else if has_jsdoc_nodes(&handle, source_file, node) {
                leading_trivia = LeadingTriviaOption::JSDoc;
            }
            delete_node(
                t,
                source_file,
                node,
                leading_trivia,
                TrailingTriviaOption::Include,
            );
        }

        Kind::BindingElement => {
            let preserve_comma = {
                let n = handle.borrow();
                let pattern = n[node].parent.unwrap_or(NodeId::NONE);
                n[pattern].kind == Kind::ArrayBindingPattern
                    && n[pattern]
                        .as_binding_pattern()
                        .elements
                        .as_ref()
                        .and_then(|e| e.nodes.last().copied())
                        != Some(node)
            };
            if preserve_comma {
                delete_node(
                    t,
                    source_file,
                    node,
                    LeadingTriviaOption::IncludeAll,
                    TrailingTriviaOption::Exclude,
                );
            } else {
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            }
        }

        Kind::VariableDeclaration => {
            delete_variable_declaration(t, deleted_nodes_in_lists, source_file, node)
        }

        Kind::TypeParameter => delete_node_in_list(t, deleted_nodes_in_lists, source_file, node),

        Kind::ImportSpecifier => {
            let named_imports = handle.borrow()[node].parent;
            let single = named_imports.is_some_and(|ni| {
                handle.borrow()[ni]
                    .as_named_imports()
                    .elements
                    .as_ref()
                    .map(|e| e.nodes.len())
                    .unwrap_or(0)
                    == 1
            });
            if single {
                delete_import_binding(t, source_file, named_imports.unwrap());
            } else {
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            }
        }

        Kind::NamespaceImport => delete_import_binding(t, source_file, node),

        Kind::SemicolonToken => delete_node(
            t,
            source_file,
            node,
            LeadingTriviaOption::IncludeAll,
            TrailingTriviaOption::Exclude,
        ),

        Kind::TypeKeyword => {
            // For type keyword in import clauses, we need to delete the
            // keyword and any trailing space. The trailing space is part of
            // the next token's leading trivia, so we include it.
            delete_node(
                t,
                source_file,
                node,
                LeadingTriviaOption::Exclude,
                TrailingTriviaOption::Include,
            )
        }

        Kind::FunctionKeyword => delete_node(
            t,
            source_file,
            node,
            LeadingTriviaOption::Exclude,
            TrailingTriviaOption::Include,
        ),

        Kind::ClassDeclaration | Kind::FunctionDeclaration => {
            let mut leading_trivia = LeadingTriviaOption::StartLine;
            if has_jsdoc_nodes(&handle, source_file, node) {
                leading_trivia = LeadingTriviaOption::JSDoc;
            }
            delete_node(
                t,
                source_file,
                node,
                leading_trivia,
                TrailingTriviaOption::Include,
            );
        }

        _ => {
            let parent = handle.borrow()[node].parent;
            if parent.is_none() {
                // a misbehaving client can reach here with the SourceFile node
                delete_node(
                    t,
                    source_file,
                    node,
                    LeadingTriviaOption::IncludeAll,
                    TrailingTriviaOption::Include,
                );
            } else {
                let parent = parent.unwrap();
                let (parent_kind, clause_name, is_call_arg) = {
                    let n = handle.borrow();
                    (
                        n[parent].kind,
                        if n[parent].kind == Kind::ImportClause {
                            n[parent].as_import_clause().name
                        } else {
                            None
                        },
                        n[parent].kind == Kind::CallExpression
                            && n[parent]
                                .as_call_expression()
                                .arguments
                                .as_ref()
                                .is_some_and(|a| a.nodes.contains(&node)),
                    )
                };
                if parent_kind == Kind::ImportClause && clause_name == Some(node) {
                    delete_default_import(t, source_file, parent);
                } else if is_call_arg {
                    delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
                } else {
                    delete_node(
                        t,
                        source_file,
                        node,
                        LeadingTriviaOption::IncludeAll,
                        TrailingTriviaOption::Include,
                    );
                }
            }
        }
    }
}

/// `deleteDefaultImport`.
fn delete_default_import(t: &mut Tracker<'_, '_>, source_file: NodeId, import_clause: NodeId) {
    let handle = t.arena_handle(source_file);
    let (named_bindings, clause_name, clause_parent) = {
        let n = handle.borrow();
        let clause = n[import_clause].as_import_clause();
        (clause.named_bindings, clause.name, n[import_clause].parent)
    };
    if named_bindings.is_none() {
        // Delete the whole import
        delete_node(
            t,
            source_file,
            clause_parent.unwrap(),
            LeadingTriviaOption::IncludeAll,
            TrailingTriviaOption::Include,
        );
    } else {
        // import |d,| * as ns from './file'
        let name = clause_name.unwrap();
        let (start, next_token) = {
            let mut n = handle.borrow_mut();
            let start = astnav::get_start_of_node(&mut n, source_file, name, false);
            let name_end = n[name].end();
            let next = astnav::get_token_at_position(&mut n, source_file, name_end);
            (start, next)
        };
        if next_token.is_some_and(|nt| handle.borrow()[nt].kind == Kind::CommaToken) {
            let next_token = next_token.unwrap();
            // shift first non-whitespace position after comma to the start
            // position of the node
            let end = {
                let n = handle.borrow();
                scanner::skip_trivia_ex(
                    n[source_file].as_source_file().text(),
                    n[next_token].end(),
                    Some(&scanner::SkipTriviaOptions {
                        stop_after_line_break: false,
                        stop_at_comments: true,
                        ..Default::default()
                    }),
                )
            };
            t.replace_text_range_with_text(&handle, source_file, TextRange::new(start, end), "");
        } else {
            delete_node(
                t,
                source_file,
                name,
                LeadingTriviaOption::IncludeAll,
                TrailingTriviaOption::Include,
            );
        }
    }
}

/// `deleteImportBinding`.
fn delete_import_binding(t: &mut Tracker<'_, '_>, source_file: NodeId, node: NodeId) {
    let handle = t.arena_handle(source_file);
    let (clause_name, node_end, node_pos) = {
        let n = handle.borrow();
        let clause = n[n[node].parent.unwrap()].as_import_clause();
        (clause.name, n[node].end(), n[node].pos())
    };
    if clause_name.is_some() {
        // Delete named imports while preserving the default import
        // import d|, * as ns| from './file'
        // import d|, { a }| from './file'
        let (previous_token, start) = {
            let mut n = handle.borrow_mut();
            let previous_token = astnav::get_token_at_position(&mut n, source_file, node_pos - 1);
            debug_assert!(previous_token.is_some(), "previousToken should not be nil");
            let previous_token = previous_token.unwrap();
            let start = astnav::get_start_of_node(&mut n, source_file, previous_token, false);
            (previous_token, start)
        };
        let _ = previous_token;
        t.replace_text_range_with_text(&handle, source_file, TextRange::new(start, node_end), "");
    } else {
        // Delete the entire import declaration
        // |import * as ns from './file'|
        // |import { a } from './file'|
        let import_decl = {
            let n = handle.borrow();
            ast::find_ancestor_kind(Some(node), Kind::ImportDeclaration, &n)
        };
        debug_assert!(import_decl.is_some(), "importDecl should not be nil");
        delete_node(
            t,
            source_file,
            import_decl.unwrap(),
            LeadingTriviaOption::IncludeAll,
            TrailingTriviaOption::Include,
        );
    }
}

/// `deleteVariableDeclaration`.
fn delete_variable_declaration(
    t: &mut Tracker<'_, '_>,
    deleted_nodes_in_lists: &mut FxHashMap<NodeId, bool>,
    source_file: NodeId,
    node: NodeId,
) {
    let handle = t.arena_handle(source_file);
    let (parent, gp) = {
        let n = handle.borrow();
        let parent = n[node].parent.unwrap();
        (parent, n[parent].parent)
    };

    if handle.borrow()[parent].kind == Kind::CatchClause {
        // TODO: There's currently no unused diagnostic for this, could be a
        // suggestion
        let (open_paren, close_paren) = {
            let mut n = handle.borrow_mut();
            (
                astnav::find_child_of_kind(&mut n, source_file, parent, Kind::OpenParenToken),
                astnav::find_child_of_kind(&mut n, source_file, parent, Kind::CloseParenToken),
            )
        };
        debug_assert!(
            open_paren.is_some() && close_paren.is_some(),
            "catch clause should have parens"
        );
        t.delete_node_range(
            &handle,
            source_file,
            open_paren.unwrap(),
            close_paren.unwrap(),
            LeadingTriviaOption::IncludeAll,
            TrailingTriviaOption::Include,
        );
        return;
    }

    let decl_count = handle.borrow()[parent]
        .as_variable_declaration_list()
        .declarations
        .as_ref()
        .map(|d| d.nodes.len())
        .unwrap_or(0);
    if decl_count != 1 {
        delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
        return;
    }

    let gp = gp.unwrap();
    let gp_kind = handle.borrow()[gp].kind;
    match gp_kind {
        Kind::ForOfStatement | Kind::ForInStatement => {
            let obj = {
                let empty = t.node_factory(source_file).new_node_list(Vec::new());
                let mut n = handle.borrow_mut();
                t.node_factory(source_file).new_object_literal_expression(
                    &mut n,
                    Some(empty),
                    false,
                )
            };
            t.replace_node(&handle, source_file, node, obj, None);
        }
        Kind::ForStatement => delete_node(
            t,
            source_file,
            parent,
            LeadingTriviaOption::IncludeAll,
            TrailingTriviaOption::Include,
        ),
        Kind::VariableStatement => {
            let mut leading_trivia = LeadingTriviaOption::StartLine;
            if has_jsdoc_nodes(&handle, source_file, gp) {
                leading_trivia = LeadingTriviaOption::JSDoc;
            }
            delete_node(
                t,
                source_file,
                gp,
                leading_trivia,
                TrailingTriviaOption::Include,
            );
        }
        kind => panic!("Unexpected grandparent kind: {}", kind.kind_string()),
    }
}

/// `deleteNode` deletes a node with the specified trivia options.
/// Warning: This deletes comments too.
fn delete_node(
    t: &mut Tracker<'_, '_>,
    source_file: NodeId,
    node: NodeId,
    leading_trivia: LeadingTriviaOption,
    trailing_trivia: TrailingTriviaOption,
) {
    let handle = t.arena_handle(source_file);
    let start_position =
        t.get_adjusted_start_position(&handle, source_file, node, leading_trivia, false);
    let end_position = t.get_adjusted_end_position(&handle, source_file, node, trailing_trivia);
    t.replace_text_range_with_text(
        &handle,
        source_file,
        TextRange::new(start_position, end_position),
        "",
    );
}

/// `deleteNodeInList`.
fn delete_node_in_list(
    t: &mut Tracker<'_, '_>,
    deleted_nodes_in_lists: &mut FxHashMap<NodeId, bool>,
    source_file: NodeId,
    node: NodeId,
) {
    let handle = t.arena_handle(source_file);
    let containing_list = {
        let mut n = handle.borrow_mut();
        format::get_containing_list(node, source_file, &mut n)
    };
    debug_assert!(
        containing_list.is_some(),
        "containingList should not be nil"
    );
    let containing_list = containing_list.unwrap();
    let index = containing_list.nodes.iter().position(|&x| x == node);
    debug_assert!(index.is_some(), "node should be in containing list");
    let index = index.unwrap();

    if containing_list.nodes.len() == 1 {
        delete_node(
            t,
            source_file,
            node,
            LeadingTriviaOption::IncludeAll,
            TrailingTriviaOption::Include,
        );
        return;
    }

    // Note: We will only delete a comma *after* a node. This will leave a
    // trailing comma if we delete the last node. That's handled in the end by
    // finishTrailingCommaAfterDeletingNodesInList.
    debug_assert!(
        !deleted_nodes_in_lists.get(&node).copied().unwrap_or(false),
        "Deleting a node twice"
    );
    deleted_nodes_in_lists.insert(node, true);

    let start_pos = t.start_position_to_delete_node_in_list(&handle, source_file, node);
    let end_pos = if index == containing_list.nodes.len() - 1 {
        t.get_adjusted_end_position(&handle, source_file, node, TrailingTriviaOption::None)
    } else {
        let prev_node = if index > 0 {
            Some(containing_list.nodes[index - 1])
        } else {
            None
        };
        t.end_position_to_delete_node_in_list(
            &handle,
            source_file,
            node,
            prev_node,
            containing_list.nodes[index + 1],
        )
    };

    t.replace_text_range_with_text(&handle, source_file, TextRange::new(start_pos, end_pos), "");
}

/// `hasJSDocNodes` checks if a node has JSDoc comments.
fn has_jsdoc_nodes(
    handle: &Rc<ArenaCell>,
    source_file: NodeId,
    node: NodeId,
) -> bool {
    let mut n = handle.borrow_mut();
    // nil is ok for JSDoc - it will return empty slice if not available
    !ast::js_doc(&mut n, node, Some(source_file)).is_empty()
}

/// `isLineBreakByte` — `stringutil.IsLineBreak(rune(text[pos]))` with bounds.
fn is_line_break_byte(text: &str, pos: TextPos) -> bool {
    pos >= 0
        && (pos as usize) < text.len()
        && stringutil::is_line_break(text.as_bytes()[pos as usize] as char)
}
