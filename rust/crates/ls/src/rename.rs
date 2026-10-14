// Ported from tsc/internal/ls/rename.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*ast.Node`/`*ast.SourceFile` are `NodeId`s; every node access goes
//   through the node's own arena (`program.nodes(node.file_index())`).
//   `original_node` and `entry.node` may live in different files, so
//   `get_text_for_rename` fetches separate arenas for each.
// - `map[renameEditKey]string` dedup is a linear `Vec` scan (`Range` is not
//   `Hash`); `changes` is a `BTreeMap` like `combine_rename_response`.
// - `RenameInfo.FileToRename`/`NewFileName` are `Option<RootedPath>` for Go's
//   `tspath.RootedPath` "" sentinel.
// - `symbol.Declarations`/`symbol.Parent`/`symbol.Flags` are read through
//   `checker.symbol_arena.get_ref(symbol)`; declaration nodes may
//   live in any file's arena.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use tsc_ast::{self as ast, Kind, Node, NodeId, SymbolFlags, SymbolId};
use tsc_astnav::tokens;
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_core::tristate::TS_TRUE;
use tsc_diagnostics::Message;
use tsc_lsconv::source_file_script;
use tsc_lsproto::{self as lsproto};
use tsc_lsutil::{self as lsutil, QuotePreference};
use tsc_module::node_module_package_root_for_file;
use tsc_spanmap::Feature;
use tsc_tspath::{self as tspath, RootedFilePath, RootedPath};

use crate::api::Error;
use crate::findallreferences::{
    combine_rename_response, CrossProjectOrchestrator, EntryKind, ReferenceEntry,
    SymbolAndEntriesData, SymbolEntryTransformOptions,
};
use crate::languageservice::LanguageService;
use crate::utilities::{
    get_adjusted_location, get_contextual_type_from_parent_or_ancestor_type_node,
    is_literal_name_of_property_declaration_or_index_access,
    is_object_binding_element_without_property_name,
};

/// `type RenameInfo struct` — the result of a rename validation check, used by
/// the `textDocument/prepareRename` LSP handler.
#[derive(Clone, Debug, Default)]
pub struct RenameInfo {
    /// `CanRename`.
    pub can_rename: bool,
    /// `LocalizedErrorMessage`.
    pub localized_error_message: String,
    /// `DisplayName`.
    pub display_name: String,
    /// `TriggerSpan`.
    pub trigger_span: lsproto::Range,
    /// `FileToRename` (`Option` is Go's `tspath.RootedPath` "" sentinel).
    pub file_to_rename: Option<RootedPath>,
    /// `NewFileName`.
    pub new_file_name: Option<RootedPath>,
}

/// `type mappedRenameEdit struct`.
struct MappedRenameEdit {
    uri: lsproto::DocumentUri,
    edit: lsproto::TextEdit,
}

/// `deduplicateRenameEdits`.
fn deduplicate_rename_edits(
    mapped_edits: Vec<MappedRenameEdit>,
) -> Option<BTreeMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>>> {
    // `map[renameEditKey]string` — linear scan (`Range` is not `Hash`).
    let mut edit_texts: Vec<(lsproto::DocumentUri, lsproto::Range, String)> = Vec::new();
    let mut unique_edits: Vec<MappedRenameEdit> = Vec::with_capacity(mapped_edits.len());
    for mapped_edit in mapped_edits {
        let existing = edit_texts.iter().find(|(uri, range, _)| {
            *uri == mapped_edit.uri && *range == mapped_edit.edit.range
        });
        if let Some((_, _, existing_text)) = existing {
            if *existing_text != mapped_edit.edit.new_text {
                return None;
            }
            continue;
        }
        edit_texts.push((
            mapped_edit.uri.clone(),
            mapped_edit.edit.range.clone(),
            mapped_edit.edit.new_text.clone(),
        ));
        unique_edits.push(mapped_edit);
    }
    let mut changes: BTreeMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>> = BTreeMap::new();
    for mapped_edit in unique_edits {
        changes
            .entry(mapped_edit.uri)
            .or_default()
            .push(mapped_edit.edit);
    }
    Some(changes)
}

impl<'h> LanguageService<'h> {
    /// `ProvideRename`.
    pub fn provide_rename(
        &self,
        ctx: &Context,
        params: &lsproto::RenameParams,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<lsproto::RenameResponse, Error> {
        self.handle_cross_project(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            orchestrator,
            |l, ctx, data, options| l.symbol_and_entries_to_rename(ctx, params, data, options),
            &combine_rename_response,
            true,  /*isRename*/
            false, /*implementations*/
            SymbolEntryTransformOptions::default(),
            None, /*defaultProjectData*/
        )
    }

    /// `GetRenameInfo`.
    pub fn get_rename_info(
        &self,
        ctx: &Context,
        new_name: &str,
        document_uri: &lsproto::DocumentUri,
        position: lsproto::Position,
    ) -> RenameInfo {
        let (program, source_file) = self.get_program_and_file(document_uri);
        let nodes = program.nodes(source_file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            source_file,
            &nodes,
            position,
            Feature::Rename,
        );
        for mapped in &positions {
            if !mapped.fidelity.is_exact() {
                continue;
            }
            let source_file = mapped.script.file;
            let node = {
                let mut nodes = program.nodes_mut(source_file.file_index());
                tokens::get_touching_property_name(&mut nodes, source_file, mapped.position)
            };
            let Some(node) = node else {
                continue;
            };
            let node = {
                let mut nodes = program.nodes_mut(source_file.file_index());
                get_adjusted_location(&mut nodes, node, true /*forRename*/, Some(source_file))
                    .unwrap_or(node)
            };
            let nodes = program.nodes(source_file.file_index());
            if node_is_eligible_for_rename(node, &nodes) {
                drop(nodes);
                if let Some(rename_info) = self.get_rename_info_for_node(
                    ctx,
                    new_name,
                    node,
                    source_file,
                    &program,
                ) {
                    return rename_info;
                }
            }
        }
        get_rename_info_error(ctx, &tsc_diagnostics::You_cannot_rename_this_element)
    }

    /// `symbolAndEntriesToRename`.
    fn symbol_and_entries_to_rename(
        &self,
        ctx: &Context,
        params: &lsproto::RenameParams,
        data: SymbolAndEntriesData,
        _options: SymbolEntryTransformOptions,
    ) -> Result<lsproto::WorkspaceEditOrNull, Error> {
        let Some(original_node) = data.original_node else {
            return Ok(lsproto::WorkspaceEditOrNull::default());
        };
        let program = self.get_program();
        {
            let nodes = program.nodes(original_node.file_index());
            if !node_is_eligible_for_rename(original_node, &nodes) {
                return Ok(lsproto::WorkspaceEditOrNull::default());
            }
        }

        // Defense-in-depth: validate rename eligibility even if the client
        // skipped prepareRename. Use `get_rename_info_for_node` directly with
        // the already-resolved node to avoid re-resolving the position and
        // polluting state baselines.
        let source_file = {
            let nodes = program.nodes(original_node.file_index());
            ast::get_source_file_of_node(Some(original_node), &nodes).expect("source file")
        };
        match self.get_rename_info_for_node(
            ctx,
            &params.new_name,
            original_node,
            source_file,
            &program,
        ) {
            Some(info) if info.can_rename => {}
            _ => return Ok(lsproto::WorkspaceEditOrNull::default()),
        }

        let mut entries: Vec<Rc<RefCell<ReferenceEntry>>> = Vec::new();
        for s in &data.symbols_and_entries {
            entries.extend(s.borrow().references.iter().cloned());
        }
        let mut mapped_edits: Vec<MappedRenameEdit> = Vec::new();
        let (checker, done) = program.get_type_checker(ctx.clone());

        let quote_preference = {
            let nodes = program.nodes(source_file.file_index());
            lsutil::get_quote_preference(&nodes, source_file, self.user_preferences())
        };
        let use_aliases_for_rename = self
            .user_preferences()
            .provide_prefix_and_suffix_text_for_rename
            .is_true_or_unknown();

        for entry in &entries {
            let uri = self.get_file_name_of_entry(entry);
            let skip = {
                let e = entry.borrow();
                self.user_preferences().allow_rename_of_import_path != TS_TRUE
                    && e.node.is_some_and(|n| {
                        let nodes = self.program.nodes(n.file_index());
                        ast::is_string_literal_like(&nodes[n])
                            && ast::try_get_import_from_module_specifier(n, &nodes).is_some()
                    })
            };
            if skip {
                continue;
            }
            let (rng, ok) = self.rename_edit_range(entry);
            if !ok {
                // The occurrence lies outside a verbatim span of a
                // content-mapped file, so it cannot be written back to the
                // original text. Skip it and keep renaming the remaining
                // occurrences.
                continue;
            }
            let text_edit = lsproto::TextEdit {
                range: rng,
                new_text: self.get_text_for_rename(
                    original_node,
                    entry,
                    &params.new_name,
                    &checker,
                    quote_preference.clone(),
                    use_aliases_for_rename,
                ),
                ..Default::default()
            };
            mapped_edits.push(MappedRenameEdit { uri, edit: text_edit });
        }
        drop(checker);
        done();

        let Some(changes) = deduplicate_rename_edits(mapped_edits) else {
            return Ok(lsproto::WorkspaceEditOrNull::default());
        };
        Ok(lsproto::WorkspaceEditOrNull {
            workspace_edit: Some(lsproto::WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }),
            ..Default::default()
        })
    }

    /// `renameEditRange` — returns the LSP range at which a rename occurrence
    /// should be edited. For occurrences in content-mapped files it maps the
    /// transformed range strictly, returning `false` when the occurrence is
    /// not fully within a single verbatim span, so the caller can skip an
    /// edit that cannot be applied to the original text.
    fn rename_edit_range(
        &self,
        entry: &Rc<RefCell<ReferenceEntry>>,
    ) -> (lsproto::Range, bool) {
        self.resolve_entry(entry);
        let (node, source_file, text_range) = {
            let e = entry.borrow();
            (e.node, e.source_file, e.text_range)
        };
        let Some(node) = node else {
            let (location, fidelity) = self.source_file_range_to_lsp_location(
                source_file.expect("source file"),
                text_range.expect("text range"),
            );
            return (location.range, fidelity.is_exact());
        };
        let nodes = self.program.nodes(node.file_index());
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        match source_file {
            Some(sf) if nodes[sf].as_source_file().span_map().is_some() => {
                let (lsp_range, fidelity) = self.converters.to_lsp_range(
                    &source_file_script(sf, &nodes),
                    text_range.expect("text range"),
                );
                (lsp_range, fidelity.is_exact())
            }
            _ => (self.get_range_of_entry(entry), true),
        }
    }

    /// `getRenameInfoForNode` — performs detailed validation for a rename
    /// operation on a specific node.
    fn get_rename_info_for_node(
        &self,
        ctx: &Context,
        new_name: &str,
        node: NodeId,
        source_file: NodeId,
        program: &Rc<Program>,
    ) -> Option<RenameInfo> {
        let (checker, done) = program.get_type_checker(ctx.clone());

        let symbol = {
            let mut c = checker.borrow_mut();
            c.get_symbol_at_location_api(node)
        };
        let Some(symbol) = symbol else {
            let nodes = program.nodes(source_file.file_index());
            if ast::is_string_literal_like(&nodes[node]) {
                // Allow renaming of string literal types with contextual
                // string literal types.
                let typ = {
                    let mut c = checker.borrow_mut();
                    get_contextual_type_from_parent_or_ancestor_type_node(node, &mut c)
                };
                if let Some(typ) = typ {
                    let c = checker.borrow();
                    let t = c.types.get(typ);
                    let eligible = t.is_string_literal()
                        || (t.is_union()
                            && t.types()
                                .iter()
                                .all(|&t2| c.types.get(t2).is_string_literal()));
                    if eligible {
                        let display_name = nodes[node].text(&nodes).into_owned();
                        drop(nodes);
                        drop(c);
                        let info =
                            self.get_rename_info_success(node, source_file, display_name);
                        drop(checker);
                        done();
                        return Some(info);
                    }
                }
            } else if ast::is_label_name(node, &nodes) {
                let display_name = nodes[node].text(&nodes).into_owned();
                drop(nodes);
                let info = self.get_rename_info_success(node, source_file, display_name);
                drop(checker);
                done();
                return Some(info);
            }
            drop(nodes);
            drop(checker);
            done();
            return None;
        };

        // Only allow a symbol to be renamed if it actually has at least one
        // declaration.
        if checker.borrow().symbol_arena.get_ref(symbol)
            .declarations
            .is_empty()
        {
            drop(checker);
            done();
            return None;
        }

        if let Some(msg) =
            self.rename_blocked_reason(source_file, node, symbol, &checker, program)
        {
            let info = get_rename_info_error(ctx, msg);
            drop(checker);
            done();
            return Some(info);
        }

        let is_module_specifier = {
            let nodes = program.nodes(source_file.file_index());
            ast::is_string_literal_like(&nodes[node])
                && ast::try_get_import_from_module_specifier(node, &nodes).is_some()
        };
        if is_module_specifier {
            if self
                .user_preferences()
                .allow_rename_of_import_path
                .is_true()
            {
                let info = self.get_rename_info_for_module(
                    ctx,
                    new_name,
                    node,
                    source_file,
                    symbol,
                    &checker,
                );
                drop(checker);
                done();
                return info;
            }
            drop(checker);
            done();
            return None;
        }

        let display_name = checker.borrow_mut().symbol_to_string(symbol);
        let info = self.get_rename_info_success(node, source_file, display_name);
        drop(checker);
        done();
        Some(info)
    }

    /// `renameBlockedReason` — returns a non-`None` diagnostic message if the
    /// rename should be blocked because the symbol is a library definition, a
    /// default keyword, or would cross node_modules boundaries.
    fn rename_blocked_reason(
        &self,
        source_file: NodeId,
        node: NodeId,
        symbol: SymbolId,
        checker: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
    ) -> Option<&'static Message> {
        let declarations = checker.borrow().symbol_arena.get_ref(symbol)
            .declarations
            .clone();
        for declaration in &declarations {
            if is_defined_in_library_file(program, *declaration) {
                return Some(
                    &tsc_diagnostics::You_cannot_rename_elements_that_are_defined_in_the_standard_TypeScript_library,
                );
            }
        }

        // Cannot rename `default` as in `import { default as foo } from
        // "./someModule"`.
        {
            let nodes = program.nodes(source_file.file_index());
            if ast::is_identifier(&nodes[node]) && nodes[node].text(&nodes) == "default" {
                let parent_is_module = checker.borrow().symbol_arena.get_ref(symbol)
                    .parent
                    .is_some_and(|parent| {
                        checker.borrow().symbol_arena.get_ref(parent)
                            .flags
                            .intersects(SymbolFlags::MODULE)
                    });
                if parent_is_module {
                    return Some(&tsc_diagnostics::You_cannot_rename_this_element);
                }
            }
        }

        if let Some(msg) = would_rename_in_other_node_modules(
            source_file,
            symbol,
            checker,
            self.user_preferences(),
            program,
        ) {
            return Some(msg);
        }

        None
    }

    /// `getRenameInfoForModule` — handles rename validation for module
    /// specifiers.
    fn get_rename_info_for_module(
        &self,
        ctx: &Context,
        new_name: &str,
        specifier: NodeId,
        source_file: NodeId,
        module_symbol: SymbolId,
        checker: &Rc<RefCell<Checker>>,
    ) -> Option<RenameInfo> {
        let text = {
            let nodes = self.program.nodes(source_file.file_index());
            nodes[specifier].text(&nodes).into_owned()
        };
        if !tspath::is_external_module_name_relative(&text) {
            return Some(get_rename_info_error(
                ctx,
                &tsc_diagnostics::You_cannot_rename_a_module_via_a_global_import,
            ));
        }
        if !client_supports_document_changes(ctx)
            || !client_supports_rename_resource_operations(ctx)
        {
            return Some(get_rename_info_error(
                ctx,
                &tsc_diagnostics::File_rename_is_not_supported_by_the_editor,
            ));
        }

        let declarations = checker.borrow().symbol_arena.get_ref(module_symbol)
            .declarations
            .clone();
        let module_source_file = declarations.iter().copied().find(|&d| {
            let nodes = self.program.nodes(d.file_index());
            ast::is_source_file(&nodes[d])
        })?;

        let file_name = {
            let nodes = self.program.nodes(module_source_file.file_index());
            nodes[module_source_file].as_source_file().file_name().clone()
        };
        let without_index = if !text.ends_with("/index") && !text.ends_with("/index.js") {
            try_remove_index_file_name(&file_name)
        } else {
            None
        };

        let display_name = without_index.unwrap_or_else(|| file_name.as_path());
        let new_file_name =
            self.get_new_file_name_for_module_rename(&display_name, &text, new_name);

        // Span should only be the last component of the path. + 1 to account
        // for the quote character.
        let index_after_last_slash = text.rfind('/').map(|i| i + 1).unwrap_or(0);
        let start = {
            let mut nodes = self.program.nodes_mut(source_file.file_index());
            tokens::get_start_of_node(&mut nodes, source_file, specifier, false)
        } + 1 + index_after_last_slash as i32;
        let length = text.len() as i32 - index_after_last_slash as i32;

        let nodes = self.program.nodes(source_file.file_index());
        let (trigger_span, fidelity) = self.converters.to_lsp_range(
            &source_file_script(source_file, &nodes),
            TextRange::new(start, start + length),
        );
        if !fidelity.is_exact() {
            return None;
        }
        Some(RenameInfo {
            can_rename: true,
            display_name: text[index_after_last_slash..].to_string(),
            trigger_span,
            file_to_rename: Some(display_name),
            new_file_name: Some(new_file_name),
            ..Default::default()
        })
    }

    /// `getNewFileNameForModuleRename` — adjust the new name based on the old
    /// path that an import specifier resolves to. For example, if specifier
    /// "a.js" resolves to file a.ts, renaming "a.js" -> "b.js" should mean
    /// file rename a.ts -> b.ts.
    fn get_new_file_name_for_module_rename(
        &self,
        old_path: &RootedPath,
        specifier_text: &str,
        new_name: &str,
    ) -> RootedPath {
        let old_file_name = tspath::rooted_file_path_from_path(old_path.clone());
        let mut new_path = old_path.directory().resolve_file(new_name);
        let case_sensitivity = self.case_sensitivity();
        let old_ext = if old_file_name.is_declaration_file() {
            old_file_name.declaration_file_extension().to_string()
        } else {
            old_file_name
                .any_extension(&[], case_sensitivity)
                .into_owned()
        };
        if !new_path.has_extension() {
            new_path = new_path.append_suffix(&old_ext);
        } else if new_path.any_extension(&[], case_sensitivity)
            == tspath::get_any_extension_from_path(specifier_text, &[], case_sensitivity)
        {
            new_path = new_path.change_any_extension(&old_ext, &[], case_sensitivity);
        }
        new_path.as_path()
    }

    /// `getTextForRename`.
    fn get_text_for_rename(
        &self,
        original_node: NodeId,
        entry: &Rc<RefCell<ReferenceEntry>>,
        new_text: &str,
        checker: &Rc<RefCell<Checker>>,
        quote_preference: QuotePreference,
        use_aliases_for_rename: bool,
    ) -> String {
        let (entry_kind, entry_node) = {
            let e = entry.borrow();
            (e.kind, e.node)
        };

        let entry_nodes = entry_node.map(|n| self.program.nodes(n.file_index()));
        let orig_nodes = self.program.nodes(original_node.file_index());

        if use_aliases_for_rename
            && entry_kind != EntryKind::Range
            && (ast::is_identifier(&orig_nodes[original_node])
                || ast::is_string_literal_like(&orig_nodes[original_node]))
        {
            let entry_node = entry_node.expect("node");
            let entry_nodes = entry_nodes.as_ref().expect("entry nodes");
            let node = ast::get_reparsed_node_for_node(entry_node, entry_nodes);
            let kind = entry_kind;
            let parent = entry_nodes[node].parent;
            let name = orig_nodes[original_node].text(&orig_nodes).into_owned();
            let is_shorthand_assignment =
                parent.is_some_and(|p| ast::is_shorthand_property_assignment(&entry_nodes[p]));

            if is_shorthand_assignment
                || parent.is_some_and(|p| {
                    is_object_binding_element_without_property_name(p, entry_nodes)
                        && entry_nodes[p].name() == Some(node)
                        && entry_nodes[p].as_binding_element().dot_dot_dot_token.is_none()
                })
            {
                if kind == EntryKind::SearchedLocalFoundProperty {
                    return format!("{name}: {new_text}");
                }
                if kind == EntryKind::SearchedPropertyFoundLocal {
                    return format!("{new_text}: {name}");
                }
                // In `const o = { x }; o.x`, symbolAtLocation at `x` in
                // `{ x }` is the property symbol. For a binding element
                // `const { x } = o;`, symbolAtLocation at `x` is the property
                // symbol.
                if is_shorthand_assignment {
                    let grand_parent = parent.and_then(|p| entry_nodes[p].parent);
                    let is_module_exports = grand_parent.is_some_and(|gp| {
                        ast::is_object_literal_expression(&entry_nodes[gp])
                            && entry_nodes[gp].parent.is_some_and(|gpp| {
                                ast::is_binary_expression(&entry_nodes[gpp])
                                    && entry_nodes[gpp]
                                        .as_binary_expression()
                                        .left
                                        .is_some_and(|left| {
                                            ast::is_module_exports_access_expression(
                                                &entry_nodes[left],
                                                entry_nodes,
                                            )
                                        })
                            })
                    });
                    if is_module_exports {
                        return format!("{name}: {new_text}");
                    }
                    return format!("{new_text}: {name}");
                }
                return format!("{name}: {new_text}");
            }

            if parent.is_some_and(|p| {
                ast::is_import_specifier(&entry_nodes[p])
                    && entry_nodes[p].property_name().is_none()
            }) {
                // If the original symbol was using this alias, just rename
                // the alias.
                let original_symbol = {
                    let orig_parent = orig_nodes[original_node].parent;
                    if orig_parent
                        .is_some_and(|p| ast::is_export_specifier(&orig_nodes[p]))
                    {
                        checker
                            .borrow_mut()
                            .get_export_specifier_local_target_symbol(
                                orig_parent.expect("parent"),
                            )
                    } else {
                        checker.borrow_mut().get_symbol_at_location_api(original_node)
                    }
                };
                if original_symbol.is_some_and(|symbol| {
                    checker.borrow().symbol_arena.get_ref(symbol)
                        .declarations
                        .contains(&parent.expect("parent"))
                }) {
                    return format!("{name} as {new_text}");
                }
                return new_text.to_string();
            }

            if parent.is_some_and(|p| {
                ast::is_export_specifier(&entry_nodes[p])
                    && entry_nodes[p].property_name().is_none()
            }) {
                // If the symbol for the node is same as declared node symbol
                // use prefix text.
                let same_symbol = original_node == entry_node || {
                    let mut c = checker.borrow_mut();
                    c.get_symbol_at_location_api(original_node)
                        == c.get_symbol_at_location_api(entry_node)
                };
                if same_symbol {
                    return format!("{name} as {new_text}");
                }
                return format!("{new_text} as {name}");
            }
        }

        // If the node is a numerical indexing literal, then add quotes around
        // the property access.
        if entry_kind != EntryKind::Range {
            if let Some(entry_node) = entry_node {
                let entry_nodes = entry_nodes.as_ref().expect("entry nodes");
                if ast::is_numeric_literal(&entry_nodes[entry_node])
                    && entry_nodes[entry_node]
                        .parent
                        .is_some_and(|p| ast::is_access_expression(&entry_nodes[p]))
                {
                    let quote = get_quote_from_preference(quote_preference);
                    return format!("{quote}{new_text}{quote}");
                }
            }
        }

        new_text.to_string()
    }

    /// `getRenameInfoSuccess`.
    fn get_rename_info_success(
        &self,
        node: NodeId,
        source_file: NodeId,
        display_name: String,
    ) -> RenameInfo {
        let mut start = {
            let mut nodes = self.program.nodes_mut(source_file.file_index());
            tokens::get_start_of_node(&mut nodes, source_file, node, false)
        };
        let nodes = self.program.nodes(source_file.file_index());
        let mut end = nodes[node].end();
        if ast::is_string_literal_like(&nodes[node]) {
            // Exclude the quotes.
            start += 1;
            end -= 1;
        }
        let (trigger_span, fidelity) = self.converters.to_lsp_range(
            &source_file_script(source_file, &nodes),
            TextRange::new(start, end),
        );
        if !fidelity.is_exact() {
            return RenameInfo {
                can_rename: false,
                ..Default::default()
            };
        }
        RenameInfo {
            can_rename: true,
            display_name,
            trigger_span,
            ..Default::default()
        }
    }
}

/// `nodeIsEligibleForRename`.
pub(crate) fn node_is_eligible_for_rename(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::Identifier
        | Kind::PrivateIdentifier
        | Kind::StringLiteral
        | Kind::NoSubstitutionTemplateLiteral
        | Kind::ThisKeyword => true,
        Kind::NumericLiteral => is_literal_name_of_property_declaration_or_index_access(node, nodes),
        _ => false,
    }
}

/// `isDefinedInLibraryFile` — checks if a declaration is from a default
/// library file (e.g., lib.d.ts).
fn is_defined_in_library_file(program: &Rc<Program>, declaration: NodeId) -> bool {
    let nodes = program.nodes(declaration.file_index());
    let decl_source_file =
        ast::get_source_file_of_node(Some(declaration), &nodes).expect("source file");
    let sf = nodes[decl_source_file].as_source_file();
    program.is_source_file_default_library(sf.path_key()) && sf.is_declaration_file
}

/// `wouldRenameInOtherNodeModules` — checks if renaming the symbol would
/// affect node_modules.
fn would_rename_in_other_node_modules(
    original_file: NodeId,
    symbol: SymbolId,
    checker: &Rc<RefCell<Checker>>,
    preferences: &lsutil::UserPreferences,
    program: &Rc<Program>,
) -> Option<&'static Message> {
    let mut sym = symbol;
    {
        let symbol_flags = checker.borrow().symbol_arena.get_ref(sym).flags;
        if !preferences
            .provide_prefix_and_suffix_text_for_rename
            .is_true_or_unknown()
            && symbol_flags.intersects(SymbolFlags::ALIAS)
        {
            let declarations =
                checker.borrow().symbol_arena.get_ref(sym).declarations.clone();
            let import_specifier = declarations.iter().copied().find(|&d| {
                let nodes = program.nodes(d.file_index());
                ast::is_import_specifier(&nodes[d])
            });
            if let Some(import_specifier) = import_specifier {
                let nodes = program.nodes(import_specifier.file_index());
                if nodes[import_specifier]
                    .as_import_specifier()
                    .property_name
                    .is_none()
                {
                    drop(nodes);
                    sym = checker
                        .borrow_mut()
                        .get_aliased_symbol(sym)
                        .unwrap_or(sym);
                }
            }
        }
    }

    let declarations = checker.borrow().symbol_arena.get_ref(sym)
        .declarations
        .clone();
    if declarations.is_empty() {
        return None;
    }

    let original_file_name = {
        let nodes = program.nodes(original_file.file_index());
        nodes[original_file].as_source_file().file_name().clone()
    };
    let original_package = node_module_package_root_for_file(&original_file_name);
    if original_package.as_string().is_empty() {
        // Original source file is not in node_modules.
        for declaration in &declarations {
            let nodes = program.nodes(declaration.file_index());
            if let Some(decl_file) =
                ast::get_source_file_of_node(Some(*declaration), &nodes)
            {
                if is_inside_node_modules(nodes[decl_file].as_source_file().file_name()) {
                    return Some(
                        &tsc_diagnostics::You_cannot_rename_elements_that_are_defined_in_a_node_modules_folder,
                    );
                }
            }
        }
        return None;
    }

    // Original source file is in node_modules.
    for declaration in &declarations {
        let nodes = program.nodes(declaration.file_index());
        if let Some(decl_file) = ast::get_source_file_of_node(Some(*declaration), &nodes) {
            let decl_package =
                node_module_package_root_for_file(nodes[decl_file].as_source_file().file_name());
            if !decl_package.as_string().is_empty() && decl_package != original_package {
                return Some(
                    &tsc_diagnostics::You_cannot_rename_elements_that_are_defined_in_another_node_modules_folder,
                );
            }
        }
    }
    None
}

/// `ClientSupportsWillRenameFiles`.
pub(crate) fn client_supports_will_rename_files(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .workspace
        .file_operations
        .will_rename
}

/// `ClientSupportsDocumentChanges`.
pub(crate) fn client_supports_document_changes(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .workspace
        .workspace_edit
        .document_changes
}

/// `ClientSupportsRenameResourceOperations`.
pub(crate) fn client_supports_rename_resource_operations(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .workspace
        .workspace_edit
        .resource_operations
        .contains(&lsproto::ResourceOperationKind::Rename)
}

/// `tryRemoveIndexFileName`.
fn try_remove_index_file_name(file_name: &RootedFilePath) -> Option<RootedPath> {
    if tspath::remove_file_extension(file_name.base_name()) == "index" {
        let (root, relative) = file_name.root_and_relative_path();
        if (root.as_string() == "/" || root.as_path().is_dynamic())
            && tspath::remove_file_extension(relative) == "index"
        {
            return None;
        }
        return Some(file_name.directory().as_path());
    }
    None
}

/// `getQuoteFromPreference`.
fn get_quote_from_preference(quote_preference: QuotePreference) -> &'static str {
    if quote_preference == QuotePreference::SINGLE {
        "'"
    } else {
        "\""
    }
}

/// `getRenameInfoError`.
fn get_rename_info_error(ctx: &Context, message: &'static Message) -> RenameInfo {
    RenameInfo {
        can_rename: false,
        localized_error_message: message.localize(&tsc_locale::from_context(ctx), &[""; 0]),
        ..Default::default()
    }
}

/// `isInsideNodeModules` — mirrors the private helper in `symbols.rs` (the
/// Go original is a package-level function).
fn is_inside_node_modules(file_name: &RootedFilePath) -> bool {
    file_name.contains_lowercase_directory_sequence("/node_modules/")
}
