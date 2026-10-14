// Ported from tsc/internal/execute/incremental/programtosnapshot.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic};
use tsc_ast::ids::NodeId;
use tsc_ast::is_string_literal;
use tsc_ast::utilities::{
    get_source_file_of_node, is_external_or_commonjs_module, is_global_scope_augmentation,
    is_json_source_file, is_module_with_string_literal_name,
};
use tsc_collections::Set;
use tsc_compiler::program::Program as CompilerProgram;
use tsc_core::context::Context;
use tsc_tsoptions::generated::options::{
    compiler_options_affect_declaration_path, compiler_options_affect_emit,
    compiler_options_affect_semantic_diagnostics,
};
use tsc_tspath::{PathKey, RootedFilePath, to_rooted_file_path};

use crate::incremental::program::Program;
use crate::incremental::snapshot::{
    BuildInfoDiagnosticWithFileName, DiagnosticsOrBuildInfoDiagnosticsWithFileName, FileInfo,
    Snapshot, get_file_emit_kind, get_pending_emit_kind_with_options, repopulate_diagnostic_chain,
};

/// `func programToSnapshot` — computes the incremental snapshot for a
/// program, reusing what it can from the old program's snapshot.
pub(crate) fn program_to_snapshot(
    program: &Rc<CompilerProgram>,
    old_program: Option<&Program>,
    hash_with_text: bool,
) -> Rc<Snapshot> {
    if let Some(old_program) = old_program {
        if old_program
            .program
            .as_ref()
            .is_some_and(|p| Rc::ptr_eq(p, program))
        {
            return old_program.snapshot.clone();
        }
    }
    let mut snapshot = Snapshot::default();
    snapshot.options = program.options();
    snapshot.hash_with_text = hash_with_text;
    snapshot
        .check_pending
        .set(program.options_ref().no_check.is_true());
    let mut to = ToProgramSnapshot {
        program,
        old_program,
        snapshot,
        global_file_removed: false,
    };

    if to.snapshot.can_use_incremental_state() {
        to.reuse_from_old_program();
        to.compute_program_file_changes();
        to.handle_file_delete();
        to.handle_global_scope_change();
        to.handle_pending_emit();
        to.handle_pending_check();
    }
    Rc::new(to.snapshot)
}

/// `type toProgramSnapshot struct`.
struct ToProgramSnapshot<'a> {
    program: &'a Rc<CompilerProgram>,
    old_program: Option<&'a Program>,
    snapshot: Snapshot,
    global_file_removed: bool,
}

impl ToProgramSnapshot<'_> {
    /// `(*toProgramSnapshot) reuseFromOldProgram`.
    fn reuse_from_old_program(&mut self) {
        if let Some(old_program) = self.old_program {
            if self.snapshot.options.composite.is_true() {
                *self.snapshot.latest_changed_dts_file.borrow_mut() = old_program
                    .snapshot
                    .latest_changed_dts_file
                    .borrow()
                    .clone();
            }
            // Copy old snapshot's changed files set.
            old_program.snapshot.changed_files_set.range(|key| {
                self.snapshot.changed_files_set.add(key);
                true
            });
            old_program
                .snapshot
                .affected_files_pending_emit
                .range(|key, emit_kind| {
                    self.snapshot
                        .affected_files_pending_emit
                        .store(key, emit_kind);
                    true
                });
            self.snapshot.build_info_emit_pending.store(
                old_program
                    .snapshot
                    .build_info_emit_pending
                    .load(std::sync::atomic::Ordering::SeqCst),
                std::sync::atomic::Ordering::SeqCst,
            );
            self.snapshot.has_errors_from_old_state = old_program.snapshot.has_errors.get();
            self.snapshot.has_semantic_errors_from_old_state =
                old_program.snapshot.has_semantic_errors.get();
            self.snapshot.package_jsons_from_old_state =
                old_program.snapshot.package_jsons.borrow().clone();
            self.snapshot.missing_package_jsons_from_old_state =
                old_program.snapshot.missing_package_jsons.borrow().clone();
        } else {
            self.snapshot.build_info_emit_pending.store(
                self.snapshot.options.is_incremental(),
                std::sync::atomic::Ordering::SeqCst,
            );
        }
    }

    /// `(*toProgramSnapshot) computeProgramFileChanges`.
    ///
    /// PORT: Go queues one job per file on `core.NewWorkGroup(program.
    /// SingleThreaded())`. The Rust `WorkGroup` requires `Send` closures and
    /// the compiler program is `Rc`-based, so the loop runs sequentially here.
    /// All state writes go through `SyncMap`/`SyncSet` keyed by path, so the
    /// result is identical regardless of job order.
    fn compute_program_file_changes(&mut self) {
        let can_copy_semantic_diagnostics = self.old_program.is_some()
            && !compiler_options_affect_semantic_diagnostics(
                self.old_program.map(|p| &*p.snapshot.options),
                Some(self.snapshot.options.as_ref()),
            );
        // We can only reuse emit signatures (i.e. .d.ts signatures) if the
        // .d.ts file is unchanged, which will eg be dependent on change in
        // options like declarationDir and outDir options are unchanged.
        // We need to look in oldState.compilerOptions, rather than
        // oldCompilerOptions (i.e. we need to disregard useOldState) because
        // oldCompilerOptions can be undefined if there was change in say
        // module from None to some other option which would make useOldState
        // as false since we can now use reference maps that are needed to
        // track what to emit, what to check etc but that option change does
        // not affect d.ts file name so emitSignatures should still be reused.
        let can_copy_emit_signatures = self.snapshot.options.composite.is_true()
            && self.old_program.is_some()
            && !compiler_options_affect_declaration_path(
                self.old_program.map(|p| &*p.snapshot.options),
                Some(self.snapshot.options.as_ref()),
            );
        let copy_declaration_file_diagnostics = can_copy_semantic_diagnostics
            && self.snapshot.options.skip_lib_check.is_true()
                == self
                    .old_program
                    .expect("checked above")
                    .snapshot
                    .options
                    .skip_lib_check
                    .is_true();
        let copy_lib_file_diagnostics = copy_declaration_file_diagnostics
            && self.snapshot.options.skip_default_lib_check.is_true()
                == self
                    .old_program
                    .expect("checked above")
                    .snapshot
                    .options
                    .skip_default_lib_check
                    .is_true();

        for &file in self.program.source_files_slice() {
            self.compute_file_change(
                file,
                can_copy_semantic_diagnostics,
                can_copy_emit_signatures,
                copy_declaration_file_diagnostics,
                copy_lib_file_diagnostics,
            );
        }
    }

    /// The body of the Go `wg.Queue` closure inside `computeProgramFileChanges`.
    fn compute_file_change(
        &mut self,
        file: NodeId,
        can_copy_semantic_diagnostics: bool,
        can_copy_emit_signatures: bool,
        copy_declaration_file_diagnostics: bool,
        copy_lib_file_diagnostics: bool,
    ) {
        let (version_text, is_declaration_file) = {
            let nodes = self.program.arena_of(file);
            let sf = nodes[file].as_source_file();
            let version_text = if !sf.content_mapper().is_empty() {
                format!(
                    "{}\x00{}",
                    sf.original_text(),
                    sf.content_mapper_info
                        .as_ref()
                        .map(|info| info.transform_identity.as_str())
                        .unwrap_or_default()
                )
            } else {
                sf.text().to_string()
            };
            (version_text, sf.is_declaration_file)
        };
        let version = self.snapshot.compute_hash(&version_text);
        let file_path_key = {
            let nodes = self.program.arena_of(file);
            nodes[file].as_source_file().path_key().clone()
        };
        let implied_node_format = self
            .program
            .get_source_file_meta_data(&file_path_key)
            .implied_node_format;
        let affects_global_scope = file_affects_global_scope(self.program, file);
        let mut signature = String::new();
        let new_references = get_referenced_files(self.program, file);
        if new_references.is_some() {
            self.snapshot
                .referenced_map
                .store_references(file_path_key.clone(), new_references.clone().map(Rc::new));
        }
        if let Some(old_program) = self.old_program {
            if let Some(old_file_info) = old_program.snapshot.file_infos.load(&file_path_key) {
                let (old_version, old_affects_global_scope, old_implied_node_format, old_signature) = {
                    let info = old_file_info.borrow();
                    (
                        info.version.clone(),
                        info.affects_global_scope,
                        info.implied_node_format,
                        info.signature.clone(),
                    )
                };
                signature = old_signature;
                if old_version != version
                    || old_affects_global_scope != affects_global_scope
                    || old_implied_node_format != implied_node_format
                {
                    self.snapshot.add_file_to_change_set(file_path_key.clone());
                } else if !Set::equals(
                    new_references.as_ref(),
                    old_program
                        .snapshot
                        .referenced_map
                        .get_references(&file_path_key)
                        .as_deref(),
                ) {
                    // Referenced files changed.
                    self.snapshot.add_file_to_change_set(file_path_key.clone());
                } else if let Some(new_references) = &new_references {
                    for ref_path in new_references.keys().iter() {
                        if self.program.get_source_file_by_path(ref_path).is_none()
                            && old_program.snapshot.file_infos.load(ref_path).is_some()
                        {
                            // Referenced file was deleted in the new program.
                            self.snapshot.add_file_to_change_set(file_path_key.clone());
                            break;
                        }
                    }
                }
            } else {
                self.snapshot.add_file_to_change_set(file_path_key.clone());
            }
            if !self.snapshot.changed_files_set.has(&file_path_key) {
                if let Some(emit_diagnostics) = old_program
                    .snapshot
                    .emit_diagnostics_per_file
                    .load(&file_path_key)
                {
                    self.snapshot.emit_diagnostics_per_file.store(
                        file_path_key.clone(),
                        repopulate_diagnostics_of_file(&emit_diagnostics, self.program, file),
                    );
                }
                if can_copy_semantic_diagnostics
                    && (!is_declaration_file || copy_declaration_file_diagnostics)
                    && (!self.program.is_source_file_default_library(&file_path_key)
                        || copy_lib_file_diagnostics)
                {
                    // Unchanged file — copy diagnostics.
                    if let Some(diagnostics) = old_program
                        .snapshot
                        .semantic_diagnostics_per_file
                        .load(&file_path_key)
                    {
                        self.snapshot.semantic_diagnostics_per_file.store(
                            file_path_key.clone(),
                            repopulate_diagnostics_of_file(&diagnostics, self.program, file),
                        );
                    }
                }
            }
            if can_copy_emit_signatures {
                if let Some(old_emit_signature) =
                    old_program.snapshot.emit_signatures.load(&file_path_key)
                {
                    self.snapshot.emit_signatures.store(
                        file_path_key.clone(),
                        Rc::new(old_emit_signature.get_new_emit_signature(
                            &old_program.snapshot.options,
                            &self.snapshot.options,
                        )),
                    );
                }
            }
        } else {
            self.snapshot.add_file_to_affected_files_pending_emit(
                file_path_key.clone(),
                get_file_emit_kind(&self.snapshot.options),
            );
            signature = version.clone();
        }
        self.snapshot.file_infos.store(
            file_path_key,
            Rc::new(RefCell::new(FileInfo {
                version,
                signature,
                affects_global_scope,
                implied_node_format,
            })),
        );
    }

    /// `(*toProgramSnapshot) handleFileDelete`.
    fn handle_file_delete(&mut self) {
        let Some(old_program) = self.old_program else {
            return;
        };
        // If the global file is removed, add all files as changed.
        old_program
            .snapshot
            .file_infos
            .range(|file_path, old_info| {
                if self.snapshot.file_infos.load(&file_path).is_none() {
                    if old_info.borrow().affects_global_scope {
                        let files = self
                            .snapshot
                            .get_all_files_excluding_default_library_file(self.program, None)
                            .clone();
                        for file in files {
                            let key = {
                                let nodes = self.program.arena_of(file);
                                nodes[file].as_source_file().path_key().clone()
                            };
                            self.snapshot.add_file_to_change_set(key);
                        }
                        self.global_file_removed = true;
                    } else {
                        self.snapshot
                            .build_info_emit_pending
                            .store(true, std::sync::atomic::Ordering::SeqCst);
                    }
                    return false;
                }
                true
            });
    }

    /// `(*toProgramSnapshot) handleGlobalScopeChange`.
    fn handle_global_scope_change(&mut self) {
        if self.old_program.is_none() || self.global_file_removed {
            return;
        }
        let mut global_scope_lost = false;
        self.old_program
            .expect("checked above")
            .snapshot
            .file_infos
            .range(|file_path, old_info| {
                if !old_info.borrow().affects_global_scope {
                    return true;
                }
                if let Some(new_info) = self.snapshot.file_infos.load(&file_path) {
                    if !new_info.borrow().affects_global_scope {
                        global_scope_lost = true;
                        return false;
                    }
                }
                true
            });
        if global_scope_lost {
            let files = self
                .snapshot
                .get_all_files_excluding_default_library_file(self.program, None)
                .clone();
            for file in files {
                let key = {
                    let nodes = self.program.arena_of(file);
                    nodes[file].as_source_file().path_key().clone()
                };
                self.snapshot.add_file_to_change_set(key);
            }
        }
    }

    /// `(*toProgramSnapshot) handlePendingEmit`.
    fn handle_pending_emit(&mut self) {
        if self.old_program.is_some() && !self.global_file_removed {
            let old_program = self.old_program.expect("checked above");
            // If options affect emit, then we need to do complete emit per
            // compiler options; otherwise only the js or dts that needs to be
            // emitted because it is different from previously emitted options.
            let pending_emit_kind = if compiler_options_affect_emit(
                Some(old_program.snapshot.options.as_ref()),
                Some(self.snapshot.options.as_ref()),
            ) {
                get_file_emit_kind(&self.snapshot.options)
            } else {
                get_pending_emit_kind_with_options(
                    &self.snapshot.options,
                    &old_program.snapshot.options,
                )
            };
            if pending_emit_kind != 0 {
                // Add all files to affectedFilesPendingEmit since emit changed.
                for &file in self.program.source_files_slice() {
                    let key = {
                        let nodes = self.program.arena_of(file);
                        nodes[file].as_source_file().path_key().clone()
                    };
                    // Add to affectedFilesPendingEmit only if not changed,
                    // since any changed file will do full emit.
                    if !self.snapshot.changed_files_set.has(&key) {
                        self.snapshot
                            .add_file_to_affected_files_pending_emit(key, pending_emit_kind);
                    }
                }
                self.snapshot
                    .build_info_emit_pending
                    .store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }
    }

    /// `(*toProgramSnapshot) handlePendingCheck`.
    fn handle_pending_check(&mut self) {
        if let Some(old_program) = self.old_program {
            if self.snapshot.semantic_diagnostics_per_file.size()
                != self.program.source_files_slice().len()
                && old_program.snapshot.check_pending.get() != self.snapshot.check_pending.get()
            {
                self.snapshot
                    .build_info_emit_pending
                    .store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }
    }
}

/// `func fileAffectsGlobalScope`.
fn file_affects_global_scope(program: &CompilerProgram, file: NodeId) -> bool {
    {
        let mut nodes = program.nodes_mut(file.file_index());
        let mut symbols = program.symbols.clone();
        tsc_binder::binder::bind_source_file(&mut nodes, file, &mut symbols);
    }
    let nodes = program.arena_of(file);
    let sf = nodes[file].as_source_file();
    // If file contains anything that augments the global scope we need to
    // build it as if it is a global file as well as a module.
    if sf.module_augmentations.iter().any(|&augmentation| {
        nodes[augmentation]
            .parent
            .is_some_and(|parent| is_global_scope_augmentation(&nodes[parent]))
    }) {
        return true;
    }

    if is_external_or_commonjs_module(sf) || is_json_source_file(sf) {
        return false;
    }

    // For script files that contain only ambient external modules, although
    // they are not actually external module files, they can only be consumed
    // via importing elements from them. Regular script files cannot consume
    // them. Therefore, there is no point rebuilding all script files if these
    // special files have changed. However, if any statement in the file is not
    // an ambient external module, we treat it as a regular script file.
    sf.statements.as_ref().is_some_and(|statements| {
        statements
            .nodes
            .iter()
            .any(|stmt| !is_module_with_string_literal_name(&nodes[*stmt], &nodes))
    })
}

/// `func addReferencedFilesFromSymbol`.
fn add_referenced_files_from_symbol(
    program: &CompilerProgram,
    file: NodeId,
    referenced_files: &mut Set<PathKey>,
    symbol: Option<tsc_ast::ids::SymbolId>,
) {
    let Some(symbol) = symbol else {
        return;
    };
    let declarations = program.symbols.get_ref(symbol)
        .declarations
        .clone();
    for declaration in declarations {
        let file_of_decl = {
            let nodes = program.arena_of(declaration);
            get_source_file_of_node(Some(declaration), &nodes)
        };
        let Some(file_of_decl) = file_of_decl else {
            continue;
        };
        if file != file_of_decl {
            let key = {
                let nodes = program.arena_of(file_of_decl);
                nodes[file_of_decl].as_source_file().path_key().clone()
            };
            referenced_files.add(key);
        }
    }
}

/// `func addReferencedFilesFromImportLiteral` — get the module source file and
/// all augmenting files from the import name node of the file.
fn add_referenced_files_from_import_literal(
    program: &CompilerProgram,
    file: NodeId,
    referenced_files: &mut Set<PathKey>,
    checker: &mut tsc_checker::checker_core::Checker,
    import_name: NodeId,
) {
    let symbol = checker.get_symbol_at_location_api(import_name);
    add_referenced_files_from_symbol(program, file, referenced_files, symbol);
}

/// `func addReferencedFileFromFileName` — gets the path of the reference file
/// from a file name, which may be a resolved redirect path.
fn add_referenced_file_from_file_name(
    program: &CompilerProgram,
    file_name: &RootedFilePath,
    referenced_files: &mut Set<PathKey>,
) {
    let redirect = program.get_parse_file_redirect(file_name);
    if !redirect.as_string().is_empty() {
        referenced_files.add(program.path_key_for_file_name(&redirect));
    } else {
        referenced_files.add(program.path_key_for_file_name(file_name));
    }
}

/// `func getReferencedFiles` — the referenced files for a file from the
/// program, as a set of `PathKey`s.
fn get_referenced_files(program: &CompilerProgram, file: NodeId) -> Option<Set<PathKey>> {
    let mut referenced_files = Set::new();

    // We need to use a set here since the code can contain the same import
    // twice, but that will only be one dependency.
    // To avoid internal conversion, the key of the referencedFiles map must be
    // of type Path.
    let (checker, done) = program.get_type_checker_for_file_exclusive(Context::default(), file);
    {
        let mut checker_guard = checker.borrow_mut();
        let checker = &mut *checker_guard;
        let (imports, source_file_directory, referenced_file_names, module_augmentations, path_key) = {
            let nodes = program.arena_of(file);
            let sf = nodes[file].as_source_file();
            (
                sf.imports.to_vec(),
                sf.file_name().directory(),
                sf.referenced_files
                    .iter()
                    .map(|reference| reference.file_name.clone())
                    .collect::<Vec<_>>(),
                sf.module_augmentations.to_vec(),
                sf.path_key().clone(),
            )
        };
        for import_name in imports {
            add_referenced_files_from_import_literal(
                program,
                file,
                &mut referenced_files,
                checker,
                import_name,
            );
        }

        // Handle triple slash references.
        for file_name in referenced_file_names {
            add_referenced_file_from_file_name(
                program,
                &to_rooted_file_path(&file_name, &source_file_directory),
                &mut referenced_files,
            );
        }

        // Handle type reference directives.
        if let Some(type_refs_in_file) = program
            .get_resolved_type_reference_directives()
            .get(&path_key)
        {
            for type_ref in type_refs_in_file.values() {
                if !type_ref.resolved_file_name.as_string().is_empty() {
                    add_referenced_file_from_file_name(
                        program,
                        &type_ref.resolved_file_name,
                        &mut referenced_files,
                    );
                }
            }
        }

        // Add module augmentations as references.
        for module_name in module_augmentations {
            let is_string_literal = {
                let nodes = program.arena_of(module_name);
                is_string_literal(&nodes[module_name])
            };
            if !is_string_literal {
                continue;
            }
            add_referenced_files_from_import_literal(
                program,
                file,
                &mut referenced_files,
                checker,
                module_name,
            );
        }

        // From ambient modules.
        for ambient_module in checker.get_ambient_modules() {
            add_referenced_files_from_symbol(
                program,
                file,
                &mut referenced_files,
                Some(ambient_module),
            );
        }
    }
    done();
    if referenced_files.len() > 0 {
        Some(referenced_files)
    } else {
        None
    }
}

/// `func repopulateDiagnosticsOfFile` — repopulates diagnostic chains that
/// depend on program state. When diagnostics are copied from a previous build,
/// their message chains may reference stale program state (e.g., resolved
/// module alternate results, package.json scope). This function recomputes
/// those chains using the current program's state.
pub(crate) fn repopulate_diagnostics_of_file(
    diags: &Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>>,
    p: &CompilerProgram,
    file: NodeId,
) -> Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>> {
    if diags.borrow().diagnostics.is_some() {
        let repopulated =
            repopulate_diagnostics_list(diags.borrow().diagnostics.as_deref().unwrap(), p, file);
        match repopulated {
            None => return diags.clone(),
            Some(repopulated) => {
                return Rc::new(RefCell::new(
                    DiagnosticsOrBuildInfoDiagnosticsWithFileName {
                        diagnostics: Some(repopulated),
                        build_info_diagnostics: Vec::new(),
                    },
                ));
            }
        }
    }
    // buildInfoDiagnostics will be repopulated via toDiagnostic's
    // repopulateInfo handling.
    diags.clone()
}

/// `func repopulateDiagnosticsList` — returns `None` if no diagnostics needed
/// repopulation (i.e., no changes were made).
fn repopulate_diagnostics_list(
    diags: &[DiagnosticRef],
    p: &CompilerProgram,
    file: NodeId,
) -> Option<Vec<DiagnosticRef>> {
    let mut changed = false;
    let mut result = Vec::with_capacity(diags.len());
    for d in diags {
        let message_chain = { lock_diagnostic(d).message_chain().to_vec() };
        if let Some(repopulated) = repopulate_diagnostic_message_chain(&message_chain, p, file) {
            let clone = lock_diagnostic(d).clone_diagnostic();
            lock_diagnostic(&clone).set_message_chain(repopulated);
            result.push(clone);
            changed = true;
        } else {
            result.push(d.clone());
        }
    }
    if !changed {
        return None;
    }
    Some(result)
}

/// `func repopulateDiagnosticMessageChain` — repopulates chains that have
/// repopulate info. Returns `None` if no changes were made.
fn repopulate_diagnostic_message_chain(
    chain: &[DiagnosticRef],
    p: &CompilerProgram,
    file: NodeId,
) -> Option<Vec<DiagnosticRef>> {
    if chain.is_empty() {
        return None;
    }
    let mut changed = false;
    let mut result = Vec::with_capacity(chain.len());
    for c in chain {
        let c_lock = lock_diagnostic(c);
        if c_lock.repopulate_info().is_some() {
            // Convert to buildInfoDiagnosticWithFileName and repopulate.
            let b = ast_diag_to_build_info_diag_locked(&c_lock);
            drop(c_lock);
            result.push(repopulate_diagnostic_chain(&b, p, Some(file)));
            changed = true;
        } else {
            // Check nested chains.
            let nested_chain = c_lock.message_chain().to_vec();
            drop(c_lock);
            if let Some(nested) = repopulate_diagnostic_message_chain(&nested_chain, p, file) {
                let clone = lock_diagnostic(c).clone_diagnostic();
                lock_diagnostic(&clone).set_message_chain(nested);
                result.push(clone);
                changed = true;
            } else {
                result.push(c.clone());
            }
        }
    }
    if !changed {
        return None;
    }
    Some(result)
}

/// `func astDiagToBuildInfoDiag`.
fn ast_diag_to_build_info_diag(d: &DiagnosticRef) -> BuildInfoDiagnosticWithFileName {
    ast_diag_to_build_info_diag_locked(&lock_diagnostic(d))
}

fn ast_diag_to_build_info_diag_locked(
    d: &std::sync::MutexGuard<'_, tsc_ast::diagnostic::Diagnostic>,
) -> BuildInfoDiagnosticWithFileName {
    let mut b = BuildInfoDiagnosticWithFileName {
        pos: d.pos(),
        end: d.end(),
        code: d.code(),
        category: d.category(),
        source: d.source().to_string(),
        message_text: d.message_text().to_string(),
        message_key: d.message_key(),
        message_args: d.message_args().to_vec(),
        repopulate_info: d.repopulate_info().cloned(),
        ..Default::default()
    };
    b.message_chain = d
        .message_chain()
        .iter()
        .map(ast_diag_to_build_info_diag)
        .collect();
    b
}
