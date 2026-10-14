// Ported from tsc/internal/execute/incremental/affectedfileshandler.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

use rustc_hash::FxHashMap;
use tsc_ast::ids::{NodeId, SymbolId};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::utilities::{get_source_file_of_node, is_json_source_file};
use tsc_collections::{SyncMap, SyncSet};
use tsc_compiler::emit_host::{EmitOnly, EmitOptions};
use tsc_core::context::Context;
use tsc_tspath::PathKey;

use crate::incremental::emit_files_handler::path_key_of;
use crate::incremental::program::{Program, SignatureUpdateKind};
use crate::incremental::snapshot::{
    FILE_EMIT_KIND_ALL_DTS, FILE_EMIT_KIND_DTS, FileEmitKind, get_file_emit_kind,
};

/// `type dtsMayChange map[tspath.PathKey]FileEmitKind`.
///
/// PORT: Go's map is a reference type passed by value; `Rc<DtsMayChange>`
/// with an inner `RefCell` reproduces the shared mutation.
pub(crate) struct DtsMayChange(pub RefCell<FxHashMap<PathKey, FileEmitKind>>);

impl DtsMayChange {
    /// `dtsMayChange.addFileToAffectedFilesPendingEmit`.
    pub fn add_file_to_affected_files_pending_emit(
        &self,
        file_path: PathKey,
        emit_kind: FileEmitKind,
    ) {
        self.0.borrow_mut().insert(file_path, emit_kind);
    }
}

/// `type updatedSignature struct` — the `sync.Mutex` is kept for parity with
/// Go's "ensure calculations for existing ones are complete" contract; the
/// port runs these handlers sequentially so the lock never contends.
#[derive(Default)]
struct UpdatedSignature {
    signature: String,
    kind: SignatureUpdateKind,
}

/// `type affectedFilesHandler struct`.
pub(crate) struct AffectedFilesHandler<'a> {
    ctx: Context,
    program: &'a Program,
    has_all_files_excluding_default_library_file: AtomicBool,
    updated_signatures: SyncMap<PathKey, Rc<Mutex<UpdatedSignature>>>,
    dts_may_change: RefCell<Vec<Rc<DtsMayChange>>>,
    files_to_remove_diagnostics: SyncSet<PathKey>,
    cleaned_diagnostics_of_lib_files: std::sync::Once,
    seen_file_and_references: SyncMap<PathKey, bool>,
}

impl<'a> AffectedFilesHandler<'a> {
    fn new(ctx: Context, program: &'a Program) -> Self {
        AffectedFilesHandler {
            ctx,
            program,
            has_all_files_excluding_default_library_file: AtomicBool::new(false),
            updated_signatures: SyncMap::new(),
            dts_may_change: RefCell::new(Vec::new()),
            files_to_remove_diagnostics: SyncSet::new(),
            cleaned_diagnostics_of_lib_files: std::sync::Once::new(),
            seen_file_and_references: SyncMap::new(),
        }
    }

    /// `(*affectedFilesHandler) getDtsMayChange`.
    fn get_dts_may_change(
        &self,
        affected_file_path: PathKey,
        affected_file_emit_kind: FileEmitKind,
    ) -> Rc<DtsMayChange> {
        let result = Rc::new(DtsMayChange(RefCell::new(FxHashMap::from_iter([(
            affected_file_path,
            affected_file_emit_kind,
        )]))));
        self.dts_may_change.borrow_mut().push(result.clone());
        result
    }

    /// `(*affectedFilesHandler) isChangedSignature` — called after updating
    /// signatures of that path, so the signature is present in
    /// `updatedSignatures` and already calculated.
    fn is_changed_signature(&self, path: &PathKey) -> bool {
        let new_signature = self
            .updated_signatures
            .load(path)
            .expect("signature must have been updated");
        let new_signature = new_signature.lock().unwrap().signature.clone();
        let old_info = self.program.snapshot.file_infos.load(path);
        new_signature != old_info.expect("file info").borrow().signature
    }

    /// `(*affectedFilesHandler) removeSemanticDiagnosticsOf`.
    fn remove_semantic_diagnostics_of(&self, path: PathKey) {
        self.files_to_remove_diagnostics.add(path);
    }

    /// `(*affectedFilesHandler) removeDiagnosticsOfLibraryFiles`.
    fn remove_diagnostics_of_library_files(&self) {
        self.cleaned_diagnostics_of_lib_files.call_once(|| {
            let program = self.program.expect_program();
            for &file in program.source_files_slice() {
                let path_key = {
                    let nodes = program.arena_of(file);
                    nodes[file].as_source_file().path_key().clone()
                };
                if program.is_source_file_default_library(&path_key)
                    && !program.skip_type_checking(file, true)
                {
                    self.files_to_remove_diagnostics.add(path_key);
                }
            }
        });
    }

    /// `(*affectedFilesHandler) computeDtsSignature`.
    fn compute_dts_signature(&self, file: NodeId) -> String {
        // PORT: `WriteFileFn` is `Fn` (not `FnMut`), so the captured signature
        // is stored in a `RefCell`.
        let signature = RefCell::new(String::new());
        let done = self.program.begin_nested_emit();
        {
            let mut options = EmitOptions {
                target_source_files: Some(vec![file]),
                emit_only: EmitOnly::BuilderSignature,
                ..Default::default()
            };
            options.write_file = Some(Box::new(|file_name, text, data| {
                if !file_name.is_declaration_file() {
                    panic!(
                        "File extension for signature expected to be dts, got : {}",
                        file_name.as_string()
                    );
                }
                *signature.borrow_mut() = self.program.snapshot.compute_signature_with_diagnostics(
                    self.program.expect_program(),
                    file,
                    text,
                    data,
                );
                Ok(())
            }));
            self.program
                .expect_program()
                .emit(self.ctx.clone(), &mut options);
        }
        drop(done);
        signature.into_inner()
    }

    /// `(*affectedFilesHandler) updateShapeSignature`.
    fn update_shape_signature(&self, file: NodeId, use_file_version_as_signature: bool) -> bool {
        let path_key = {
            let program = self.program.expect_program();
            let nodes = program.arena_of(file);
            nodes[file].as_source_file().path_key().clone()
        };
        let update = Rc::new(Mutex::new(UpdatedSignature::default()));
        // If we have cached the result for this file, that means hence forth
        // we should assume file shape is up to date.
        let (stored, loaded) = self
            .updated_signatures
            .load_or_store(path_key.clone(), update.clone());
        if loaded {
            // Ensure calculations for existing ones are complete before using
            // the value.
            let _existing = stored.lock().unwrap();
            return false;
        }

        let mut update = update.lock().unwrap();
        let info = self
            .program
            .snapshot
            .file_infos
            .load(&path_key)
            .expect("file info");
        let prev_signature = info.borrow().signature.clone();
        // JSON files have no declaration output from which to compute a shape
        // signature, so use the file version to conservatively invalidate
        // dependents.
        let (is_declaration_file, is_json) = {
            let program = self.program.expect_program();
            let nodes = program.arena_of(file);
            let sf = nodes[file].as_source_file();
            (sf.is_declaration_file, is_json_source_file(sf))
        };
        if !is_declaration_file && !is_json && !use_file_version_as_signature {
            update.signature = self.compute_dts_signature(file);
        }
        // Default is to use file version as signature.
        if update.signature.is_empty() {
            update.signature = info.borrow().version.clone();
            update.kind = SignatureUpdateKind::UsedVersion;
        }
        update.signature != prev_signature
    }

    /// `(*affectedFilesHandler) getFilesAffectedBy`.
    fn get_files_affected_by(&self, path: &PathKey) -> Vec<NodeId> {
        let Some(file) = self.program.expect_program().get_source_file_by_path(path) else {
            return Vec::new();
        };

        if !self.update_shape_signature(file, false) {
            return vec![file];
        }

        let affects_global_scope = self
            .program
            .snapshot
            .file_infos
            .load(&path_key_of(self.program, file))
            .map(|info| info.borrow().affects_global_scope)
            .unwrap_or(false);
        if affects_global_scope {
            self.has_all_files_excluding_default_library_file
                .store(true, Ordering::SeqCst);
            return self
                .program
                .snapshot
                .get_all_files_excluding_default_library_file(
                    self.program.expect_program(),
                    Some(file),
                )
                .clone();
        }

        if self.program.snapshot.options.isolated_modules.is_true() {
            return vec![file];
        }

        // Now we need to see if each file in the referencedBy list has a
        // shape change as well. Because if so, its own referencedBy files need
        // to be saved as well to make the emitting result consistent with
        // files on disk.
        let seen_file_names_map =
            self.for_each_file_referenced_by(file, &mut |current_file, _current_path| {
                // If the current file is not nil and has a shape change, we
                // need to queue it for processing.
                match current_file {
                    Some(current_file) if self.update_shape_signature(current_file, false) => {
                        (true, false)
                    }
                    _ => (false, false),
                }
            });
        // Return array of values that needs emit.
        seen_file_names_map.values().flatten().copied().collect()
    }

    /// `(*affectedFilesHandler) forEachFileReferencedBy` — `fn` returns
    /// `(queue_for_file, fast_return)` like Go.
    fn for_each_file_referenced_by(
        &self,
        file: NodeId,
        f: &mut dyn FnMut(Option<NodeId>, &PathKey) -> (bool, bool),
    ) -> FxHashMap<PathKey, Option<NodeId>> {
        let mut seen_file_names_map: FxHashMap<PathKey, Option<NodeId>> = FxHashMap::default();
        // Start with the paths this file was referenced by.
        let file_key = path_key_of(self.program, file);
        seen_file_names_map.insert(file_key.clone(), Some(file));
        let mut queue = self
            .program
            .snapshot
            .referenced_map
            .get_referenced_by(&file_key);
        while let Some(current_path) = queue.pop() {
            if !seen_file_names_map.contains_key(&current_path) {
                let current_file = self
                    .program
                    .expect_program()
                    .get_source_file_by_path(&current_path);
                seen_file_names_map.insert(current_path.clone(), current_file);
                let (queue_for_file, fast_return) = f(current_file, &current_path);
                if fast_return {
                    return seen_file_names_map;
                }
                if queue_for_file {
                    if let Some(current_file) = current_file {
                        queue.extend(
                            self.program
                                .snapshot
                                .referenced_map
                                .get_referenced_by(&path_key_of(self.program, current_file)),
                        );
                    }
                }
            }
        }
        seen_file_names_map
    }

    /// `(*affectedFilesHandler) handleDtsMayChangeOfAffectedFile` — handles
    /// semantic diagnostics and dts emit for affectedFile and files that are
    /// referencing modules that export entities from affected file. This is
    /// because even though js emit doesn't change, dts emit / type used can
    /// change, resulting in need for dts emit and js change.
    fn handle_dts_may_change_of_affected_file(
        &self,
        dts_may_change: &DtsMayChange,
        affected_file: NodeId,
    ) {
        let affected_key = path_key_of(self.program, affected_file);
        self.remove_semantic_diagnostics_of(affected_key.clone());

        // If affected files is everything except default library, then
        // nothing more to do.
        if self
            .has_all_files_excluding_default_library_file
            .load(Ordering::SeqCst)
        {
            self.remove_diagnostics_of_library_files();
            // When a change affects the global scope, all files are
            // considered to be affected without updating their signature.
            // That means when affected file is handled, its signature can be
            // out of date. To avoid this, ensure that we update the signature
            // for any affected file in this scenario.
            self.update_shape_signature(affected_file, false);
            return;
        }

        if self
            .program
            .snapshot
            .options
            .assume_changes_only_affect_direct_dependencies
            .is_true()
        {
            return;
        }

        // Iterate on referencing modules that export entities from affected
        // file and delete diagnostics and add pending emit. If there was a
        // change in signature (dts output) for the changed file, then only do
        // we need to handle pending file emit.
        if !self.program.snapshot.changed_files_set.has(&affected_key)
            || !self.is_changed_signature(&affected_key)
        {
            return;
        }

        // At this point affectedFile is actually one of the changed files
        // that has some change in its .d.ts signature.

        // Since isolated modules don't change js files, files affected by
        // change in signature is itself. But we need to cleanup semantic
        // diagnostics and queue dts emit for affected files.
        if self.program.snapshot.options.isolated_modules.is_true() {
            self.for_each_file_referenced_by(affected_file, &mut |_current_file, current_path| {
                if self.handle_dts_may_change_of_global_scope(
                    dts_may_change,
                    current_path,
                    /*invalidate_js_files*/ false,
                ) {
                    return (false, true);
                }
                self.handle_dts_may_change_of(
                    dts_may_change,
                    current_path,
                    /*invalidate_js_files*/ false,
                );
                (self.is_changed_signature(current_path), false)
            });
        }

        let mut invalidate_js_files = false;
        // If exported const enum, we need to ensure that js files are emitted
        // as well since the const enum value changed.
        let program = self.program.expect_program();
        let affected_symbol = {
            let nodes = program.arena_of(affected_file);
            nodes[affected_file].symbol()
        };
        if let Some(symbol) = affected_symbol {
            let exports: Vec<SymbolId> = program.symbols.get_ref(symbol)
                .exports
                .values()
                .copied()
                .collect();
            let mut type_checker: Option<(Rc<RefCell<tsc_checker::checker_core::Checker>>, _)> =
                None;
            for exported in exports {
                if program.symbols.get_ref(exported)
                    .flags
                    .contains(SymbolFlags::CONST_ENUM)
                {
                    invalidate_js_files = true;
                    break;
                }
                if type_checker.is_none() {
                    type_checker = Some(
                        program
                            .get_type_checker_for_file_exclusive(self.ctx.clone(), affected_file),
                    );
                }
                let (checker, _) = type_checker.as_ref().expect("checker");
                let aliased =
                    tsc_checker::utilities::skip_alias(&mut checker.borrow_mut(), exported);
                // PORT: Go's `checker.SkipAlias` never returns nil; `None`
                // means "no alias resolution possible" — treated like a
                // self-alias (continue).
                let Some(aliased) = aliased else {
                    continue;
                };
                if aliased == exported {
                    continue;
                }
                if program.symbols.get_ref(aliased)
                    .flags
                    .contains(SymbolFlags::CONST_ENUM)
                {
                    let declared_in_affected_file = program.symbols.get_ref(aliased)
                        .declarations
                        .iter()
                        .any(|&d| {
                            let nodes = program.arena_of(d);
                            get_source_file_of_node(Some(d), &nodes) == Some(affected_file)
                        });
                    if declared_in_affected_file {
                        invalidate_js_files = true;
                        break;
                    }
                }
            }
            if let Some((_, done)) = type_checker {
                done();
            }
        }

        // Go through files that reference affected file and handle dts emit
        // and semantic diagnostics for them and their references.
        for file_referencing_changed_file in self
            .program
            .snapshot
            .referenced_map
            .get_referenced_by(&affected_key)
        {
            if self.handle_dts_may_change_of_global_scope(
                dts_may_change,
                &file_referencing_changed_file,
                invalidate_js_files,
            ) {
                return;
            }
            // Since references of changed file = affected files - we would
            // have already handled d.ts emit and semantic diagnostics for
            // those files. Now we need to handle files referencing those
            // affected files to ensure correctness.
            for file_referencing_affected_file in self
                .program
                .snapshot
                .referenced_map
                .get_referenced_by(&file_referencing_changed_file)
            {
                if self.handle_dts_may_change_of_file_and_references(
                    dts_may_change,
                    &file_referencing_affected_file,
                    invalidate_js_files,
                ) {
                    return;
                }
            }
        }
    }

    /// `(*affectedFilesHandler) handleDtsMayChangeOfFileAndReferences`.
    fn handle_dts_may_change_of_file_and_references(
        &self,
        dts_may_change: &DtsMayChange,
        file_path: &PathKey,
        invalidate_js_files: bool,
    ) -> bool {
        let (existing, loaded) = self
            .seen_file_and_references
            .load_or_store(file_path.clone(), invalidate_js_files);
        if loaded && (existing || !invalidate_js_files) {
            return false;
        } else if loaded && invalidate_js_files {
            self.seen_file_and_references.store(file_path.clone(), true);
        }

        if self.handle_dts_may_change_of_global_scope(
            dts_may_change,
            file_path,
            invalidate_js_files,
        ) {
            return true;
        }
        self.handle_dts_may_change_of(dts_may_change, file_path, invalidate_js_files);

        // Remove the diagnostics of files that import this file and any files
        // that are referenced by it (directly or indirectly).
        for referencing_file_path in self
            .program
            .snapshot
            .referenced_map
            .get_referenced_by(file_path)
        {
            if self.handle_dts_may_change_of_file_and_references(
                dts_may_change,
                &referencing_file_path,
                invalidate_js_files,
            ) {
                return true;
            }
        }
        false
    }

    /// `(*affectedFilesHandler) handleDtsMayChangeOfGlobalScope`.
    fn handle_dts_may_change_of_global_scope(
        &self,
        dts_may_change: &DtsMayChange,
        file_path: &PathKey,
        invalidate_js_files: bool,
    ) -> bool {
        let affects_global_scope = self
            .program
            .snapshot
            .file_infos
            .load(file_path)
            .map(|info| info.borrow().affects_global_scope)
            .unwrap_or(false);
        if !affects_global_scope {
            return false;
        }
        // Every file needs to be handled.
        let files = self
            .program
            .snapshot
            .get_all_files_excluding_default_library_file(self.program.expect_program(), None)
            .clone();
        for file in files {
            self.handle_dts_may_change_of(
                dts_may_change,
                &path_key_of(self.program, file),
                invalidate_js_files,
            );
        }
        self.remove_diagnostics_of_library_files();
        true
    }

    /// `(*affectedFilesHandler) handleDtsMayChangeOf` — handle the dts may
    /// change, so they need to be added to pending emit if dts emit is
    /// enabled; also we need to make sure signature is updated for these
    /// files.
    fn handle_dts_may_change_of(
        &self,
        dts_may_change: &DtsMayChange,
        path: &PathKey,
        invalidate_js_files: bool,
    ) {
        if self.program.snapshot.changed_files_set.has(path) {
            return;
        }
        let Some(file) = self.program.expect_program().get_source_file_by_path(path) else {
            return;
        };
        self.remove_semantic_diagnostics_of(path.clone());
        // Even though the js emit doesn't change and we are already handling
        // dts emit and semantic diagnostics we need to update the signature to
        // reflect correctness of the signature (which is output d.ts emit) of
        // this file. This ensures that we don't later during incremental
        // builds consider the wrong signature. E.g. where this is also needed
        // to ensure that .tsbuildinfo generated by incremental build is the
        // same as if it was first fresh build. But we avoid expensive full
        // shape computation, as using file version as shape is enough for
        // correctness.
        self.update_shape_signature(file, true);
        // If not dts emit, nothing more to do.
        if invalidate_js_files {
            dts_may_change.add_file_to_affected_files_pending_emit(
                path.clone(),
                get_file_emit_kind(&self.program.snapshot.options),
            );
        } else if self.program.snapshot.options.get_emit_declarations() {
            dts_may_change.add_file_to_affected_files_pending_emit(
                path.clone(),
                if self.program.snapshot.options.declaration_map.is_true() {
                    FILE_EMIT_KIND_ALL_DTS
                } else {
                    FILE_EMIT_KIND_DTS
                },
            );
        }
    }

    /// `(*affectedFilesHandler) updateSnapshot`.
    fn update_snapshot(&self) {
        if self.ctx.is_cancelled() {
            return;
        }
        self.updated_signatures.range(|file_path, update| {
            if let Some(info) = self.program.snapshot.file_infos.load(&file_path) {
                let signature = update.lock().unwrap().signature.clone();
                let kind = update.lock().unwrap().kind;
                info.borrow_mut().signature = signature;
                if let Some(testing_data) = self.program.testing_data.get() {
                    testing_data
                        .updated_signature_kinds
                        .borrow_mut()
                        .insert(file_path, kind);
                }
            }
            true
        });
        self.files_to_remove_diagnostics.range(|file| {
            self.program
                .snapshot
                .semantic_diagnostics_per_file
                .delete(&file);
            true
        });
        for change in self.dts_may_change.borrow().iter() {
            for (file_path, emit_kind) in change.0.borrow().iter() {
                self.program
                    .snapshot
                    .add_file_to_affected_files_pending_emit(file_path.clone(), *emit_kind);
            }
        }
        // PORT: Go assigns a fresh `SyncSet`; `clear()` on the shared set is
        // equivalent since nothing else holds the old contents.
        self.program.snapshot.changed_files_set.clear();
        self.program
            .snapshot
            .build_info_emit_pending
            .store(true, Ordering::SeqCst);
    }
}

/// `func collectAllAffectedFiles`.
///
/// PORT: Go queues one job per changed/affected file on
/// `core.NewWorkGroup(program.SingleThreaded())`. Rust's `WorkGroup` requires
/// `Send` closures and the incremental program is `Rc`-based, so both phases
/// run sequentially on the calling thread. All ordering-sensitive state uses
/// `SyncMap`/`SyncSet` (insertion-order-independent for these reads) or is
/// accumulated into `dtsMayChange` lists processed after the barrier, matching
/// Go's post-`RunAndWait` merge.
pub(crate) fn collect_all_affected_files(ctx: &Context, program: &Program) {
    if program.snapshot.changed_files_set.size() == 0 {
        return;
    }

    let handler = AffectedFilesHandler::new(ctx.clone(), program);
    let result = SyncSet::<NodeId>::new();
    program.snapshot.changed_files_set.range(|file| {
        for affected_file in handler.get_files_affected_by(&file) {
            result.add(affected_file);
        }
        true
    });

    if ctx.is_cancelled() {
        return;
    }

    // For all the affected files, get all the files that would need to change
    // their dts or js files, update their diagnostics.
    let emit_kind = get_file_emit_kind(&program.snapshot.options);
    for file in result.to_slice() {
        // Remove the cached semantic diagnostics and handle dts emit and js
        // emit if needed.
        let dts_may_change = handler.get_dts_may_change(path_key_of(program, file), emit_kind);
        handler.handle_dts_may_change_of_affected_file(&dts_may_change, file);
    }

    // Update the snapshot with the new state.
    handler.update_snapshot();
}
