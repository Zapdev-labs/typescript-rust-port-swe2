// Ported from tsc/internal/execute/incremental/emitfileshandler.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};

use tsc_ast::ids::NodeId;
use tsc_collections::{SyncMap, SyncSet};
use tsc_compiler::emit_host::{EmitOnly, EmitOptions, EmitResult, WriteFileData, WriteFileFn};
use tsc_compiler::program::combine_emit_results;
use tsc_core::context::Context;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::incremental::affected_files_handler::collect_all_affected_files;
use crate::incremental::program::{Program, SignatureUpdateKind};
use crate::incremental::snapshot::{
    DiagnosticsOrBuildInfoDiagnosticsWithFileName, EmitSignature, FILE_EMIT_KIND_ALL_DTS,
    FILE_EMIT_KIND_ALL_JS, FILE_EMIT_KIND_DTS_ERRORS, FileEmitKind, get_pending_emit_kind,
    get_text_handling_source_map_for_signature,
};

/// `type emitUpdate struct`.
struct EmitUpdate {
    pending_kind: FileEmitKind,
    result: Option<EmitResult>,
    dts_errors_from_cache: bool,
}

/// `type emitFilesHandler struct`.
pub(crate) struct EmitFilesHandler<'a> {
    ctx: Context,
    program: &'a Program,
    is_for_dts_errors: bool,
    signatures: SyncMap<PathKey, String>,
    emit_signatures: SyncMap<PathKey, Rc<EmitSignature>>,
    latest_changed_dts_files: SyncMap<PathKey, RootedFilePath>,
    deleted_pending_kinds: SyncSet<PathKey>,
    /// PORT: `RefCell` so `updateSnapshot` can take the `EmitResult` out of a
    /// shared `Rc` — Go reads through the `*emitUpdate` pointer.
    emit_updates: SyncMap<PathKey, Rc<RefCell<EmitUpdate>>>,
    has_emit_diagnostics: AtomicBool,
}

impl<'a> EmitFilesHandler<'a> {
    fn new(ctx: Context, program: &'a Program, is_for_dts_errors: bool) -> Self {
        EmitFilesHandler {
            ctx,
            program,
            is_for_dts_errors,
            signatures: SyncMap::new(),
            emit_signatures: SyncMap::new(),
            latest_changed_dts_files: SyncMap::new(),
            deleted_pending_kinds: SyncSet::new(),
            emit_updates: SyncMap::new(),
            has_emit_diagnostics: AtomicBool::new(false),
        }
    }

    /// `(*emitFilesHandler) getPendingEmitKindForEmitOptions` — determining
    /// what is pending to be emitted based on previous options or previous
    /// file emit flags.
    fn get_pending_emit_kind_for_emit_options(
        &self,
        emit_kind: FileEmitKind,
        options: &EmitOptions<'_>,
    ) -> FileEmitKind {
        let mut pending_kind = get_pending_emit_kind(emit_kind, 0);
        if options.emit_only == EmitOnly::Dts {
            pending_kind &= FILE_EMIT_KIND_ALL_DTS;
        }
        if self.is_for_dts_errors {
            pending_kind &= FILE_EMIT_KIND_DTS_ERRORS;
        }
        pending_kind
    }

    /// `(*emitFilesHandler) emitAllAffectedFiles` — emits the next affected
    /// file's emit result (EmitResult and sourceFiles emitted) or returns
    /// `None` if iteration is complete. The first of writeFile if provided,
    /// writeFile of BuilderProgramHost if provided, writeFile of compiler
    /// host — in that order — is used to write the files.
    fn emit_all_affected_files(&self, options: &mut EmitOptions<'_>) -> Option<EmitResult> {
        // Emit all affected files.
        if self.program.snapshot.can_use_incremental_state() {
            let results = self.emit_files_incremental(options);
            if self.is_for_dts_errors {
                if let Some(target_source_files) = &options.target_source_files {
                    // Result from cache.
                    let mut diagnostics = Vec::new();
                    for &target_file in target_source_files {
                        if let Some(cached) = self
                            .program
                            .snapshot
                            .emit_diagnostics_per_file
                            .load(&path_key_of(self.program, target_file))
                        {
                            diagnostics.extend_from_slice(
                                cached.borrow_mut().get_diagnostics(
                                    self.program.expect_program(),
                                    Some(target_file),
                                ),
                            );
                        }
                    }
                    let result = EmitResult {
                        emit_skipped: true,
                        diagnostics,
                        ..Default::default()
                    };
                    self.update_has_emit_diagnostics(Some(&result));
                    return Some(result);
                }
                for result in &results {
                    self.update_has_emit_diagnostics(Some(result));
                }
                return Some(combine_emit_results(results.into_iter()));
            } else {
                // Combine results and update buildInfo.
                let mut result = combine_emit_results(results.into_iter());
                self.update_has_emit_diagnostics(Some(&result));
                self.emit_build_info(options, &mut result);
                return Some(result);
            }
        } else if !self.is_for_dts_errors {
            let result = self
                .program
                .expect_program()
                .emit(self.ctx.clone(), &mut self.get_emit_options(options));
            self.update_has_emit_diagnostics(Some(&result));
            self.update_snapshot();
            let mut result = result;
            self.emit_build_info(options, &mut result);
            return Some(result);
        } else {
            let diagnostics = match &options.target_source_files {
                None => self
                    .program
                    .expect_program()
                    .get_declaration_diagnostics(self.ctx.clone(), None),
                Some(target_source_files) => target_source_files
                    .iter()
                    .flat_map(|&target_source_file| {
                        self.program
                            .expect_program()
                            .get_declaration_diagnostics(self.ctx.clone(), Some(target_source_file))
                    })
                    .collect(),
            };
            let result = EmitResult {
                emit_skipped: true,
                diagnostics,
                ..Default::default()
            };
            if !result.diagnostics.is_empty() {
                self.update_has_emit_diagnostics(Some(&result));
                self.program.snapshot.has_emit_diagnostics.set(true);
            }
            Some(result)
        }
    }

    /// `(*emitFilesHandler) updateHasEmitDiagnostics`.
    fn update_has_emit_diagnostics(&self, result: Option<&EmitResult>) {
        if result.is_some_and(|result| !result.diagnostics.is_empty()) {
            self.has_emit_diagnostics.store(true, Ordering::SeqCst);
        }
    }

    /// `(*emitFilesHandler) emitBuildInfo`.
    fn emit_build_info(&self, options: &mut EmitOptions<'_>, result: &mut EmitResult) {
        if let Some(mut build_info_result) = self.program.emit_build_info(&self.ctx, options) {
            result
                .diagnostics
                .append(&mut build_info_result.diagnostics);
            result
                .emitted_files
                .append(&mut build_info_result.emitted_files);
        }
    }

    /// `(*emitFilesHandler) emitFilesIncremental`.
    ///
    /// PORT: Go queues a job per pending file on
    /// `core.NewWorkGroup(program.SingleThreaded())`; the port runs the same
    /// work sequentially — the jobs are independent (`SyncMap` state) and the
    /// program is `Rc`-based, so `Send` work items are impossible.
    fn emit_files_incremental(&self, options: &EmitOptions<'_>) -> Vec<EmitResult> {
        // Get all affected files.
        collect_all_affected_files(&self.ctx, self.program);
        if self.ctx.is_cancelled() {
            return Vec::new();
        }

        self.program
            .snapshot
            .affected_files_pending_emit
            .range(|path, emit_kind| {
                let affected_file = self.program.expect_program().get_source_file_by_path(&path);
                if affected_file.is_none()
                    || !self
                        .program
                        .expect_program()
                        .source_file_may_be_emitted_for(affected_file.expect("checked"), false)
                {
                    self.deleted_pending_kinds.add(path);
                    return true;
                }
                let affected_file = affected_file.expect("checked");
                let pending_kind = self.get_pending_emit_kind_for_emit_options(emit_kind, options);
                if pending_kind != 0 {
                    // Determine if we can do partial emit.
                    let mut emit_only = EmitOnly::All;
                    if pending_kind & FILE_EMIT_KIND_ALL_JS != 0 {
                        emit_only = EmitOnly::Js;
                    }
                    if pending_kind & FILE_EMIT_KIND_ALL_DTS != 0 {
                        if emit_only == EmitOnly::Js {
                            emit_only = EmitOnly::All;
                        } else {
                            emit_only = EmitOnly::Dts;
                        }
                    }
                    let result = if !self.is_for_dts_errors {
                        let mut per_file_options = EmitOptions {
                            target_source_files: Some(vec![affected_file]),
                            emit_only,
                            ..Default::default()
                        };
                        // PORT: Go copies the func value; a boxed fn cannot
                        // be copied, so forward through a borrow of the
                        // caller's `write_file` (valid for the duration of
                        // this emit call).
                        per_file_options.write_file = options.write_file.as_ref().map(|wf| {
                            Box::new(
                                move |file_name: &RootedFilePath,
                                      text: &str,
                                      data: &mut WriteFileData| {
                                    wf(file_name, text, data)
                                },
                            ) as WriteFileFn<'_>
                        });
                        self.program
                            .expect_program()
                            .emit(self.ctx.clone(), &mut per_file_options)
                    } else {
                        EmitResult {
                            emit_skipped: true,
                            diagnostics: self
                                .program
                                .expect_program()
                                .get_declaration_diagnostics(self.ctx.clone(), Some(affected_file)),
                            ..Default::default()
                        }
                    };
                    self.update_has_emit_diagnostics(Some(&result));

                    // Update the pendingEmit for the file.
                    self.emit_updates.store(
                        path,
                        Rc::new(RefCell::new(EmitUpdate {
                            pending_kind: get_pending_emit_kind(emit_kind, pending_kind),
                            result: Some(result),
                            dts_errors_from_cache: false,
                        })),
                    );
                }
                true
            });
        if self.ctx.is_cancelled() {
            return Vec::new();
        }

        // Get updated errors that were not included in affected files emit.
        self.program
            .snapshot
            .emit_diagnostics_per_file
            .range(|path, diagnostics| {
                if self.emit_updates.load(&path).is_none() {
                    let affected_file =
                        self.program.expect_program().get_source_file_by_path(&path);
                    if affected_file.is_none()
                        || !self
                            .program
                            .expect_program()
                            .source_file_may_be_emitted_for(affected_file.expect("checked"), false)
                    {
                        self.deleted_pending_kinds.add(path);
                        return true;
                    }
                    let affected_file = affected_file.expect("checked");
                    let pending_kind = self
                        .program
                        .snapshot
                        .affected_files_pending_emit
                        .load(&path)
                        .unwrap_or_default();
                    self.emit_updates.store(
                        path,
                        Rc::new(RefCell::new(EmitUpdate {
                            pending_kind,
                            result: Some(EmitResult {
                                emit_skipped: true,
                                diagnostics: diagnostics
                                    .borrow_mut()
                                    .get_diagnostics(
                                        self.program.expect_program(),
                                        Some(affected_file),
                                    )
                                    .to_vec(),
                                ..Default::default()
                            }),
                            dts_errors_from_cache: true,
                        })),
                    );
                }
                true
            });

        self.update_snapshot()
    }

    /// `(*emitFilesHandler) getEmitOptions`.
    fn get_emit_options<'o>(&'o self, options: &'o EmitOptions<'o>) -> EmitOptions<'o> {
        if !self.program.snapshot.options.get_emit_declarations() {
            return EmitOptions {
                target_source_files: options.target_source_files.clone(),
                emit_only: options.emit_only,
                force_emit: options.force_emit,
                // PORT: Go copies the func value; the boxed fn is forwarded
                // through a borrow-valid closure.
                write_file: options.write_file.as_ref().map(|wf| {
                    Box::new(
                        move |file_name: &RootedFilePath, text: &str, data: &mut WriteFileData| {
                            wf(file_name, text, data)
                        },
                    ) as WriteFileFn<'o>
                }),
            };
        }
        let can_use_incremental_state = self.program.snapshot.can_use_incremental_state();
        let caller_write_file = options.write_file.as_ref();
        EmitOptions {
            target_source_files: options.target_source_files.clone(),
            emit_only: options.emit_only,
            force_emit: options.force_emit,
            write_file: Some(Box::new(
                move |file_name: &RootedFilePath, text: &str, data: &mut WriteFileData| {
                    let mut differs_only_in_map = false;
                    if file_name.is_declaration_file() {
                        if can_use_incremental_state {
                            let mut emit_signature = String::new();
                            let info = self
                                .program
                                .snapshot
                                .file_infos
                                .load(&path_key_of(
                                    self.program,
                                    data.source_file.expect("source file"),
                                ))
                                .expect("file info");
                            if info.borrow().signature == info.borrow().version {
                                let signature =
                                    self.program.snapshot.compute_signature_with_diagnostics(
                                        self.program.expect_program(),
                                        data.source_file.expect("source file"),
                                        text,
                                        data,
                                    );
                                // With d.ts diagnostics they are also part of
                                // the signature so emitSignature will be
                                // different from it since it's just a hash of
                                // d.ts.
                                if data.diagnostics.is_empty() {
                                    emit_signature = signature.clone();
                                }
                                if signature != info.borrow().version {
                                    // Update it.
                                    self.signatures.store(
                                        path_key_of(
                                            self.program,
                                            data.source_file.expect("source file"),
                                        ),
                                        signature,
                                    );
                                }
                            }

                            // Store d.ts emit hash so it can later be
                            // compared to check if d.ts has changed.
                            // Currently we do this only for composite
                            // projects since these are the only projects that
                            // can be referenced by other projects and would
                            // need their d.ts change time in --build mode.
                            if self.skip_dts_output_of_composite(
                                data.source_file.expect("source file"),
                                file_name,
                                text,
                                data,
                                &emit_signature,
                                &mut differs_only_in_map,
                            ) {
                                return Ok(());
                            }
                        }
                    }

                    let mut a_time = None;
                    if differs_only_in_map {
                        a_time = Some(self.program.host().get_mtime(file_name));
                    }
                    let err = match caller_write_file {
                        Some(write_file) => write_file(file_name, text, data),
                        None => self
                            .program
                            .expect_program()
                            .host()
                            .fs()
                            .write_file(file_name, text)
                            .map_err(|e| e.to_string()),
                    };
                    if err.is_ok() && differs_only_in_map {
                        // Revert the time to the original one.
                        return self
                            .program
                            .host()
                            .set_mtime(file_name, a_time.expect("a_time"));
                    }
                    err
                },
            )),
        }
    }

    /// `(*emitFilesHandler) skipDtsOutputOfComposite` — compare to existing
    /// computed signature and store it, or handle the changes in d.ts map
    /// option from before; returning `true` means we don't need to emit this
    /// d.ts file since its contents didn't change.
    fn skip_dts_output_of_composite(
        &self,
        file: NodeId,
        output_file_name: &RootedFilePath,
        text: &str,
        data: &mut WriteFileData,
        new_signature: &str,
        differs_only_in_map: &mut bool,
    ) -> bool {
        if !self.program.snapshot.options.composite.is_true() {
            return false;
        }
        let mut old_signature = String::new();
        let old_signature_format = self
            .program
            .snapshot
            .emit_signatures
            .load(&path_key_of(self.program, file));
        if let Some(old_signature_format) = &old_signature_format {
            if !old_signature_format.signature.is_empty() {
                old_signature = old_signature_format.signature.clone();
            } else {
                old_signature = old_signature_format
                    .signature_with_different_options
                    .as_ref()
                    .expect("signatureWithDifferentOptions")[0]
                    .clone();
            }
        }
        let new_signature = if new_signature.is_empty() {
            self.program
                .snapshot
                .compute_hash(get_text_handling_source_map_for_signature(text, data))
        } else {
            new_signature.to_string()
        };
        // Don't write dts files if they didn't change.
        if new_signature == old_signature {
            // If the signature was encoded as string the dts map options
            // match so nothing to do.
            if old_signature_format
                .as_ref()
                .is_some_and(|format| format.signature == old_signature)
            {
                data.skipped_dts_write = true;
                return true;
            } else {
                // Mark as differsOnlyInMap so that we can reverse the
                // timestamp with --build so that the downstream projects
                // don't detect this as change in d.ts file.
                *differs_only_in_map = self.program.options().build.is_true();
            }
        } else {
            self.latest_changed_dts_files
                .store(path_key_of(self.program, file), output_file_name.clone());
        }
        self.emit_signatures.store(
            path_key_of(self.program, file),
            Rc::new(EmitSignature {
                signature: new_signature,
                ..Default::default()
            }),
        );
        false
    }

    /// `(*emitFilesHandler) updateSnapshot`.
    fn update_snapshot(&self) -> Vec<EmitResult> {
        if self.program.snapshot.can_use_incremental_state() {
            self.signatures.range(|file, signature| {
                let info = self
                    .program
                    .snapshot
                    .file_infos
                    .load(&file)
                    .expect("file info");
                info.borrow_mut().signature = signature;
                if let Some(testing_data) = self.program.testing_data.get() {
                    testing_data
                        .updated_signature_kinds
                        .borrow_mut()
                        .insert(file, SignatureUpdateKind::StoredAtEmit);
                }
                self.program
                    .snapshot
                    .build_info_emit_pending
                    .store(true, Ordering::SeqCst);
                true
            });
            self.emit_signatures.range(|file, signature| {
                self.program.snapshot.emit_signatures.store(file, signature);
                self.program
                    .snapshot
                    .build_info_emit_pending
                    .store(true, Ordering::SeqCst);
                true
            });
            for file in self.deleted_pending_kinds.keys().iter() {
                self.program
                    .snapshot
                    .affected_files_pending_emit
                    .delete(file);
                self.program
                    .snapshot
                    .build_info_emit_pending
                    .store(true, Ordering::SeqCst);
            }
            // Always use the correct order when collecting the result.
            let mut results = Vec::new();
            for file in self.program.get_source_files() {
                let path_key = path_key_of(self.program, file);
                if let Some(latest_changed_dts_file) = self.latest_changed_dts_files.load(&path_key)
                {
                    *self.program.snapshot.latest_changed_dts_file.borrow_mut() =
                        latest_changed_dts_file;
                    self.program
                        .snapshot
                        .build_info_emit_pending
                        .store(true, Ordering::SeqCst);
                    self.program.snapshot.has_changed_dts_file.set(true);
                }
                if let Some(update) = self.emit_updates.load(&path_key) {
                    let mut update = update.borrow_mut();
                    if !update.dts_errors_from_cache {
                        if update.pending_kind == 0 {
                            self.program
                                .snapshot
                                .affected_files_pending_emit
                                .delete(&path_key);
                        } else {
                            self.program
                                .snapshot
                                .affected_files_pending_emit
                                .store(path_key.clone(), update.pending_kind);
                        }
                        self.program
                            .snapshot
                            .build_info_emit_pending
                            .store(true, Ordering::SeqCst);
                    }
                    if let Some(result) = update.result.take() {
                        if !result.diagnostics.is_empty() {
                            self.program.snapshot.emit_diagnostics_per_file.store(
                                path_key.clone(),
                                Rc::new(RefCell::new(
                                    DiagnosticsOrBuildInfoDiagnosticsWithFileName {
                                        diagnostics: Some(result.diagnostics.clone()),
                                        build_info_diagnostics: Vec::new(),
                                    },
                                )),
                            );
                        }
                        results.push(result);
                    }
                }
            }
            results
        } else {
            if self.has_emit_diagnostics.load(Ordering::SeqCst) {
                self.program.snapshot.has_emit_diagnostics.set(true);
            }
            Vec::new()
        }
    }
}

/// `func pathKeyOf` — shared with `affected_files_handler`.
pub(crate) fn path_key_of(program: &Program, file: NodeId) -> PathKey {
    let program = program.expect_program();
    let nodes = program.arena_of(file);
    nodes[file].as_source_file().path_key().clone()
}

/// `func emitFiles`.
pub(crate) fn emit_files(
    ctx: &Context,
    program: &Program,
    options: &mut EmitOptions<'_>,
    is_for_dts_errors: bool,
) -> Option<EmitResult> {
    let emit_handler = EmitFilesHandler::new(ctx.clone(), program, is_for_dts_errors);

    // Single file emit — do direct from program.
    if !is_for_dts_errors && options.target_source_files.is_some() {
        let result = program
            .expect_program()
            .emit(ctx.clone(), &mut emit_handler.get_emit_options(options));
        emit_handler.update_has_emit_diagnostics(Some(&result));
        if ctx.is_cancelled() {
            return None;
        }
        emit_handler.update_snapshot();
        return Some(result);
    }

    // Emit only affected files if using builder for emit.
    emit_handler.emit_all_affected_files(options)
}
