// Ported from tsc/internal/execute/incremental/program.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::{OnceCell, RefCell};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_ast::ids::NodeId;
use tsc_collections::SyncMap;
use tsc_compiler::emit_host::{EmitOnly, EmitOptions, EmitResult, WriteFileData};
use tsc_compiler::program::{
    Program as CompilerProgram, ProgramLike, filter_no_emit_semantic_diagnostics,
    handle_no_emit_options,
};
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN};
use tsc_diagnostics as diagnostics;
use tsc_outputpaths::get_build_info_file_name;
use tsc_tracing::{PHASE_EMIT, push};
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath, rooted_file_path_from_path};

use crate::incremental::affected_files_handler::collect_all_affected_files;
use crate::incremental::emit_files_handler::emit_files;
use crate::incremental::host::Host;
use crate::incremental::program_to_snapshot::program_to_snapshot;
use crate::incremental::snapshot::{DiagnosticsOrBuildInfoDiagnosticsWithFileName, Snapshot};
use crate::incremental::snapshot_to_buildinfo::snapshot_to_build_info;

/// `type SignatureUpdateKind byte`.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub enum SignatureUpdateKind {
    #[default]
    ComputedDts,
    StoredAtEmit,
    UsedVersion,
}

/// `type TestingData struct`.
///
/// PORT: `updated_signature_kinds` is behind `RefCell` because Go mutates
/// the plain map through `*Program` in handlers; the port's program is
/// `Rc`-shared.
pub struct TestingData {
    pub semantic_diagnostics_per_file:
        Rc<SyncMap<PathKey, Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>>>>,
    pub old_program_semantic_diagnostics_per_file:
        Rc<SyncMap<PathKey, Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>>>>,
    pub updated_signature_kinds: RefCell<FxHashMap<PathKey, SignatureUpdateKind>>,
}

/// `type Program struct` — incremental program wraps a
/// `compiler.Program` with a snapshot of prior state.
///
/// PORT: `program` is `Option<Rc<..>>` because Go's `*Program` is a nil-able
/// pointer — `ReadBuildInfoProgram` produces a snapshot-only program (nil
/// `program`) used as `oldProgram` for a later `NewProgram`.
pub struct Program {
    pub(crate) snapshot: Rc<Snapshot>,
    pub(crate) program: Option<Rc<CompilerProgram>>,
    pub(crate) host: Option<Arc<dyn Host>>,
    /// PORT: `OnceCell` replaces Go's nil-pointer assignment during
    /// `NewProgram` — the snapshot must exist before `TestingData` can alias
    /// its maps.
    pub(crate) testing_data: OnceCell<Rc<TestingData>>,
    nested_emit: Mutex<NestedEmitState>,
}

#[derive(Default)]
struct NestedEmitState {
    /// `func() time.Time` — injected for tests.
    now: Option<Arc<dyn Fn() -> SystemTime>>,
    depth: u32,
    start: Option<SystemTime>,
    time: Duration,
}

/// `func NewProgram`.
///
/// PORT: returns `Rc<Program>` — `performIncrementalCompilation` shares the
/// program between `EmitInput.programLike`, the testing hook and the nested
/// emit clock closure.
pub fn new_program(
    program: Rc<CompilerProgram>,
    old_program: Option<Rc<Program>>,
    host: Option<Arc<dyn Host>>,
    nested_emit_now: Arc<dyn Fn() -> SystemTime>,
    testing: bool,
) -> Rc<Program> {
    let incremental_program = Program {
        snapshot: program_to_snapshot(&program, old_program.as_deref(), testing),
        program: Some(program),
        host,
        testing_data: OnceCell::new(),
        nested_emit: Mutex::new(NestedEmitState {
            now: Some(nested_emit_now),
            ..Default::default()
        }),
    };

    if testing {
        let old_state = old_program
            .map(|p| p.snapshot.semantic_diagnostics_per_file.clone())
            .unwrap_or_default();
        let _ = incremental_program.testing_data.set(Rc::new(TestingData {
            semantic_diagnostics_per_file: incremental_program
                .snapshot
                .semantic_diagnostics_per_file
                .clone(),
            old_program_semantic_diagnostics_per_file: old_state,
            updated_signature_kinds: RefCell::new(FxHashMap::default()),
        }));
    }
    Rc::new(incremental_program)
}

impl Program {
    /// Constructor for the buildInfo-only program produced by
    /// `ReadBuildInfoProgram` — a `*Program` with a snapshot but no
    /// `*compiler.Program` or host (both nil in Go).
    pub(crate) fn from_snapshot(snapshot: Rc<Snapshot>) -> Program {
        Program {
            snapshot,
            program: None,
            host: None,
            testing_data: OnceCell::new(),
            nested_emit: Mutex::new(NestedEmitState::default()),
        }
    }

    /// `func (p *Program) GetTestingData`.
    pub fn get_testing_data(&self) -> Option<Rc<TestingData>> {
        self.testing_data.get().cloned()
    }

    /// `(*Program) beginNestedEmit` — returns a guard whose `Drop` finishes
    /// the nested-emit span (Go's `defer done()`).
    pub(crate) fn begin_nested_emit(&self) -> NestedEmitDone<'_> {
        {
            let mut state = self.nested_emit.lock().unwrap();
            if let Some(now) = state.now.as_ref() {
                if state.depth == 0 {
                    state.start = Some(now());
                }
                state.depth += 1;
            }
        }
        NestedEmitDone { program: self }
    }

    /// `(*Program) TakeNestedEmitTime`.
    pub fn take_nested_emit_time(&self) -> Duration {
        let mut state = self.nested_emit.lock().unwrap();
        std::mem::take(&mut state.time)
    }

    /// `(*Program) panicIfNoProgram`.
    fn panic_if_no_program(&self, method: &str) {
        if self.program.is_none() {
            panic!("{}: should not be called without program", method);
        }
    }

    /// `(*Program) GetProgram`.
    pub fn get_program(&self) -> &Rc<CompilerProgram> {
        self.panic_if_no_program("GetProgram");
        self.program.as_ref().expect("checked")
    }

    /// Shared `&CompilerProgram` accessor for internal callers (Go simply
    /// dereferences `p.program` in package-private code).
    pub(crate) fn expect_program(&self) -> &CompilerProgram {
        self.program.as_deref().expect("program not loaded")
    }

    /// `(*Program) Host` accessor for the incremental host.
    pub(crate) fn host(&self) -> &Arc<dyn Host> {
        self.host.as_ref().expect("incremental host not set")
    }

    /// `(*Program) HasChangedDtsFile`.
    pub fn has_changed_dts_file(&self) -> bool {
        self.snapshot.has_changed_dts_file.get()
    }

    /// `Options` — the snapshot's compiler options (Go returns
    /// `p.snapshot.options`).
    pub fn options(&self) -> &CompilerOptions {
        &self.snapshot.options
    }

    /// `GetSourceFiles` — `p.program.GetSourceFiles()`.
    pub fn get_source_files(&self) -> Vec<NodeId> {
        self.panic_if_no_program("GetSourceFiles");
        self.expect_program().source_files()
    }

    /// `(*Program) getSemanticDiagnosticsOfFile`.
    fn get_semantic_diagnostics_of_file(&self, file: NodeId) -> Vec<DiagnosticRef> {
        let path_key = {
            let program = self.expect_program();
            let nodes = program.arena_of(file);
            nodes[file].as_source_file().path_key().clone()
        };
        let cached_diagnostics = self
            .snapshot
            .semantic_diagnostics_per_file
            .load(&path_key)
            .expect("After handling all the affected files, there shouldn't be more changes");
        let mut result = filter_no_emit_semantic_diagnostics(
            cached_diagnostics
                .borrow_mut()
                .get_diagnostics(self.expect_program(), Some(file))
                .to_vec(),
            &self.snapshot.options,
        );
        result.extend(
            self.expect_program()
                .get_include_processor_diagnostics(file),
        );
        result
    }

    /// `(*Program) collectSemanticDiagnosticsOfAffectedFiles` — handle
    /// affected files and cache the semantic diagnostics for all of them or
    /// the file asked for.
    fn collect_semantic_diagnostics_of_affected_files(&self, ctx: &Context, file: Option<NodeId>) {
        if self.snapshot.can_use_incremental_state() {
            // Get all affected files.
            collect_all_affected_files(ctx, self);
            if ctx.is_cancelled() {
                return;
            }
            if self.snapshot.semantic_diagnostics_per_file.size()
                == self.expect_program().source_files_slice().len()
            {
                // If we have all the files,
                return;
            }
        }

        let mut affected_files = Vec::new();
        if let Some(file) = file {
            let path_key = {
                let program = self.expect_program();
                let nodes = program.arena_of(file);
                nodes[file].as_source_file().path_key().clone()
            };
            if self
                .snapshot
                .semantic_diagnostics_per_file
                .load(&path_key)
                .is_some()
            {
                return;
            }
            affected_files.push(file);
        } else {
            for &file in self.expect_program().source_files_slice() {
                let path_key = {
                    let program = self.expect_program();
                    let nodes = program.arena_of(file);
                    nodes[file].as_source_file().path_key().clone()
                };
                if self
                    .snapshot
                    .semantic_diagnostics_per_file
                    .load(&path_key)
                    .is_none()
                {
                    affected_files.push(file);
                }
            }
        }

        // Get their diagnostics and cache them.
        let diagnostics_per_file = self
            .expect_program()
            .get_semantic_diagnostics_for_incremental(ctx.clone(), &affected_files);
        // Commit changes if no err.
        if ctx.is_cancelled() {
            return;
        }

        // Commit changes to snapshot.
        let program = self.expect_program();
        for (file, diagnostics) in diagnostics_per_file {
            let path_key = {
                let nodes = program.arena_of(file);
                nodes[file].as_source_file().path_key().clone()
            };
            self.snapshot.semantic_diagnostics_per_file.store(
                path_key,
                Rc::new(RefCell::new(
                    DiagnosticsOrBuildInfoDiagnosticsWithFileName {
                        diagnostics: Some(diagnostics),
                        build_info_diagnostics: Vec::new(),
                    },
                )),
            );
        }
        if self.snapshot.semantic_diagnostics_per_file.size() == program.source_files_slice().len()
            && self.snapshot.check_pending.get()
            && !self.snapshot.options.no_check.is_true()
        {
            self.snapshot.check_pending.set(false);
        }
        self.snapshot
            .build_info_emit_pending
            .store(true, std::sync::atomic::Ordering::SeqCst);
    }

    /// `(*Program) emitBuildInfo`.
    pub(crate) fn emit_build_info(
        &self,
        ctx: &Context,
        options: &EmitOptions<'_>,
    ) -> Option<EmitResult> {
        let trace_done = push(
            self.expect_program().tracing().as_ref(),
            PHASE_EMIT,
            "emitBuildInfo",
            Default::default(),
            true,
        );
        let _trace_done = TraceDone(Some(trace_done));
        let build_info_file_name = get_build_info_file_name(
            &self.snapshot.options,
            self.expect_program().case_sensitivity(),
        );
        if build_info_file_name.as_string().is_empty()
            || self.expect_program().is_emit_blocked(&build_info_file_name)
        {
            return None;
        }
        if self.snapshot.has_errors.get() == TS_UNKNOWN {
            self.ensure_has_errors_for_state(ctx, self.expect_program());
            if self.snapshot.has_errors.get() != self.snapshot.has_errors_from_old_state
                || self.snapshot.has_semantic_errors.get()
                    != self.snapshot.has_semantic_errors_from_old_state
            {
                self.snapshot
                    .build_info_emit_pending
                    .store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }
        if self.snapshot.package_jsons.borrow().is_none() {
            self.ensure_package_jsons_for_state();
            if *self.snapshot.package_jsons.borrow() != self.snapshot.package_jsons_from_old_state
                || *self.snapshot.missing_package_jsons.borrow()
                    != self.snapshot.missing_package_jsons_from_old_state
            {
                self.snapshot
                    .build_info_emit_pending
                    .store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }
        if !self
            .snapshot
            .build_info_emit_pending
            .load(std::sync::atomic::Ordering::SeqCst)
        {
            return None;
        }
        if ctx.is_cancelled() {
            return None;
        }
        let build_info = match snapshot_to_build_info(
            &self.snapshot,
            self.expect_program(),
            &build_info_file_name,
        ) {
            Ok(build_info) => build_info,
            Err(err) => {
                return Some(EmitResult {
                    emit_skipped: true,
                    diagnostics: vec![
                        tsc_compiler::file_loader::content_mapper_project_diagnostic(&err),
                    ],
                    ..Default::default()
                });
            }
        };
        let text = match tsc_json::marshal(&build_info, &[]) {
            Ok(text) => String::from_utf8(text).expect("marshal produces utf-8"),
            Err(err) => panic!("Failed to marshal build info: {}", err),
        };
        let err = match &options.write_file {
            Some(write_file) => {
                // PORT: Go passes the `BuildInfo` value itself (`any`) in
                // `WriteFileData`; the Rust port serializes to
                // `serde_json::Value`.
                let mut data = WriteFileData {
                    build_info: serde_json::to_value(&build_info).ok(),
                    ..Default::default()
                };
                write_file(&build_info_file_name, &text, &mut data)
            }
            None => self
                .expect_program()
                .host()
                .fs()
                .write_file(&build_info_file_name, &text)
                .map_err(|e| e.to_string()),
        };
        if let Err(err) = err {
            return Some(EmitResult {
                emit_skipped: true,
                diagnostics: vec![new_compiler_diagnostic(
                    &diagnostics::Could_not_write_file_0_Colon_1,
                    &[build_info_file_name.as_string().to_string(), err],
                )],
                ..Default::default()
            });
        }
        self.snapshot
            .build_info_emit_pending
            .store(false, std::sync::atomic::Ordering::SeqCst);
        Some(EmitResult {
            emit_skipped: false,
            emitted_files: vec![build_info_file_name],
            ..Default::default()
        })
    }

    /// `(*Program) ensureHasErrorsForState`.
    fn ensure_has_errors_for_state(&self, ctx: &Context, program: &CompilerProgram) {
        let mut has_include_processing_diagnostics: Option<Box<dyn Fn() -> bool + '_>> = None;
        let has_emit_diagnostics;
        if self.snapshot.can_use_incremental_state() {
            let mut found_emit_diagnostics = false;
            for &file in program.source_files_slice() {
                let path_key = {
                    let nodes = program.arena_of(file);
                    nodes[file].as_source_file().path_key().clone()
                };
                if self
                    .snapshot
                    .emit_diagnostics_per_file
                    .load(&path_key)
                    .is_some()
                {
                    // Emit diagnostics will be encoded in buildInfo.
                    found_emit_diagnostics = true;
                    break;
                }
                if has_include_processing_diagnostics.is_none()
                    && !self
                        .expect_program()
                        .get_include_processor_diagnostics(file)
                        .is_empty()
                {
                    has_include_processing_diagnostics = Some(Box::new(|| true));
                }
            }
            has_emit_diagnostics = found_emit_diagnostics;
            if has_include_processing_diagnostics.is_none() {
                has_include_processing_diagnostics = Some(Box::new(|| false));
            }
        } else {
            has_emit_diagnostics = self.snapshot.has_emit_diagnostics.get();
            has_include_processing_diagnostics = Some(Box::new(|| {
                program.source_files_slice().iter().any(|&file| {
                    !self
                        .expect_program()
                        .get_include_processor_diagnostics(file)
                        .is_empty()
                })
            }));
        }

        if has_emit_diagnostics {
            // Record this for only non incremental build info.
            self.snapshot
                .has_errors
                .set(if self.snapshot.options.is_incremental() {
                    TS_FALSE
                } else {
                    TS_TRUE
                });
            // Don't need to encode semantic errors state since the emit
            // diagnostics are encoded.
            self.snapshot.has_semantic_errors.set(false);
            return;
        }

        if has_include_processing_diagnostics.expect("set above")()
            || !program.get_config_file_parsing_diagnostics().is_empty()
            || !program
                .get_syntactic_diagnostics(ctx.clone(), None)
                .is_empty()
            || !program.get_program_diagnostics().is_empty()
            || !program.get_global_diagnostics(ctx.clone()).is_empty()
        {
            self.snapshot.has_errors.set(TS_TRUE);
            // Don't need to encode semantic errors state since the syntax and
            // program diagnostics are encoded as present.
            self.snapshot.has_semantic_errors.set(false);
            return;
        }

        self.snapshot.has_errors.set(TS_FALSE);
        // Check semantic and emit diagnostics first as we don't need to ask
        // program about it.
        let program_has_semantic_or_emit = program.source_files_slice().iter().any(|&file| {
            let path_key = {
                let nodes = program.arena_of(file);
                nodes[file].as_source_file().path_key().clone()
            };
            match self.snapshot.semantic_diagnostics_per_file.load(&path_key) {
                None => {
                    // Missing semantic diagnostics in cache will be encoded
                    // in incremental buildInfo.
                    self.snapshot.options.is_incremental()
                }
                Some(semantic_diagnostics) => {
                    // Cached semantic diagnostics will be encoded in
                    // buildInfo.
                    let semantic_diagnostics = semantic_diagnostics.borrow();
                    semantic_diagnostics
                        .diagnostics
                        .as_ref()
                        .is_some_and(|diagnostics| !diagnostics.is_empty())
                        || !semantic_diagnostics.build_info_diagnostics.is_empty()
                }
            }
        });
        if program_has_semantic_or_emit {
            // Because semantic diagnostics are recorded in buildInfo, we
            // don't need to encode hasErrors in incremental buildInfo, but
            // encode as errors in non incremental buildInfo.
            self.snapshot
                .has_semantic_errors
                .set(!self.snapshot.options.is_incremental());
        }
    }

    /// `(*Program) ensurePackageJsonsForState`.
    fn ensure_package_jsons_for_state(&self) {
        let program = self.expect_program();
        let config = program.command_line().config_name().directory();
        if !config.as_string().is_empty() {
            let mut package_jsons = Vec::new();
            let mut missing_package_jsons = Vec::new();
            program.package_json_cache_entries(|_key, value| {
                let mut package_json = value.package_directory.resolve_file("package.json");
                if value.exists() || value.directory_exists {
                    package_json = rooted_file_path_from_path(
                        program.host().fs().realpath(&package_json.as_path()),
                    );
                }
                if value.exists() {
                    package_jsons.push(package_json);
                } else if package_json.contains_lowercase_directory_sequence("/node_modules/") {
                    missing_package_jsons.push(package_json);
                }
                true
            });
            *self.snapshot.package_jsons.borrow_mut() =
                Some(normalize_package_jsons(Some(package_jsons)));
            *self.snapshot.missing_package_jsons.borrow_mut() =
                Some(normalize_package_jsons(Some(missing_package_jsons)));
        }
    }

    /// `(*Program) PackageJsonLookupPaths`.
    pub fn package_json_lookup_paths(&self) -> Vec<RootedFilePath> {
        let program = self.expect_program();
        let config = program.command_line().config_name().directory();
        if config.as_string().is_empty() {
            return Vec::new();
        }

        let mut package_jsons = Vec::new();
        program.package_json_cache_entries(|_key, value| {
            let mut package_json = value.package_directory.resolve_file("package.json");
            if value.exists() || value.directory_exists {
                package_json = rooted_file_path_from_path(
                    program.host().fs().realpath(&package_json.as_path()),
                );
            }
            package_jsons.push(package_json);
            true
        });
        package_jsons.sort();
        deduplicate(package_jsons)
    }
}

/// RAII guard calling the tracing end function — Go's `defer tr.Push(...)()`.
struct TraceDone(Option<Box<dyn FnOnce()>>);

impl Drop for TraceDone {
    fn drop(&mut self) {
        if let Some(done) = self.0.take() {
            done();
        }
    }
}

/// `(*Program) beginNestedEmit`'s returned `done` func.
pub(crate) struct NestedEmitDone<'a> {
    program: &'a Program,
}

impl Drop for NestedEmitDone<'_> {
    fn drop(&mut self) {
        let mut state = self.program.nested_emit.lock().unwrap();
        if state.now.is_none() || state.depth == 0 {
            return;
        }
        state.depth -= 1;
        if state.depth == 0 {
            let start = state.start.take();
            let now = state.now.clone();
            if let (Some(now), Some(start)) = (now, start) {
                state.time += now().duration_since(start).unwrap_or_default();
            }
        }
    }
}

/// `func normalizePackageJsons`.
fn normalize_package_jsons(package_jsons: Option<Vec<RootedFilePath>>) -> Vec<RootedFilePath> {
    let mut package_jsons = package_jsons.unwrap_or_default();
    package_jsons.sort();
    deduplicate(package_jsons)
}

/// `core.Deduplicate` — assumes sorted input.
fn deduplicate<T: Eq>(items: Vec<T>) -> Vec<T> {
    let mut result = Vec::with_capacity(items.len());
    for item in items {
        if result.last() != Some(&item) {
            result.push(item);
        }
    }
    result
}

impl ProgramLike for Program {
    /// `Options implements compiler.AnyProgram interface`.
    fn options(&self) -> &CompilerOptions {
        &self.snapshot.options
    }

    /// `GetSourceFile implements compiler.AnyProgram interface`.
    fn get_source_file(&self, file_name: &RootedFilePath) -> Option<NodeId> {
        self.panic_if_no_program("GetSourceFile");
        self.expect_program().get_source_file(file_name)
    }

    /// `GetSourceFiles implements compiler.AnyProgram interface`.
    fn get_source_files(&self) -> Vec<NodeId> {
        self.panic_if_no_program("GetSourceFiles");
        self.expect_program().source_files()
    }

    /// `GetConfigFileParsingDiagnostics implements compiler.AnyProgram interface`.
    fn get_config_file_parsing_diagnostics(&self) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetConfigFileParsingDiagnostics");
        self.expect_program().get_config_file_parsing_diagnostics()
    }

    /// `GetSyntacticDiagnostics implements compiler.AnyProgram interface`.
    fn get_syntactic_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetSyntacticDiagnostics");
        self.expect_program().get_syntactic_diagnostics(ctx, file)
    }

    /// `GetBindDiagnostics implements compiler.AnyProgram interface`.
    fn get_bind_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetBindDiagnostics");
        self.expect_program().get_bind_diagnostics(ctx, file)
    }

    /// `GetProgramDiagnostics`.
    fn get_program_diagnostics(&self) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetProgramDiagnostics");
        self.expect_program().get_program_diagnostics()
    }

    /// `GetGlobalDiagnostics`.
    fn get_global_diagnostics(&self, ctx: Context) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetGlobalDiagnostics");
        self.expect_program().get_global_diagnostics(ctx)
    }

    /// `GetSemanticDiagnostics implements compiler.AnyProgram interface`.
    fn get_semantic_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetSemanticDiagnostics");
        if self.snapshot.options.no_check.is_true() {
            return Vec::new();
        }

        // Ensure all the diagnostics are cached.
        self.collect_semantic_diagnostics_of_affected_files(&ctx, file);
        if ctx.is_cancelled() {
            return Vec::new();
        }

        // Return result from cache.
        if let Some(file) = file {
            return self.get_semantic_diagnostics_of_file(file);
        }

        let mut diagnostics = Vec::new();
        for file in self.expect_program().source_files_slice() {
            diagnostics.extend(self.get_semantic_diagnostics_of_file(*file));
        }
        diagnostics
    }

    /// `GetDeclarationDiagnostics implements compiler.AnyProgram interface`.
    fn get_declaration_diagnostics(
        &self,
        ctx: Context,
        file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetDeclarationDiagnostics");
        let mut options = EmitOptions {
            target_source_files: Some(tsc_core::core::single_element_slice(file)),
            ..Default::default()
        };
        match emit_files(&ctx, self, &mut options, true) {
            Some(result) => result.diagnostics,
            None => Vec::new(),
        }
    }

    /// `GetSuggestionDiagnostics implements compiler.AnyProgram interface`.
    ///
    /// TODO: incremental suggestion diagnostics (only relevant in editor
    /// incremental builder?)
    fn get_suggestion_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        self.panic_if_no_program("GetSuggestionDiagnostics");
        self.expect_program().get_suggestion_diagnostics(ctx, file)
    }

    /// `Emit implements compiler.AnyProgram interface`.
    fn emit(&self, ctx: Context, options: &mut EmitOptions<'_>) -> EmitResult {
        self.panic_if_no_program("Emit");

        let mut result = None;
        if !options.force_emit && options.emit_only != EmitOnly::BuilderSignature {
            let emit_build_info_closure;
            let emit_build_info: Option<&dyn Fn() -> Option<EmitResult>> =
                if self.options().no_emit.is_true() {
                    emit_build_info_closure = || self.emit_build_info(&ctx, options);
                    Some(&emit_build_info_closure)
                } else {
                    None
                };
            result = handle_no_emit_options(
                &ctx,
                self,
                options.target_source_files.as_deref(),
                emit_build_info,
            );
            if ctx.is_cancelled() {
                return EmitResult::default();
            }
        }
        if let Some(mut result) = result {
            if options.target_source_files.is_some() || self.options().no_emit.is_true() {
                return result;
            }

            // Emit buildInfo and combine result.
            if let Some(mut build_info_result) = self.emit_build_info(&ctx, options) {
                result
                    .diagnostics
                    .append(&mut build_info_result.diagnostics);
                result
                    .emitted_files
                    .append(&mut build_info_result.emitted_files);
            }
            return result;
        }
        emit_files(&ctx, self, options, false).unwrap_or_default()
    }

    /// `CommonSourceDirectory implements compiler.AnyProgram interface`.
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.panic_if_no_program("CommonSourceDirectory");
        self.expect_program().common_source_directory()
    }

    /// `IsSourceFileDefaultLibrary implements compiler.AnyProgram interface`.
    fn is_source_file_default_library(&self, path: &PathKey) -> bool {
        self.panic_if_no_program("IsSourceFileDefaultLibrary");
        self.expect_program().is_source_file_default_library(path)
    }

    /// `Program implements compiler.AnyProgram interface`.
    fn program(&self) -> &CompilerProgram {
        self.panic_if_no_program("Program");
        self.expect_program()
    }
}
