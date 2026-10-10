// Ported from tsc/internal/execute/build/buildtask.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Concurrency: Go runs `BuildTask`s on a pool of builder goroutines that
// block on each task's `done` channel (`waitOnUpstream`) and report via a
// separate reporter goroutine draining `built` channels. The port is a
// sequential work-list (the chosen shape; see the concurrency note in
// `orchestrator.rs`): `o.order`/`schedule_order` is already a topological
// order, so when a task runs all of its upstream tasks have finished —
// `waitOnUpstream` is a no-op, `close(done)`/`close(built)` are dropped, and
// reporting happens in order after the sequential pass. `task.built`/`done`
// channels are therefore not represented; `pending`, `isInitialCycle`, and
// `dirty` remain plain `bool`s, and the `*BuildInfo`/`mtime` bookkeeping that
// Go guarded with `buildInfoEntryMu`/`downStreamUpdateMu` uses `RefCell` only
// where a `&self` callback needs interior mutability.

use std::cell::RefCell;
use std::io;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use rustc_hash::FxHashSet;
use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_collections::SyncMap;
use tsc_compiler::emit_host::WriteFileData;
use tsc_compiler::file_loader::content_mapper_project_diagnostic;
use tsc_compiler::host::CompilerHost;
use tsc_compiler::program::{
    ProgramConfig, ProgramFactories, ProgramHosts, ProgramOptions, new_program,
};
use tsc_contentmapper::host::{Error as ContentMapperError, Project, ProjectSpec};
use tsc_core::core::if_else;
use tsc_core::projectreference::resolve_config_file_name_of_project_reference;
use tsc_diagnostics::Message;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::incremental::build_info::BuildInfo;
use crate::tsc::{CompileTimes, DiagnosticReporter, ExitStatus, SharedWriter, Statistics};

use super::host::BuildHost;
use super::orchestrator::{OrchestratorResult, OrchestratorState};
use super::uptodatestatus::{
    FileAndTime, InputOutputFileAndTime, InputOutputName, UpToDateStatus, UpToDateStatusData,
    UpToDateStatusKind, UpstreamErrors, ZERO_TIME, is_zero_time,
};

/// Index into `OrchestratorState::tasks` — Go's `*BuildTask` pointers.
pub(crate) type TaskId = usize;

/// `type buildKind uint`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(crate) enum BuildKind {
    /// `buildKindNone`.
    #[default]
    None,
    /// `buildKindPseudo`.
    Pseudo,
    /// `buildKindProgram`.
    Program,
}

/// `type upstreamTask struct`.
#[derive(Clone)]
pub(crate) struct UpstreamTask {
    pub task: TaskId,
    pub ref_index: usize,
}

/// `type buildInfoEntry struct`.
pub(crate) struct BuildInfoEntry {
    pub build_info: Option<Rc<BuildInfo>>,
    pub file_name: RootedFilePath,
    pub path: PathKey,
    /// Go `mTime time.Time`; [`ZERO_TIME`] is Go's zero time.
    pub m_time: SystemTime,
    /// Go `dtsTime *time.Time`.
    pub dts_time: Option<SystemTime>,
}

/// `taskResult.builder strings.Builder` — Go buffers the task's formatted
/// output and `report` flushes it to the system writer afterwards; reporters
/// need `io::Write + Send`, so the buffer is an `Arc<Mutex<String>>` they
/// clone freely.
#[derive(Clone, Default)]
pub(crate) struct TaskBuffer {
    inner: Arc<Mutex<String>>,
}

impl TaskBuffer {
    /// `builder.String()` — take the accumulated text.
    pub(crate) fn take(&self) -> String {
        std::mem::take(&mut *self.inner.lock().unwrap_or_else(|e| e.into_inner()))
    }
}

impl io::Write for TaskBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push_str(&String::from_utf8_lossy(buf));
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `type taskResult struct`.
pub(crate) struct TaskResult {
    pub builder: TaskBuffer,
    pub report_status: DiagnosticReporter,
    pub diagnostic_reporter: DiagnosticReporter,
    pub exit_status: ExitStatus,
    pub statistics: Option<Statistics>,
    /// `program *incremental.Program`.
    pub program: Option<Rc<crate::incremental::Program>>,
    pub build_kind: BuildKind,
    pub files_to_delete: Vec<RootedFilePath>,
}

impl TaskResult {
    pub(crate) fn new(
        builder: TaskBuffer,
        report_status: DiagnosticReporter,
        diagnostic_reporter: DiagnosticReporter,
    ) -> TaskResult {
        TaskResult {
            builder,
            report_status,
            diagnostic_reporter,
            exit_status: ExitStatus::Success,
            statistics: None,
            program: None,
            build_kind: BuildKind::None,
            files_to_delete: Vec::new(),
        }
    }
}

/// `type BuildTask struct`.
///
/// `done`/`built` channels and the mutexes are dropped per the concurrency
/// note above; `build_info_entry` keeps a `Rc<RefCell>` so the `WriteFile`
/// callback (a `&self`-era closure that cannot borrow the task) can populate
/// it, mirroring Go's shared `buildInfoEntry` pointer.
pub(crate) struct BuildTask {
    pub config: RootedFilePath,
    pub path: PathKey,
    pub resolved: Option<Arc<ParsedCommandLine>>,
    pub up_stream: Vec<UpstreamTask>,
    /// `downStream` — only set and used in watch mode.
    pub down_stream: Vec<TaskId>,
    pub status: Option<UpToDateStatus>,

    // task reporting
    pub result: Option<TaskResult>,

    pub build_info_entry: Rc<RefCell<Option<BuildInfoEntry>>>,
    pub package_jsons: Vec<RootedFilePath>,

    pub errors: Vec<DiagnosticRef>,
    pub pending: bool,
    pub is_initial_cycle: bool,
    pub dirty: bool,

    /// `contentMapperProjectOnce sync.Once` — `true` once the project was
    /// (attempted to be) acquired.
    pub content_mapper_project_loaded: bool,
    pub content_mapper_project: Option<Arc<dyn Project>>,
    pub content_mapper_project_err: Option<Arc<ContentMapperError>>,
}

impl BuildTask {
    pub(crate) fn new(config: RootedFilePath, path: PathKey, is_initial_cycle: bool) -> BuildTask {
        BuildTask {
            config,
            path,
            resolved: None,
            up_stream: Vec::new(),
            down_stream: Vec::new(),
            status: None,
            result: None,
            build_info_entry: Rc::new(RefCell::new(None)),
            package_jsons: Vec::new(),
            errors: Vec::new(),
            pending: true,
            is_initial_cycle,
            dirty: false,
            content_mapper_project_loaded: false,
            content_mapper_project: None,
            content_mapper_project_err: None,
        }
    }

    /// `(t *BuildTask) refreshContentMapperProject`.
    pub(crate) fn refresh_content_mapper_project(&mut self) {
        if let Some(project) = &self.content_mapper_project {
            self.content_mapper_project_err = project.refresh().err().map(Arc::new);
        }
    }

    /// `(t *BuildTask) unblockDownstream` — `close(t.done)` is a no-op in the
    /// sequential port (see the file banner).
    pub(crate) fn unblock_downstream(&mut self) {
        self.pending = false;
        self.is_initial_cycle = false;
    }

    /// `(t *BuildTask) reportDiagnostic`.
    pub(crate) fn report_diagnostic(&mut self, err: DiagnosticRef) {
        self.errors.push(err.clone());
        if let Some(result) = &self.result {
            (result.diagnostic_reporter)(&err);
        }
    }

    /// `t.result.reportStatus` — verbose/status output into the task buffer.
    pub(crate) fn report_status(&self, err: &DiagnosticRef) {
        if let Some(result) = &self.result {
            (result.report_status)(err);
        }
    }

    /// `(t *BuildTask) resetStatus`.
    pub(crate) fn reset_status(&mut self) {
        self.status = None;
        self.pending = true;
        self.errors.clear();
    }

    /// `(t *BuildTask) resetConfig` — Go also deletes the `resolvedReferences`
    /// cache entry; there is no such cache in the port (see the PORT note in
    /// `host.rs`), so only `dirty` is recorded — a fresh parse happens on the
    /// next graph generation.
    pub(crate) fn reset_config(&mut self) {
        self.dirty = true;
    }

    /// `(t *BuildTask) loadOrStoreBuildInfo`.
    pub(crate) fn load_or_store_build_info(
        &self,
        host: &Arc<BuildHost>,
        case_sensitivity: tsc_tspath::CaseSensitivity,
        build_info_file_name: RootedFilePath,
    ) -> (Option<Rc<BuildInfo>>, SystemTime) {
        let resolved = self.resolved.as_ref().expect("resolved");
        load_or_store_build_info_cell(
            &self.build_info_entry,
            host,
            resolved,
            case_sensitivity,
            build_info_file_name,
        )
    }

    /// `(t *BuildTask) onBuildInfoEmit`.
    pub(crate) fn on_build_info_emit(
        &mut self,
        case_sensitivity: tsc_tspath::CaseSensitivity,
        build_info_file_name: RootedFilePath,
        build_info: Rc<BuildInfo>,
        has_changed_dts_file: bool,
        now: SystemTime,
    ) {
        let mut entry = self.build_info_entry.borrow_mut();
        let dts_time = if has_changed_dts_file {
            Some(now)
        } else {
            entry.as_ref().and_then(|e| e.dts_time)
        };
        *entry = Some(BuildInfoEntry {
            build_info: Some(build_info),
            path: case_sensitivity.path_key(&build_info_file_name.as_path()),
            file_name: build_info_file_name,
            m_time: now,
            dts_time,
        });
    }

    /// `(t *BuildTask) hasConflictingBuildInfo`.
    pub(crate) fn has_conflicting_build_info(&self, upstream: &BuildTask) -> bool {
        let task_entry = self.build_info_entry.borrow();
        let upstream_entry = upstream.build_info_entry.borrow();
        match (task_entry.as_ref(), upstream_entry.as_ref()) {
            (Some(task_entry), Some(upstream_entry)) => task_entry.path == upstream_entry.path,
            _ => false,
        }
    }

    /// `(t *BuildTask) getLatestChangedDtsMTime`.
    pub(crate) fn get_latest_changed_dts_mtime(&self, host: &BuildHost) -> SystemTime {
        let mut entry_guard = self.build_info_entry.borrow_mut();
        let entry = entry_guard.as_mut().expect("buildInfoEntry");
        if let Some(dts_time) = entry.dts_time {
            return dts_time;
        }
        let dts_time = host.get_mtime(
            &crate::incremental::build_info::resolve_build_info_file_name(
                &entry
                    .build_info
                    .as_ref()
                    .expect("build_info")
                    .latest_changed_dts_file,
                &entry.file_name.directory(),
                host.default_library_path(),
            ),
        );
        entry.dts_time = Some(dts_time);
        dts_time
    }

    /// `(t *BuildTask) canUpdateJsDtsOutputTimestamps`.
    fn can_update_js_dts_output_timestamps(&self) -> bool {
        let options = self
            .resolved
            .as_ref()
            .expect("resolved")
            .compiler_options()
            .expect("compiler_options");
        !options.no_emit.is_true() && !options.is_incremental()
    }

    /// `(t *BuildTask) storeOutputTimeStamp` — `watch` is the command's
    /// `--watch` option.
    fn store_output_time_stamp(&self, watch: bool) -> bool {
        watch
            && !self
                .resolved
                .as_ref()
                .expect("resolved")
                .compiler_options()
                .expect("compiler_options")
                .is_incremental()
    }
}

/// The shared body of Go's `h.ReadBuildInfo` /
/// `t.loadOrStoreBuildInfo`: consult the task's entry for `path`, else read
/// the file through `incremental.NewBuildInfoReader` and populate the entry.
///
/// PORT(sibling-pending): `crate::incremental::new_build_info_reader` is the
/// natural name for Go's `NewBuildInfoReader`; `BuildInfo` is assumed
/// `Clone`able through `Rc`.
fn load_or_store_build_info_cell(
    entry_cell: &Rc<RefCell<Option<BuildInfoEntry>>>,
    host: &Arc<BuildHost>,
    resolved: &ParsedCommandLine,
    case_sensitivity: tsc_tspath::CaseSensitivity,
    build_info_file_name: RootedFilePath,
) -> (Option<Rc<BuildInfo>>, SystemTime) {
    let path = case_sensitivity.path_key(&build_info_file_name.as_path());
    {
        let entry = entry_cell.borrow();
        if let Some(entry) = entry.as_ref() {
            if entry.path == path {
                return (entry.build_info.clone(), entry.m_time);
            }
        }
    }
    let compiler_host: Arc<dyn CompilerHost> = host.clone();
    let build_info = crate::incremental::new_build_info_reader(compiler_host)
        .read_build_info(resolved)
        .map(Rc::new);
    let m_time = if build_info.is_some() {
        host.get_mtime(&build_info_file_name)
    } else {
        ZERO_TIME
    };
    *entry_cell.borrow_mut() = Some(BuildInfoEntry {
        build_info: build_info.clone(),
        file_name: build_info_file_name,
        path,
        m_time,
        dts_time: None,
    });
    (build_info, m_time)
}

/// `h.ReadBuildInfo` as a standalone `incremental::BuildInfoReader` — Go's
/// reader looks the task up by `config.ConfigName()`; `ReadBuildInfoProgram`
/// is only ever invoked with this task's own `resolved`, so the reader is
/// bound to the task's entry and resolved config directly.
pub(crate) struct TaskBuildInfoReader {
    host: Arc<BuildHost>,
    entry: Rc<RefCell<Option<BuildInfoEntry>>>,
    case_sensitivity: tsc_tspath::CaseSensitivity,
}

impl TaskBuildInfoReader {
    pub(crate) fn new(
        host: Arc<BuildHost>,
        entry: Rc<RefCell<Option<BuildInfoEntry>>>,
        case_sensitivity: tsc_tspath::CaseSensitivity,
    ) -> TaskBuildInfoReader {
        TaskBuildInfoReader {
            host,
            entry,
            case_sensitivity,
        }
    }
}

/// PORT(sibling-pending): `crate::incremental::BuildInfoReader` is assumed to
/// be `trait { fn read_build_info(&self, config: &ParsedCommandLine) ->
/// Option<BuildInfo> }`, mirroring Go.
impl crate::incremental::BuildInfoReader for TaskBuildInfoReader {
    fn read_build_info(&self, config: &ParsedCommandLine) -> Option<BuildInfo> {
        load_or_store_build_info_cell(
            &self.entry,
            &self.host,
            config,
            self.case_sensitivity,
            config.get_build_info_file_name(),
        )
        .0
        .map(|rc| (*rc).clone())
    }
}

/// `isContentMapperSupplementalBuildInfoPath`.
fn is_content_mapper_supplemental_build_info_path(input_path: &PathKey, roots: &[PathKey]) -> bool {
    for root in roots {
        let Some(suffix) = input_path
            .as_string()
            .strip_prefix(&format!("{}.", root.as_string()))
        else {
            continue;
        };
        let Some((index, extension)) = suffix.split_once('.') else {
            continue;
        };
        if extension.is_empty() {
            continue;
        }
        if index.parse::<i32>().is_ok()
            && tsc_contentmapper::contentmapper::is_supported_virtual_extension(&format!(
                ".{extension}"
            ))
        {
            return true;
        }
    }
    false
}

impl OrchestratorState {
    /// `(t *BuildTask) getContentMapperProject` — Go's `sync.Once` collapses
    /// to `content_mapper_project_loaded` in the sequential port.
    pub(crate) fn get_content_mapper_project(
        &mut self,
        task_id: TaskId,
    ) -> (Option<Arc<dyn Project>>, Option<Arc<ContentMapperError>>) {
        if !self.tasks[task_id].content_mapper_project_loaded {
            self.tasks[task_id].content_mapper_project_loaded = true;
            let resolved = self.tasks[task_id].resolved.clone();
            if let (Some(mapper_host), Some(resolved)) =
                (self.content_mapper_host.clone(), resolved)
            {
                if !resolved.content_mappers().is_empty() {
                    self.tasks[task_id].content_mapper_project =
                        mapper_host.project(&ProjectSpec {
                            config_file_name: resolved.config_name().clone(),
                            mappers: resolved.content_mappers().to_vec(),
                            compiler_options: resolved.compiler_options().cloned().map(Arc::new),
                        });
                }
            }
        }
        (
            self.tasks[task_id].content_mapper_project.clone(),
            self.tasks[task_id].content_mapper_project_err.clone(),
        )
    }

    /// `(t *BuildTask) report`.
    pub(crate) fn task_report(&mut self, task_id: TaskId, build_result: &mut OrchestratorResult) {
        if !self.tasks[task_id].errors.is_empty() {
            build_result
                .errors
                .extend(self.tasks[task_id].errors.iter().cloned());
        }
        let task_result = self.tasks[task_id].result.take().expect("task result");
        self.opts
            .sys
            .writer()
            .write_text(&task_result.builder.take());
        if task_result.exit_status as i32 > build_result.result.status as i32 {
            build_result.result.status = task_result.exit_status;
        }
        if let Some(statistics) = &task_result.statistics {
            build_result.statistics.aggregate(statistics);
        }
        // If we built the program, or updated timestamps, or had errors, we
        // need to delete files that are no longer needed.
        match task_result.build_kind {
            BuildKind::Program => {
                if let Some(testing) = &self.opts.testing {
                    testing.on_program(task_result.program.as_deref().expect("program"));
                }
                build_result.statistics.projects_built += 1;
            }
            BuildKind::Pseudo => {
                build_result.statistics.timestamp_updates += 1;
            }
            BuildKind::None => {}
        }
        build_result
            .files_to_delete
            .extend(task_result.files_to_delete);
    }

    /// `(t *BuildTask) buildProject` — `waitOnUpstream` is a no-op in the
    /// sequential port (see the file banner).
    pub(crate) fn build_project(&mut self, task_id: TaskId) {
        if self.tasks[task_id].pending {
            let status = self.get_up_to_date_status(task_id);
            self.tasks[task_id].status = Some(status);
            self.report_up_to_date_status(task_id);
            if !self.handle_status_that_doesnt_require_build(task_id) {
                self.compile_and_emit(task_id);
                self.update_downstream(task_id);
            } else {
                if let Some(resolved) = self.tasks[task_id].resolved.clone() {
                    for diagnostic in resolved.get_config_file_parsing_diagnostics() {
                        self.tasks[task_id].report_diagnostic(diagnostic);
                    }
                }
                if !self.tasks[task_id].errors.is_empty() {
                    if let Some(result) = &mut self.tasks[task_id].result {
                        result.exit_status = ExitStatus::DiagnosticsPresentOutputsSkipped;
                    }
                }
            }
        } else if !self.tasks[task_id].errors.is_empty() {
            self.report_up_to_date_status(task_id);
            let reporter = self.tasks[task_id]
                .result
                .as_ref()
                .map(|result| result.diagnostic_reporter.clone());
            if let Some(reporter) = reporter {
                // Should not add the diagnostics so just reporting.
                for err in self.tasks[task_id].errors.clone() {
                    reporter(&err);
                }
            }
        }
        self.tasks[task_id].unblock_downstream();
    }

    /// `(t *BuildTask) updateDownstream` — `downStreamUpdateMu` is dropped in
    /// the sequential port.
    fn update_downstream(&mut self, task_id: TaskId) {
        if self.tasks[task_id].is_initial_cycle {
            return;
        }
        if self.build_options().stop_build_on_errors.is_true()
            && self.tasks[task_id]
                .status
                .as_ref()
                .is_some_and(|status| status.is_error())
        {
            return;
        }
        let program = self.tasks[task_id]
            .result
            .as_ref()
            .and_then(|result| result.program.clone());
        let Some(program) = program else {
            for &down_stream in &self.tasks[task_id].down_stream.clone() {
                self.tasks[down_stream].reset_status();
            }
            return;
        };

        let config = self.tasks[task_id].config.clone();
        let changed_dts = program.has_changed_dts_file();
        for down_stream_id in self.tasks[task_id].down_stream.clone() {
            if let Some(status) = self.tasks[down_stream_id].status.clone() {
                match status.kind {
                    UpToDateStatusKind::UpToDate if !changed_dts => {
                        self.tasks[down_stream_id].status = Some(UpToDateStatus::with_data(
                            UpToDateStatusKind::UpToDateWithUpstreamTypes,
                            status.data,
                        ));
                    }
                    UpToDateStatusKind::UpToDate
                    | UpToDateStatusKind::UpToDateWithUpstreamTypes
                    | UpToDateStatusKind::UpToDateWithInputFileText => {
                        if changed_dts {
                            self.tasks[down_stream_id].status = Some(UpToDateStatus::with_data(
                                UpToDateStatusKind::InputFileNewer,
                                UpToDateStatusData::InputOutputName(InputOutputName {
                                    input: config.as_path(),
                                    output: status.oldest_output_file_name(),
                                }),
                            ));
                        }
                    }
                    UpToDateStatusKind::UpstreamErrors => {
                        let upstream_errors = status.upstream_errors();
                        let ref_config =
                            resolve_config_file_name_of_project_reference(&upstream_errors.r#ref);
                        if self.case_sensitivity.path_key(&ref_config.as_path())
                            == self.tasks[task_id].path
                        {
                            self.tasks[down_stream_id].reset_status();
                            continue;
                        }
                    }
                    _ => {}
                }
            }
            self.tasks[down_stream_id].pending = true;
        }
    }

    /// `(t *BuildTask) compileAndEmit`.
    fn compile_and_emit(&mut self, task_id: TaskId) {
        self.tasks[task_id].errors.clear();
        if self.build_options().verbose.is_true() {
            let rel_config = self.relative_file_name(&self.tasks[task_id].config);
            let diagnostic =
                new_compiler_diagnostic(&tsc_diagnostics::Building_project_0, &[rel_config]);
            self.tasks[task_id].report_status(&diagnostic);
        }

        // Real build.
        let compile_times = Rc::new(RefCell::new(CompileTimes::default()));
        compile_times.borrow_mut().config_time = self.host.config_time(&self.tasks[task_id].path);
        let build_info_read_start = self.opts.sys.now();
        let (content_mapper_project, content_mapper_project_err) =
            self.get_content_mapper_project(task_id);
        if let Some(err) = content_mapper_project_err {
            let diagnostic = content_mapper_project_diagnostic(err.as_ref());
            self.tasks[task_id].report_diagnostic(diagnostic);
            self.tasks[task_id].status = Some(UpToDateStatus::new(UpToDateStatusKind::BuildErrors));
            if let Some(result) = &mut self.tasks[task_id].result {
                result.exit_status = ExitStatus::DiagnosticsPresentOutputsSkipped;
            }
            return;
        }
        let task_buffer = self.tasks[task_id]
            .result
            .as_ref()
            .expect("task result")
            .builder
            .clone();
        let compiler_host: Arc<dyn CompilerHost> =
            Arc::new(super::compiler_host::BuildCompilerHost::new(
                self.host.clone(),
                crate::tsc::get_trace_with_writer_from_sys(
                    SharedWriter::new(task_buffer.clone()),
                    self.command_locale(),
                    self.opts.testing.as_ref(),
                ),
                content_mapper_project,
            ));
        let resolved = self.tasks[task_id].resolved.clone().expect("resolved");
        let mut old_program = None;
        if !self.build_options().force.is_true() {
            let reader: Arc<dyn crate::incremental::BuildInfoReader> =
                Arc::new(TaskBuildInfoReader::new(
                    self.host.clone(),
                    self.tasks[task_id].build_info_entry.clone(),
                    self.case_sensitivity,
                ));
            old_program =
                crate::incremental::read_build_info_program(&resolved, reader, &compiler_host);
        }
        compile_times.borrow_mut().build_info_read_time = self
            .opts
            .sys
            .now()
            .duration_since(build_info_read_start)
            .unwrap_or_default();
        let parse_start = self.opts.sys.now();
        let program = new_program(ProgramOptions {
            config: Rc::new(ProgramConfig {
                config: resolved.clone(),
                use_source_of_project_reference: false,
                single_threaded: tsc_core::tristate::Tristate::default(),
                typings_location: tsc_tspath::RootedDirectoryPath::default(),
                project_name: String::new(),
                skip_module_resolution: false,
            }),
            hosts: ProgramHosts {
                host: compiler_host.clone(),
                tracing: None,
            },
            factories: ProgramFactories::default(),
        });
        compile_times.borrow_mut().parse_time = self
            .opts
            .sys
            .now()
            .duration_since(parse_start)
            .unwrap_or_default();
        let changes_compute_start = self.opts.sys.now();
        let incremental_host: Arc<dyn crate::incremental::Host> = self.host.clone();
        let nested_emit_now = {
            let sys = self.opts.sys.clone();
            move || sys.now()
        };
        let incremental_program = crate::incremental::new_program(
            program.clone(),
            old_program,
            Some(incremental_host),
            Arc::new(nested_emit_now),
            self.opts.testing.is_some(),
        );
        if let Some(result) = &mut self.tasks[task_id].result {
            result.program = Some(incremental_program.clone());
        }
        compile_times.borrow_mut().changes_compute_time = self
            .opts
            .sys
            .now()
            .duration_since(changes_compute_start)
            .unwrap_or_default();

        // `t.reportDiagnostic` as a `DiagnosticReporter` — it must be
        // `Send + Sync`, so the task-errors append goes through a shared
        // collection drained into `task.errors` after the emit.
        let emitted_diagnostics: Arc<Mutex<Vec<DiagnosticRef>>> = Arc::new(Mutex::new(Vec::new()));
        let report_diagnostic: DiagnosticReporter = {
            let emitted_diagnostics = emitted_diagnostics.clone();
            let task_reporter = self.tasks[task_id]
                .result
                .as_ref()
                .expect("task result")
                .diagnostic_reporter
                .clone();
            Arc::new(move |diagnostic: &DiagnosticRef| {
                emitted_diagnostics
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(diagnostic.clone());
                (task_reporter)(diagnostic);
            })
        };

        // `t.writeFile` — `has_changed_dts_file` is fixed for the emit, so it
        // is read once up front; build-info emits are queued and applied by
        // `on_build_info_emit` afterwards (Go mutates the task's entry from
        // inside the callback; the queued form is equivalent because nothing
        // reads the entry during the emit).
        let has_changed_dts_file = incremental_program.has_changed_dts_file();
        let emitted_build_infos: Rc<RefCell<Vec<(RootedFilePath, BuildInfo)>>> =
            Rc::new(RefCell::new(Vec::new()));
        let write_file = {
            let fs = self.host.fs().clone();
            let host = self.host.clone();
            let sys = self.opts.sys.clone();
            let emitted_build_infos = emitted_build_infos.clone();
            let store_output_time_stamps = self.tasks[task_id]
                .store_output_time_stamp(self.command_compiler_options().watch.is_true());
            Box::new(
                move |file_name: &RootedFilePath, text: &str, data: &mut WriteFileData| {
                    match fs.write_file(file_name, text) {
                        Ok(()) => {
                            if let Some(build_info_json) = data.build_info.take() {
                                // PORT(sibling-pending): Go stores
                                // `*incremental.BuildInfo` in
                                // `WriteFileData.build_info`; the Rust
                                // `serde_json::Value` slot round-trips through
                                // `Deserialize`.
                                let build_info: BuildInfo = serde_json::from_value(build_info_json)
                                    .expect(
                                        "WriteFileData.build_info must be a serialized \
                                         incremental::BuildInfo",
                                    );
                                emitted_build_infos
                                    .borrow_mut()
                                    .push((file_name.clone(), build_info));
                            } else if store_output_time_stamps {
                                // Store time stamps.
                                host.store_mtime(file_name, sys.now());
                            }
                            Ok(())
                        }
                        Err(err) => Err(err.to_string()),
                    }
                },
            )
        };

        // Scope `emit_input` so that its drop (and the `&self.opts` borrows it
        // holds) ends before the `&mut self` bookkeeping calls below.
        let (result, statistics) = {
            let m_times = self.host.m_times();
            let mut emit_input = crate::tsc::EmitInput {
                sys: &self.opts.sys,
                program_like: &*incremental_program,
                program: &program,
                config: resolved.as_ref(),
                report_diagnostic,
                report_error_summary: crate::tsc::quiet_diagnostics_reporter_fn(),
                writer: SharedWriter::new(task_buffer),
                write_file: Some(write_file),
                compile_times: compile_times.clone(),
                testing: self.opts.testing.as_ref(),
                testing_mtimes_cache: Some(&m_times),
                tracing: None,
                take_nested_emit_time: Some(Box::new({
                    let incremental_program = incremental_program.clone();
                    move || incremental_program.take_nested_emit_time()
                })),
            };
            crate::tsc::emit_and_report_statistics(&mut emit_input)
        };
        let task_result = self.tasks[task_id].result.as_mut().expect("task result");
        task_result.exit_status = result.status;
        task_result.statistics = statistics;
        self.tasks[task_id]
            .errors
            .extend(emitted_diagnostics.lock().unwrap().drain(..));
        for (file_name, build_info) in emitted_build_infos.borrow_mut().drain(..) {
            self.tasks[task_id].on_build_info_emit(
                self.case_sensitivity,
                file_name,
                Rc::new(build_info),
                has_changed_dts_file,
                self.opts.sys.now(),
            );
        }
        self.tasks[task_id].package_jsons = incremental_program.package_json_lookup_paths();
        if (!program.options().no_emit_on_error.is_true() || result.diagnostics.is_empty())
            && (!result.emit_result.emitted_files.is_empty()
                || self.tasks[task_id].status.as_ref().map(|s| s.kind)
                    != Some(UpToDateStatusKind::OutOfDateBuildInfoWithErrors))
        {
            // Update time stamps for rest of the outputs.
            self.update_task_time_stamps(
                task_id,
                &result.emit_result.emitted_files,
                &tsc_diagnostics::Updating_unchanged_output_timestamps_of_project_0,
            );
        }
        self.tasks[task_id]
            .result
            .as_mut()
            .expect("task result")
            .build_kind = BuildKind::Program;
        if result.status == ExitStatus::DiagnosticsPresentOutputsSkipped
            || result.status == ExitStatus::DiagnosticsPresentOutputsGenerated
        {
            self.tasks[task_id].status = Some(UpToDateStatus::new(UpToDateStatusKind::BuildErrors));
        } else {
            let oldest_output_file_name =
                if let Some(emitted) = result.emit_result.emitted_files.first() {
                    emitted.clone()
                } else {
                    resolved
                        .get_output_file_names()
                        .into_iter()
                        .next()
                        .unwrap_or_default()
                };
            self.tasks[task_id].status = Some(UpToDateStatus::with_data(
                UpToDateStatusKind::UpToDate,
                UpToDateStatusData::FilePath(oldest_output_file_name),
            ));
        }
    }

    /// `(t *BuildTask) handleStatusThatDoesntRequireBuild`.
    fn handle_status_that_doesnt_require_build(&mut self, task_id: TaskId) -> bool {
        let status = self.tasks[task_id].status.clone().expect("upToDateStatus");
        match status.kind {
            UpToDateStatusKind::UpToDate => {
                if self.build_options().dry.is_true() {
                    let diagnostic = new_compiler_diagnostic(
                        &tsc_diagnostics::Project_0_is_up_to_date,
                        &[self.tasks[task_id].config.as_string().to_string()],
                    );
                    self.tasks[task_id].report_status(&diagnostic);
                }
                return true;
            }
            UpToDateStatusKind::UpstreamErrors => {
                let upstream_status = status.upstream_errors();
                if self.build_options().verbose.is_true() {
                    let rel_config = self.relative_file_name(&self.tasks[task_id].config);
                    let rel_ref = self.relative_path(&upstream_status.r#ref);
                    let diagnostic = new_compiler_diagnostic(
                        if_else(
                            upstream_status.ref_has_upstream_errors,
                            &tsc_diagnostics::Skipping_build_of_project_0_because_its_dependency_1_was_not_built,
                            &tsc_diagnostics::Skipping_build_of_project_0_because_its_dependency_1_has_errors,
                        ),
                        &[rel_config, rel_ref],
                    );
                    self.tasks[task_id].report_status(&diagnostic);
                }
                return true;
            }
            UpToDateStatusKind::Solution => return true,
            UpToDateStatusKind::ConfigFileNotFound => {
                let diagnostic = new_compiler_diagnostic(
                    &tsc_diagnostics::File_0_not_found,
                    &[self.tasks[task_id].config.as_string().to_string()],
                );
                self.tasks[task_id].report_diagnostic(diagnostic);
                return true;
            }
            _ => {}
        }

        // Update timestamps.
        if status.is_pseudo_build() {
            if self.build_options().dry.is_true() {
                let diagnostic = new_compiler_diagnostic(
                    &tsc_diagnostics::A_non_dry_build_would_update_timestamps_for_output_of_project_0,
                    &[self.tasks[task_id].config.as_string().to_string()],
                );
                self.tasks[task_id].report_status(&diagnostic);
                self.tasks[task_id].status =
                    Some(UpToDateStatus::new(UpToDateStatusKind::UpToDate));
                return true;
            }

            self.update_task_time_stamps(
                task_id,
                &[],
                &tsc_diagnostics::Updating_output_timestamps_of_project_0,
            );
            self.tasks[task_id].status = Some(UpToDateStatus::with_data(
                UpToDateStatusKind::UpToDate,
                status.data,
            ));
            self.tasks[task_id]
                .result
                .as_mut()
                .expect("task result")
                .build_kind = BuildKind::Pseudo;
            return true;
        }

        if self.build_options().dry.is_true() {
            let diagnostic = new_compiler_diagnostic(
                &tsc_diagnostics::A_non_dry_build_would_build_project_0,
                &[self.tasks[task_id].config.as_string().to_string()],
            );
            self.tasks[task_id].report_status(&diagnostic);
            self.tasks[task_id].status = Some(UpToDateStatus::new(UpToDateStatusKind::UpToDate));
            return true;
        }
        false
    }

    /// `(t *BuildTask) getUpToDateStatus`.
    pub(crate) fn get_up_to_date_status(&mut self, task_id: TaskId) -> UpToDateStatus {
        if let Some(status) = &self.tasks[task_id].status {
            return status.clone();
        }
        // Config file not found.
        let Some(resolved) = self.tasks[task_id].resolved.clone() else {
            return UpToDateStatus::new(UpToDateStatusKind::ConfigFileNotFound);
        };

        // Solution - nothing to build.
        //
        // PORT: Go checks `ProjectReferences() != nil` (nil-vs-empty slice);
        // Rust's `project_references` is a `Vec`, so an explicit empty
        // `"references": []` is approximated as absent.
        if resolved.file_names().is_empty() && !resolved.project_references().is_empty() {
            return UpToDateStatus::new(UpToDateStatusKind::Solution);
        }

        let up_streams = self.tasks[task_id].up_stream.clone();
        for upstream in &up_streams {
            let upstream_status = self.tasks[upstream.task]
                .status
                .as_ref()
                .expect("upstream task status");
            if self.build_options().stop_build_on_errors.is_true() && upstream_status.is_error() {
                // Upstream project has errors, so we cannot build this
                // project.
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::UpstreamErrors,
                    UpToDateStatusData::UpstreamErrors(UpstreamErrors {
                        r#ref: resolved.project_references()[upstream.ref_index]
                            .path
                            .clone(),
                        ref_has_upstream_errors: upstream_status.kind
                            == UpToDateStatusKind::UpstreamErrors,
                    }),
                );
            }
        }

        if self.build_options().force.is_true() {
            return UpToDateStatus::new(UpToDateStatusKind::ForceBuild);
        }

        // Check the build info.
        let build_info_path = resolved.get_build_info_file_name();
        let (build_info, build_info_time) = self.tasks[task_id].load_or_store_build_info(
            &self.host,
            self.case_sensitivity,
            build_info_path.clone(),
        );
        let Some(build_info) = build_info else {
            return UpToDateStatus::with_data(
                UpToDateStatusKind::OutputMissing,
                UpToDateStatusData::FilePath(build_info_path),
            );
        };

        // Build info version.
        if !build_info.is_valid_version() {
            return UpToDateStatus::with_data(
                UpToDateStatusKind::TsVersionOutputOfDate,
                UpToDateStatusData::Version(build_info.version.clone()),
            );
        }

        // If a configured content mapper's identity has changed, files it
        // produced may be stale.
        let (content_mapper_project, content_mapper_project_err) =
            self.get_content_mapper_project(task_id);
        let (content_mapper_identities, identity_failed) =
            match crate::incremental::build_info::content_mapper_identities(
                content_mapper_project.as_ref(),
            ) {
                Ok(identities) => (identities, false),
                Err(err) => {
                    self.tasks[task_id].content_mapper_project_err = Some(Arc::new(err));
                    (Vec::new(), true)
                }
            };
        if content_mapper_project_err.is_some()
            || identity_failed
            || !build_info.content_mapper_identities_match(&content_mapper_identities)
        {
            return UpToDateStatus::with_data(
                UpToDateStatusKind::OutOfDateOptions,
                UpToDateStatusData::FilePath(build_info_path),
            );
        }

        let options = resolved.compiler_options().expect("compiler_options");

        // Report errors if build info indicates errors.
        if build_info.errors // Errors that need to be reported irrespective of "--noCheck"
            || (!options.no_check.is_true()
                && (build_info.semantic_errors || build_info.check_pending))
        // Errors without --noCheck
        {
            return UpToDateStatus::with_data(
                UpToDateStatusKind::OutOfDateBuildInfoWithErrors,
                UpToDateStatusData::FilePath(build_info_path),
            );
        }

        let get_build_info_directory = || build_info_path.directory();
        if options.is_incremental() {
            if !build_info.is_incremental() {
                // Program options out of date.
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::OutOfDateOptions,
                    UpToDateStatusData::FilePath(build_info_path),
                );
            }

            // Errors need to be reported if build info has errors — Go's
            // `!= nil` slice checks become `!is_empty()` (nil-vs-empty is
            // not observable on a deserialized build info).
            if (options.get_emit_declarations()
                && !build_info.emit_diagnostics_per_file.is_empty())
                // Always reported errors
                || (!options.no_check.is_true() // Semantic errors if not --noCheck
                    && (!build_info.change_file_set.is_empty()
                        || !build_info.semantic_diagnostics_per_file.is_empty()))
            {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::OutOfDateBuildInfoWithErrors,
                    UpToDateStatusData::FilePath(build_info_path),
                );
            }

            // Pending emit files.
            if !options.no_emit.is_true()
                && (!build_info.change_file_set.is_empty()
                    || !build_info.affected_files_pending_emit.is_empty())
            {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::OutOfDateBuildInfoWithPendingEmit,
                    UpToDateStatusData::FilePath(build_info_path),
                );
            }

            // Some of the emit files like source map or dts etc are not yet
            // done.
            if build_info.is_emit_pending(&resolved, &get_build_info_directory()) {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::OutOfDateOptions,
                    UpToDateStatusData::FilePath(build_info_path),
                );
            }
        }
        let mut input_text_unchanged = false;
        let mut oldest_output_file_and_time = FileAndTime {
            file: build_info_path.clone(),
            time: build_info_time,
        };
        let mut newest_input_file_and_time = FileAndTime {
            file: RootedFilePath::default(),
            time: ZERO_TIME,
        };
        let mut seen_roots: FxHashSet<PathKey> = FxHashSet::default();
        let case_sensitivity = self.case_sensitivity;
        let mut root_info_reader = None;
        macro_rules! root_info_reader {
            () => {
                root_info_reader.get_or_insert_with(|| {
                    build_info.get_build_info_root_info_reader(
                        &get_build_info_directory(),
                        case_sensitivity,
                    )
                })
            };
        }
        for input_file in resolved.file_names() {
            let input_time = self.host.get_mtime(input_file);
            if is_zero_time(input_time) {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::InputFileMissing,
                    UpToDateStatusData::FilePath(input_file.clone()),
                );
            }
            let input_path = case_sensitivity.path_key(&input_file.as_path());
            if input_time > oldest_output_file_and_time.time {
                let mut version = String::new();
                let mut current_version = String::new();
                if build_info.is_incremental() {
                    let (build_info_file_info, resolved_input_path) =
                        root_info_reader!().get_build_info_file_info(&input_path);
                    // `GetFileInfo` always returns a `FileInfo` (empty for a
                    // missing entry) — Go's `!= nil && != ""` collapses to
                    // checking the version text.
                    if let Some(file_info) = build_info_file_info {
                        let file_info = file_info.get_file_info();
                        if !file_info.version().is_empty() {
                            version = file_info.version().to_string();
                            let text =
                                resolved_input_path.and_then(|path| self.host.fs().read_file(path));
                            if let Some(text) = text {
                                current_version = crate::incremental::compute_hash(
                                    &text,
                                    self.opts.testing.is_some(),
                                );
                                if version == current_version {
                                    input_text_unchanged = true;
                                }
                            }
                        }
                    }
                }

                if version.is_empty() || version != current_version {
                    return UpToDateStatus::with_data(
                        UpToDateStatusKind::InputFileNewer,
                        UpToDateStatusData::InputOutputName(InputOutputName {
                            input: input_file.as_path(),
                            output: build_info_path.clone(),
                        }),
                    );
                }
            }
            if input_time > newest_input_file_and_time.time {
                newest_input_file_and_time = FileAndTime {
                    file: input_file.clone(),
                    time: input_time,
                };
            }
            seen_roots.insert(input_path);
        }

        let roots: Vec<PathKey> = root_info_reader!().roots().cloned().collect();
        for root in &roots {
            if !seen_roots.contains(root) {
                // File was root file when project was built but its not any
                // more.
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::OutOfDateRoots,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: root_info_reader!().root_file_name(root).as_path(),
                        output: build_info_path.clone(),
                    }),
                );
            }
        }

        if build_info.is_incremental() {
            let mut resolved_roots: FxHashSet<PathKey> = FxHashSet::default();
            for root in &roots {
                let (_, resolved) = root_info_reader!().get_build_info_file_info(root);
                if let Some(resolved) = resolved {
                    if !resolved.as_string().is_empty() {
                        resolved_roots.insert(case_sensitivity.path_key(&resolved.as_path()));
                    }
                }
            }
            for (index, build_info_file_info) in build_info.file_infos.iter().enumerate() {
                let build_info_file_name = &build_info.file_names[index];
                // Lib files bundled with the compiler can change only with
                // the version of the compiler, which is already verified with
                // buildInfo.version.
                if crate::incremental::build_info::is_build_info_file_name_default_library(
                    build_info_file_name,
                ) {
                    continue;
                }
                let input_file_name = crate::incremental::build_info::resolve_build_info_file_name(
                    build_info_file_name,
                    &get_build_info_directory(),
                    self.host.default_library_path(),
                );
                let input_path = case_sensitivity.path_key(&input_file_name.as_path());
                // Root files are already checked.
                if seen_roots.contains(&input_path) || resolved_roots.contains(&input_path) {
                    continue;
                }
                if is_content_mapper_supplemental_build_info_path(&input_path, &roots)
                    && !self.host.fs().file_exists(&input_file_name)
                {
                    continue;
                }
                let input_time = self.host.get_mtime(&input_file_name);
                if is_zero_time(input_time) {
                    // Input file that was part of the program is missing (eg:
                    // dependency was removed).
                    return UpToDateStatus::with_data(
                        UpToDateStatusKind::InputFileMissing,
                        UpToDateStatusData::FilePath(input_file_name),
                    );
                }

                if input_time > oldest_output_file_and_time.time {
                    let version = build_info_file_info
                        .as_ref()
                        .map(|info| info.get_file_info().version().to_string())
                        .unwrap_or_default();
                    let mut current_version = String::new();
                    if !version.is_empty() {
                        if let Some(text) = self.host.fs().read_file(&input_file_name) {
                            current_version = crate::incremental::compute_hash(
                                &text,
                                self.opts.testing.is_some(),
                            );
                        }
                    }
                    if version.is_empty() || version != current_version {
                        return UpToDateStatus::with_data(
                            UpToDateStatusKind::InputFileNewer,
                            UpToDateStatusData::InputOutputName(InputOutputName {
                                input: input_file_name.as_path(),
                                output: build_info_path.clone(),
                            }),
                        );
                    }
                    input_text_unchanged = true;
                }
            }
        }

        if !options.is_incremental() {
            // Check output file stamps.
            for output_file in resolved.get_output_file_names() {
                let output_time = self.host.get_mtime(&output_file);
                if is_zero_time(output_time) {
                    // Output file missing.
                    return UpToDateStatus::with_data(
                        UpToDateStatusKind::OutputMissing,
                        UpToDateStatusData::FilePath(output_file),
                    );
                }

                if output_time < newest_input_file_and_time.time {
                    // Output file is older than input file.
                    return UpToDateStatus::with_data(
                        UpToDateStatusKind::InputFileNewer,
                        UpToDateStatusData::InputOutputName(InputOutputName {
                            input: newest_input_file_and_time.file.as_path(),
                            output: output_file,
                        }),
                    );
                }

                if output_time < oldest_output_file_and_time.time {
                    oldest_output_file_and_time = FileAndTime {
                        file: output_file,
                        time: output_time,
                    };
                }
            }
        }

        let mut ref_dts_unchanged = false;
        for upstream in &up_streams {
            let upstream_status = self.tasks[upstream.task]
                .status
                .as_ref()
                .expect("upstream task status");
            if upstream_status.kind == UpToDateStatusKind::Solution {
                // Not dependent on the status or this upstream project
                // (eg: expected cycle was detected and hence skipped, or is
                // solution).
                continue;
            }

            // If the upstream project's newest file is older than our oldest
            // output, we can't be out of date because of it. `input.time`
            // will not be present if we just built this project or updated
            // timestamps - in that case we do want to either build or update
            // timestamps.
            if let Some(ref_input_output) = upstream_status.input_output_file_and_time() {
                if !is_zero_time(ref_input_output.input.time)
                    && ref_input_output.input.time < oldest_output_file_and_time.time
                {
                    continue;
                }
            }

            // Check if tsbuildinfo path is shared, then we need to rebuild.
            let out_of_date_input = || InputOutputName {
                input: resolved.project_references()[upstream.ref_index]
                    .path
                    .clone(),
                output: oldest_output_file_and_time.file.clone(),
            };
            if self.tasks[task_id].has_conflicting_build_info(&self.tasks[upstream.task]) {
                // We have an output older than an upstream output - we are
                // out of date.
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::InputFileNewer,
                    UpToDateStatusData::InputOutputName(out_of_date_input()),
                );
            }

            // If the upstream project has only change .d.ts files, and we've
            // built *after* those files, then we're "pseudo up to date" and
            // eligible for a fast rebuild.
            let newest_dts_change_time =
                self.tasks[upstream.task].get_latest_changed_dts_mtime(&self.host);
            if !is_zero_time(newest_dts_change_time)
                && newest_dts_change_time < oldest_output_file_and_time.time
            {
                ref_dts_unchanged = true;
                continue;
            }

            // We have an output older than an upstream output - we are out
            // of date.
            return UpToDateStatus::with_data(
                UpToDateStatusKind::InputFileNewer,
                UpToDateStatusData::InputOutputName(out_of_date_input()),
            );
        }

        let check_input_file_time = |input_file: &RootedFilePath| -> Option<UpToDateStatus> {
            let input_time = self.host.get_mtime(input_file);
            if input_time > oldest_output_file_and_time.time {
                // Output file is older than input file.
                return Some(UpToDateStatus::with_data(
                    UpToDateStatusKind::InputFileNewer,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: input_file.as_path(),
                        output: oldest_output_file_and_time.file.clone(),
                    }),
                ));
            }
            None
        };

        if let Some(config_status) = {
            let config = self.tasks[task_id].config.clone();
            check_input_file_time(&config)
        } {
            return config_status;
        }

        for extended_config in resolved.extended_source_files() {
            if let Some(extended_config_status) = check_input_file_time(&extended_config) {
                return extended_config_status;
            }
        }

        for package_json in build_info.get_package_jsons(&get_build_info_directory()) {
            let package_json_time = self.host.get_mtime(&package_json);
            if is_zero_time(package_json_time) {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::InputFileMissing,
                    UpToDateStatusData::FilePath(package_json),
                );
            }
            if package_json_time > oldest_output_file_and_time.time {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::InputFileNewer,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: package_json.as_path(),
                        output: oldest_output_file_and_time.file.clone(),
                    }),
                );
            }
        }
        for package_json in build_info.get_missing_package_jsons(&get_build_info_directory()) {
            if !is_zero_time(self.host.get_mtime(&package_json)) {
                return UpToDateStatus::with_data(
                    UpToDateStatusKind::InputFileNewer,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: package_json.as_path(),
                        output: oldest_output_file_and_time.file.clone(),
                    }),
                );
            }
        }
        self.tasks[task_id].package_jsons =
            build_info.get_package_jsons(&get_build_info_directory());
        self.tasks[task_id]
            .package_jsons
            .extend(build_info.get_missing_package_jsons(&get_build_info_directory()));

        UpToDateStatus::with_data(
            if_else(
                ref_dts_unchanged,
                UpToDateStatusKind::UpToDateWithUpstreamTypes,
                if_else(
                    input_text_unchanged,
                    UpToDateStatusKind::UpToDateWithInputFileText,
                    UpToDateStatusKind::UpToDate,
                ),
            ),
            UpToDateStatusData::InputOutputFileAndTime(InputOutputFileAndTime {
                input: newest_input_file_and_time,
                output: oldest_output_file_and_time,
            }),
        )
    }

    /// `(t *BuildTask) reportUpToDateStatus`.
    fn report_up_to_date_status(&mut self, task_id: TaskId) {
        if !self.build_options().verbose.is_true() {
            return;
        }
        let Some(status) = self.tasks[task_id].status.clone() else {
            return;
        };
        let config_file = self.relative_file_name(&self.tasks[task_id].config);
        let diagnostic = match status.kind {
            UpToDateStatusKind::ConfigFileNotFound => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_config_file_does_not_exist,
                &[config_file],
            ),
            UpToDateStatusKind::UpstreamErrors => {
                let upstream_status = status.upstream_errors();
                let rel_ref = self.relative_path(&upstream_status.r#ref);
                new_compiler_diagnostic(
                    if_else(
                        upstream_status.ref_has_upstream_errors,
                        &tsc_diagnostics::Project_0_can_t_be_built_because_its_dependency_1_was_not_built,
                        &tsc_diagnostics::Project_0_can_t_be_built_because_its_dependency_1_has_errors,
                    ),
                    &[config_file, rel_ref],
                )
            }
            UpToDateStatusKind::BuildErrors => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_it_has_errors,
                &[config_file],
            ),
            UpToDateStatusKind::UpToDate => {
                // This is to ensure skipping verbose log for projects that
                // were built, and then some other package changed but this
                // package doesnt need update.
                if let Some(input_output) = status.input_output_file_and_time() {
                    let input = self.relative_file_name(&input_output.input.file);
                    let output = self.relative_file_name(&input_output.output.file);
                    new_compiler_diagnostic(
                        &tsc_diagnostics::Project_0_is_up_to_date_because_newest_input_1_is_older_than_output_2,
                        &[config_file, input, output],
                    )
                } else {
                    return;
                }
            }
            UpToDateStatusKind::UpToDateWithUpstreamTypes => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_up_to_date_with_d_ts_files_from_its_dependencies,
                &[config_file],
            ),
            UpToDateStatusKind::UpToDateWithInputFileText => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_up_to_date_but_needs_to_update_timestamps_of_output_files_that_are_older_than_input_files,
                &[config_file],
            ),
            UpToDateStatusKind::InputFileMissing => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_input_1_does_not_exist,
                &[
                    config_file,
                    self.relative_file_name(status.file_path_data()),
                ],
            ),
            UpToDateStatusKind::OutputMissing => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_output_file_1_does_not_exist,
                &[
                    config_file,
                    self.relative_file_name(status.file_path_data()),
                ],
            ),
            UpToDateStatusKind::InputFileNewer => {
                let input_output = status.input_output_name().expect("inputOutputName");
                let output = self.relative_file_name(&input_output.output);
                let input = self.relative_path(&input_output.input);
                new_compiler_diagnostic(
                    &tsc_diagnostics::Project_0_is_out_of_date_because_output_1_is_older_than_input_2,
                    &[config_file, output, input],
                )
            }
            UpToDateStatusKind::OutOfDateBuildInfoWithPendingEmit => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_that_some_of_the_changes_were_not_emitted,
                &[
                    config_file,
                    self.relative_file_name(status.file_path_data()),
                ],
            ),
            UpToDateStatusKind::OutOfDateBuildInfoWithErrors => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_that_program_needs_to_report_errors,
                &[
                    config_file,
                    self.relative_file_name(status.file_path_data()),
                ],
            ),
            UpToDateStatusKind::OutOfDateOptions => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_there_is_change_in_compilerOptions,
                &[
                    config_file,
                    self.relative_file_name(status.file_path_data()),
                ],
            ),
            UpToDateStatusKind::OutOfDateRoots => {
                let input_output = status.input_output_name().expect("inputOutputName");
                let output = self.relative_file_name(&input_output.output);
                let input = self.relative_path(&input_output.input);
                new_compiler_diagnostic(
                    &tsc_diagnostics::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_that_file_2_was_root_file_of_compilation_but_not_any_more,
                    &[config_file, output, input],
                )
            }
            UpToDateStatusKind::TsVersionOutputOfDate => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_out_of_date_because_output_for_it_was_generated_with_version_1_that_differs_with_current_version_2,
                &[
                    config_file,
                    status.version_data().to_string(),
                    tsc_core::version::version().to_string(),
                ],
            ),
            UpToDateStatusKind::ForceBuild => new_compiler_diagnostic(
                &tsc_diagnostics::Project_0_is_being_forcibly_rebuilt,
                &[config_file],
            ),
            UpToDateStatusKind::Solution => return, // Does not need to report status.
        };
        self.tasks[task_id].report_status(&diagnostic);
    }

    /// `(t *BuildTask) updateTimeStamps`.
    fn update_task_time_stamps(
        &mut self,
        task_id: TaskId,
        emitted_files: &[RootedFilePath],
        verbose_message: &'static Message,
    ) {
        let emitted: FxHashSet<RootedFilePath> = emitted_files.iter().cloned().collect();
        let mut verbose_message_reported = false;
        let resolved = self.tasks[task_id].resolved.clone().expect("resolved");
        let build_info_name = resolved.get_build_info_file_name();
        let now = self.opts.sys.now();
        if self.tasks[task_id].can_update_js_dts_output_timestamps() {
            for output_file in resolved.get_output_file_names() {
                self.update_time_stamp(
                    task_id,
                    &output_file,
                    &emitted,
                    &mut verbose_message_reported,
                    verbose_message,
                    now,
                    &build_info_name,
                );
            }
        }
        self.update_time_stamp(
            task_id,
            &resolved.get_build_info_file_name(),
            &emitted,
            &mut verbose_message_reported,
            verbose_message,
            now,
            &build_info_name,
        );
    }

    /// The `updateTimeStamp` closure inside Go's `updateTimeStamps`.
    #[allow(clippy::too_many_arguments)]
    fn update_time_stamp(
        &mut self,
        task_id: TaskId,
        file: &RootedFilePath,
        emitted: &FxHashSet<RootedFilePath>,
        verbose_message_reported: &mut bool,
        verbose_message: &'static Message,
        now: SystemTime,
        build_info_name: &RootedFilePath,
    ) {
        if emitted.contains(file) {
            return;
        }
        if !*verbose_message_reported && self.build_options().verbose.is_true() {
            let rel_config = self.relative_file_name(&self.tasks[task_id].config);
            let diagnostic = new_compiler_diagnostic(verbose_message, &[rel_config]);
            self.tasks[task_id].report_status(&diagnostic);
            *verbose_message_reported = true;
        }
        if self.host.set_mtime(file, now).is_ok() {
            if *file == *build_info_name {
                let entry = self.tasks[task_id].build_info_entry.clone();
                if let Some(entry) = entry.borrow_mut().as_mut() {
                    entry.m_time = now;
                }
            } else if self.tasks[task_id]
                .store_output_time_stamp(self.command_compiler_options().watch.is_true())
            {
                self.host.store_mtime(file, now);
            }
        }
    }

    /// `(t *BuildTask) cleanProject`.
    pub(crate) fn clean_project(&mut self, task_id: TaskId) {
        let Some(resolved) = self.tasks[task_id].resolved.clone() else {
            let diagnostic = new_compiler_diagnostic(
                &tsc_diagnostics::File_0_not_found,
                &[self.tasks[task_id].config.as_string().to_string()],
            );
            self.tasks[task_id].report_diagnostic(diagnostic);
            if let Some(result) = &mut self.tasks[task_id].result {
                result.exit_status = ExitStatus::DiagnosticsPresentOutputsSkipped;
            }
            return;
        };

        let inputs: FxHashSet<PathKey> = resolved
            .file_names()
            .iter()
            .map(|file_name| self.case_sensitivity.path_key(&file_name.as_path()))
            .collect();
        for output_file in resolved.get_output_file_names() {
            self.task_clean_project_output(task_id, &output_file, &inputs);
        }
        self.task_clean_project_output(task_id, &resolved.get_build_info_file_name(), &inputs);
    }

    /// `(t *BuildTask) cleanProjectOutput`.
    fn task_clean_project_output(
        &mut self,
        task_id: TaskId,
        output_file: &RootedFilePath,
        inputs: &FxHashSet<PathKey>,
    ) {
        let output_path = self.case_sensitivity.path_key(&output_file.as_path());
        // If output name is same as input file name, do not delete and
        // ignore the error.
        if inputs.contains(&output_path) {
            return;
        }
        if self.host.fs().file_exists(output_file) {
            if !self.build_options().dry.is_true() {
                if self.host.fs().remove(&output_file.as_path()).is_err() {
                    let diagnostic = new_compiler_diagnostic(
                        &tsc_diagnostics::Failed_to_delete_file_0,
                        &[output_file.as_string().to_string()],
                    );
                    self.tasks[task_id].report_diagnostic(diagnostic);
                }
            } else if let Some(result) = &mut self.tasks[task_id].result {
                result.files_to_delete.push(output_file.clone());
            }
        }
    }

    /// `(t *BuildTask) updateWatch`.
    pub(crate) fn task_update_watch(
        &mut self,
        task_id: TaskId,
        old_cache: &SyncMap<PathKey, SystemTime>,
    ) {
        if let Some(resolved) = self.tasks[task_id].resolved.clone() {
            if self.tasks[task_id].can_update_js_dts_output_timestamps() {
                for output_file in resolved.get_output_file_names() {
                    self.host
                        .store_mtime_from_old_cache(&output_file, old_cache);
                }
            }
        }
    }

    /// `h.ReadBuildInfo` — Go's task-aware `BuildInfoReader`
    /// implementation; looks the task up by `config.ConfigName()` and
    /// load-or-stores its build-info entry.
    ///
    /// PORT(dead-code): in Go the orchestrator itself is passed as the
    /// `BuildInfoReader` to `ReadBuildInfoProgram`. In Rust the
    /// `OrchestratorState` is driven through `&mut` and cannot be
    /// `Arc<dyn BuildInfoReader>`, so `TaskBuildInfoReader` is used
    /// instead; this method is retained for parity with the Go API.
    #[allow(dead_code)]
    pub(crate) fn task_read_build_info(
        &mut self,
        config: &ParsedCommandLine,
    ) -> Option<Rc<BuildInfo>> {
        let config_path = self
            .case_sensitivity
            .path_key(&config.config_name().as_path());
        let task_id = *self
            .tasks_by_path
            .get(&config_path)
            .unwrap_or_else(|| panic!("No build task found for {}", config_path.as_string()));
        self.tasks[task_id]
            .load_or_store_build_info(
                &self.host,
                self.case_sensitivity,
                config.get_build_info_file_name(),
            )
            .0
    }
}
