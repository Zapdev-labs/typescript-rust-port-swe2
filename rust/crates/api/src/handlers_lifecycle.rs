// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Lifecycle/session handlers — profiling, snapshot create/update/release,
// the language-server snapshot, default-project lookup, and the build
// orchestrator (`handleStartCPUProfile` … `handleCleanReferences`,
// session.go:1372-1989) plus the snapshot diff/response helpers
// (`computeSnapshotChanges`/`createSnapshotResponse`/
// `createSnapshotOperationResponse`, session.go:5047-5166).
//
// PORT notes:
// - Go's `defer` becomes RAII: `SnapshotReleaseGuard` performs
//   `releaseSnapshot` on drop, so early returns and error paths release the
//   retained base the same way Go's deferred call does.
// - `sd.fileSystem` is `Arc<dyn Vfs>` — non-optional — so the session fs is
//   stored as a placeholder where Go stores nil; a `RequestFileSystem`
//   downcast (`is_request_file_system`) recovers Go's `!= nil` checks.
//   `has_full_file_system` answers false for the placeholder exactly as it
//   would for Go's nil.
// - `new_for_update` takes an explicit `base_source` twin because trait
//   objects cannot be re-asserted (`fs.(FileHandleSource)` in Go). The
//   session fs is source-capable only for LSP sessions (`OverlayFs`); a
//   standalone `snapshotHost.fs` gets `None`, and `RequestFileSystem` bases
//   recover their own source inside `new_for_update`.
// - `module_resolver_factory` and `api_update` are `self: &Arc<Self>`
//   methods; handlers receive `&Session`, so `self_arc` rebuilds the owning
//   `Arc` (see its SAFETY comment).
// - `DiffOrderedMaps`/`DiffMaps` run over `projects_by_id()` vecs and
//   `files_by_path()` maps; `*project.Project`/`*compiler.Program` identity
//   is `Rc::ptr_eq`. The Go ordered-map diff iterates each map's own order;
//   `projects_by_id()` is already stable (ID-sorted).
// - Build diagnostics: a `DiagnosticFile.node` minted by the orchestrator's
//   internal programs/config parses indexes arenas unreachable from the
//   session, so `strip_diagnostic_nodes` clears `node` recursively — the
//   same `DiagnosticFile` snapshot rendering `diagnostic_response` uses
//   for foreign arenas (handlers_ls.rs) — identical output except live
//   `span_map`/`canonical_source_file` lookups.
// - `pprof` diverges from Go by design (see tsc-pprof): CPU profiles use
//   the `pprof` crate; heap "profiles" are a memory summary.

use std::cell::{Cell, RefCell};
use std::io;
use std::rc::Rc;
use std::sync::Arc;
use std::time::{Duration, SystemTime};

use rustc_hash::FxHashMap;
use tsc_ast as ast;
use tsc_collections as collections;
use tsc_core as core_;
use tsc_execute::build;
use tsc_execute::tsc;
use tsc_ipc as ipc;
use tsc_ls as ls;
use tsc_project as project;
use tsc_tspath as tspath;
use tsc_vfs as vfs;

use crate::module_resolution::module_resolution_error;
use crate::proto::*;
use crate::requestfilesystem;
use crate::session::*;

/// `snapshotOpenState` — the open project/file paths a snapshot tracks so
/// later requests know which opens are still pending (session.go:1721).
struct SnapshotOpenState {
    open_projects: collections::Set<tspath::PathKey>,
    open_files: collections::Set<tspath::PathKey>,
}

/// `languageServerSnapshotUpdate` (session.go:1675) — the pending request
/// plus the open state it will become once committed.
struct LanguageServerSnapshotUpdate {
    request: Rc<project::snapshot::ApiSnapshotRequest>,
    open_state: SnapshotOpenState,
}

/// Go's `defer func() { _ = s.releaseSnapshot(h) }()` — releases a retained
/// snapshot handle on drop, including error and panic paths.
struct SnapshotReleaseGuard<'a> {
    session: &'a Session,
    handle: Option<SnapshotId>,
}

impl Drop for SnapshotReleaseGuard<'_> {
    fn drop(&mut self) {
        if let Some(handle) = self.handle {
            let _ = self.session.release_snapshot(handle);
        }
    }
}

/// `fs.(requestfilesystem.requestFileSystem)` — distinguishes a stored
/// request filesystem from the session-fs placeholder (see file header).
fn is_request_file_system(fs: &Arc<dyn vfs::Vfs>) -> bool {
    fs.as_concrete()
        .is_some_and(|c| c.is::<requestfilesystem::RequestFileSystem>())
}

/// `NewDiagnosticResponses` for orchestrator results — see the file header
/// for why `DiagnosticFile.node` must be stripped before rendering.
fn build_diagnostic_responses(diags: &[ast::diagnostic::DiagnosticRef]) -> Vec<DiagnosticResponse> {
    let stripped: Vec<ast::diagnostic::DiagnosticRef> =
        diags.iter().map(strip_diagnostic_nodes).collect();
    new_diagnostic_responses(&stripped, &[])
}

/// Recursively clears `file.node` so `new_diagnostic_response` renders from
/// the `DiagnosticFile` snapshot (`node` indexes only the arena that minted
/// it; orchestrator arenas are unreachable here).
fn strip_diagnostic_nodes(d: &ast::diagnostic::DiagnosticRef) -> ast::diagnostic::DiagnosticRef {
    let stripped = ast::diagnostic::lock_diagnostic(d).clone_diagnostic();
    {
        let mut locked = ast::diagnostic::lock_diagnostic(&stripped);
        if let Some(mut file) = locked.file().cloned() {
            if file.node.is_some() {
                file.node = None;
                locked.set_file(Some(file));
            }
        }
        let chain: Vec<ast::diagnostic::DiagnosticRef> = locked
            .message_chain()
            .iter()
            .map(strip_diagnostic_nodes)
            .collect();
        locked.set_message_chain(chain);
        let related: Vec<ast::diagnostic::DiagnosticRef> = locked
            .related_information()
            .iter()
            .map(strip_diagnostic_nodes)
            .collect();
        locked.set_related_info(related);
    }
    stripped
}

/// `NewProjectResponse` with the tsconfig arena that the project's
/// command-line diagnostics resolve through — a `DiagnosticFile.node`
/// indexes only the arena that minted it (see `diagnostic_response` in
/// handlers_ls.rs). Projects without a `config_file` (synthetic programs)
/// render from `DiagnosticFile` snapshots.
fn project_response(project: &project::project::Project) -> ProjectResponse {
    let nodes: &[ast::Node] = project
        .command_line
        .as_ref()
        .and_then(|command_line| command_line.config_file.as_ref())
        .map(|config_file| config_file.nodes.as_slice())
        .unwrap_or(&[]);
    new_project_response(project, nodes)
}

/// `collections.DiffOrderedMaps` over two `projects_by_id()` results —
/// `Rc::ptr_eq` stands in for Go's `==` on `*project.Project`. Added entries
/// iterate `next` first, then removed/modified iterate `prev`, matching
/// `DiffOrderedMapsFunc`'s pass order.
fn diff_project_collections(
    prev: &[(project::project::Id, Rc<project::project::Project>)],
    next: &[(project::project::Id, Rc<project::project::Project>)],
    mut on_added: impl FnMut(&project::project::Id, &project::project::Project),
    mut on_removed: impl FnMut(&project::project::Id, &project::project::Project),
    mut on_modified: impl FnMut(
        &project::project::Id,
        &project::project::Project,
        &project::project::Project,
    ),
) {
    let prev_by_id: FxHashMap<&project::project::Id, &Rc<project::project::Project>> =
        prev.iter().map(|(id, p)| (id, p)).collect();
    for (id, proj) in next {
        if !prev_by_id.contains_key(id) {
            on_added(id, proj);
        }
    }
    let next_by_id: FxHashMap<&project::project::Id, &Rc<project::project::Project>> =
        next.iter().map(|(id, p)| (id, p)).collect();
    for (id, old_proj) in prev {
        match next_by_id.get(id) {
            Some(&new_proj) => {
                if !Rc::ptr_eq(old_proj, new_proj) {
                    on_modified(id, old_proj, new_proj);
                }
            }
            None => on_removed(id, old_proj),
        }
    }
}

/// `computeSnapshotChanges` (session.go:5047).
fn compute_snapshot_changes(
    prev: &project::snapshot::Snapshot,
    next: &project::snapshot::Snapshot,
) -> SnapshotChanges {
    let prev_projects = prev.project_collection.projects_by_id();
    let next_projects = next.project_collection.projects_by_id();

    // Go's callbacks mutate `changes`; the port's `FnMut` closures would
    // each take an exclusive `&mut`, so the accumulators live in `RefCell`.
    let changes = RefCell::new(SnapshotChanges::default());
    diff_project_collections(
        &prev_projects,
        &next_projects,
        // onAdded: new project — nothing to retain from previous snapshot.
        |_id, _proj| {},
        // onRemoved: project removed entirely.
        |_id, old_proj| {
            changes
                .borrow_mut()
                .removed_projects
                .push(old_proj.id().clone());
        },
        // onModified: project changed, diff its files.
        |_id, old_proj, new_proj| {
            let programs_equal = match (old_proj.get_program(), new_proj.get_program()) {
                (Some(old_program), Some(new_program)) => Rc::ptr_eq(old_program, new_program),
                (None, None) => true,
                _ => false,
            };
            if programs_equal {
                return;
            }
            let empty: FxHashMap<tspath::PathKey, ast::NodeId> = FxHashMap::default();
            let old_files = old_proj
                .get_program()
                .map(|p| p.files_by_path())
                .unwrap_or(&empty);
            let new_files = new_proj
                .get_program()
                .map(|p| p.files_by_path())
                .unwrap_or(&empty);
            let project_changes = RefCell::new(ProjectFileChanges::default());
            let mut on_removed = |path: &tspath::PathKey, _file: &ast::NodeId| {
                project_changes.borrow_mut().deleted_files.push(path.clone());
            };
            let mut on_changed =
                |path: &tspath::PathKey, _old: &ast::NodeId, _new: &ast::NodeId| {
                    project_changes.borrow_mut().changed_files.push(path.clone());
                };
            core_::core::diff_maps(
                old_files,
                new_files,
                None, // onAdded: new file in project, not a change.
                Some(&mut on_removed),
                Some(&mut on_changed),
            );
            let project_changes = project_changes.into_inner();
            if !project_changes.changed_files.is_empty() || !project_changes.deleted_files.is_empty()
            {
                changes
                    .borrow_mut()
                    .changed_projects
                    .insert(new_proj.id().clone(), project_changes);
            }
        },
    );
    changes.into_inner()
}

/// `apiBuildSystem` (session.go:1963) — the `tsc.System` view of an API
/// session for a build orchestrator: output is discarded, the host
/// filesystem is the snapshot host's, processes cannot be spawned.
struct ApiBuildSystem {
    session: Arc<Session>,
    current_directory: tspath::RootedDirectoryPath,
    start: SystemTime,
    /// The port's `System` trait carries a diagnostic-arena registry Go
    /// doesn't need (live `*ast.SourceFile` pointers); it backs the CLI
    /// reporter path — unused by API result conversion.
    diagnostic_registry: Arc<tsc::DiagnosticRegistry>,
}

impl tsc::System for ApiBuildSystem {
    /// `Writer` — Go's `io.Discard`.
    fn writer(&self) -> tsc::SharedWriter {
        tsc::SharedWriter::new(io::sink())
    }

    /// `ErrorWriter` — Go's `io.Discard`.
    fn error_writer(&self) -> tsc::SharedWriter {
        tsc::SharedWriter::new(io::sink())
    }

    fn fs(&self) -> Arc<dyn vfs::Vfs> {
        self.session.snapshot_host.fs().clone()
    }

    fn default_library_path(&self) -> tspath::RootedDirectoryPath {
        self.session.default_library_path()
    }

    fn current_directory(&self) -> tspath::RootedDirectoryPath {
        self.current_directory.clone()
    }

    fn write_output_is_tty(&self) -> bool {
        false
    }

    fn width_of_terminal(&self) -> usize {
        0
    }

    fn environment_variable(&self, _name: &str) -> Option<String> {
        None
    }

    fn spawn(
        &self,
        _command: &[String],
        _dir: &str,
        _stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn tsc_contentmapper::hostimpl::SpawnedProcess>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "spawning processes is not supported by the API build orchestrator",
        ))
    }

    fn now(&self) -> SystemTime {
        SystemTime::now()
    }

    fn since_start(&self) -> Duration {
        self.start.elapsed().unwrap_or_default()
    }

    fn diagnostic_registry(&self) -> &Arc<tsc::DiagnosticRegistry> {
        &self.diagnostic_registry
    }
}

impl Session {
    /// `Arc<Self>` handle for collaborators declared `self: &Arc<Self>`
    /// (`module_resolver_factory`). Go's `s` pointer is freely shareable;
    /// Rust's `&Session` receiver is not.
    ///
    /// SAFETY: `Session`'s only constructor (`new_session`) returns
    /// `Arc<Session>` and its fields are `pub(crate)` with no public
    /// constructor, so every `&Session` in this crate is a borrow of that
    /// `Arc` allocation. `increment_strong_count` before `from_raw` keeps
    /// the allocation owned by both the original Arc and this clone.
    #[allow(unsafe_code)]
    fn self_arc(&self) -> Arc<Self> {
        let ptr = self as *const Self;
        unsafe {
            Arc::increment_strong_count(ptr);
            Arc::from_raw(ptr)
        }
    }

    /// `s.FS()` plus its `FileHandleSource` assertion (Go's lazy
    /// `fs.(project.FileHandleSource)` inside request filesystem lookups):
    /// an LSP session's `OverlayFs` is a source; the standalone snapshot
    /// host fs is `vfs.FS`-only.
    fn fs_and_source(
        &self,
    ) -> (
        Arc<dyn vfs::Vfs>,
        Option<Arc<dyn project::overlayfs::FileHandleSource>>,
    ) {
        if let Some(session) = &self.project_session {
            let overlay = session.fs().clone();
            return (overlay.clone(), Some(overlay));
        }
        (self.snapshot_host.fs().clone(), None)
    }

    /// `s.handleStartCPUProfile`.
    pub(crate) fn handle_start_cpu_profile(
        &self,
        _ctx: &core_::context::Context,
        params: &ProfileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        if params.dir.is_empty() {
            return Err(format!("{ERR_CLIENT_ERROR}: dir is required"));
        }
        let profile_directory =
            tspath::to_rooted_directory_path(&params.dir, &self.get_current_directory());
        self.cpu_profiler
            .start_cpu_profile(profile_directory.as_string())
            .map_err(|e| format!("{ERR_CLIENT_ERROR}: failed to start CPU profile: {e}"))?;
        Ok(None)
    }

    /// `s.handleStopCPUProfile`.
    pub(crate) fn handle_stop_cpu_profile(
        &self,
        _ctx: &core_::context::Context,
    ) -> Result<ProfileResult, String> {
        let file_path = self
            .cpu_profiler
            .stop_cpu_profile()
            .map_err(|e| format!("{ERR_CLIENT_ERROR}: failed to stop CPU profile: {e}"))?;
        Ok(ProfileResult {
            file: tspath::to_rooted_file_path(&file_path, &self.get_current_directory()),
        })
    }

    /// `s.handleSaveHeapProfile`.
    pub(crate) fn handle_save_heap_profile(
        &self,
        _ctx: &core_::context::Context,
        params: &ProfileParams,
    ) -> Result<ProfileResult, String> {
        if params.dir.is_empty() {
            return Err(format!("{ERR_CLIENT_ERROR}: dir is required"));
        }
        let profile_directory =
            tspath::to_rooted_directory_path(&params.dir, &self.get_current_directory());
        let file_path = tsc_pprof::save_heap_profile(profile_directory.as_string())
            .map_err(|e| format!("{ERR_CLIENT_ERROR}: failed to save heap profile: {e}"))?;
        Ok(ProfileResult {
            file: tspath::to_rooted_file_path(&file_path, &self.get_current_directory()),
        })
    }

    /// `s.handleInitialize`.
    pub(crate) fn handle_initialize(
        &self,
        _ctx: &core_::context::Context,
    ) -> Result<InitializeResponse, String> {
        Ok(InitializeResponse {
            case_sensitivity: self.case_sensitivity(),
            current_directory: self.get_current_directory(),
        })
    }

    /// `s.handleCreateSnapshot` creates a new independent snapshot.
    pub(crate) fn handle_create_snapshot(
        &self,
        ctx: &core_::context::Context,
        params: &CreateSnapshotParams,
    ) -> Result<CreateSnapshotResponse, String> {
        let mut api_request = self.to_api_snapshot_request(&params.snapshot_request_changes)?;
        api_request.user_preferences = params.user_preferences.clone();
        if let Some(prepare) = &params.prepare_auto_imports {
            api_request.prepare_auto_imports = prepare.to_uri(&self.get_current_directory());
        }

        let open_state =
            self.reconcile_snapshot_opens(&mut api_request, &SnapshotOpenState::default());
        let mut file_changes = self.to_file_change_summary(params.file_notifications.as_ref());
        let mut snapshot_file_system: Option<Arc<dyn vfs::Vfs>> = None;
        if let Some(fs_params) = &params.file_system {
            let (base, base_source) = self.fs_and_source();
            let file_system = requestfilesystem::new_for_update(
                Some(fs_params),
                base,
                base_source,
                &self.get_current_directory(),
                &mut file_changes,
            )
            .map_err(|e| format!("{ERR_CLIENT_ERROR}: {e}"))?;
            snapshot_file_system = Some(file_system.clone());
            api_request.file_system = Some(file_system);
            api_request.replace_file_system = fs_params.kind == requestfilesystem::Kind::Full;
        }
        let root = self.snapshot_host.new_root_snapshot();
        let (snapshot, error) = self.snapshot_host.clone_snapshot(
            ctx,
            &root,
            file_changes,
            Some(Rc::new(api_request)),
        );
        root.deref();
        if let Some(error) = error {
            snapshot.deref();
            return Err(format!("{ERR_CLIENT_ERROR}: failed to create snapshot: {error}"));
        }
        if let Err(error) =
            self.validate_prepared_auto_imports(ctx, &snapshot, params.prepare_auto_imports.as_ref())
        {
            snapshot.deref();
            return Err(error);
        }
        if let Some(error) = module_resolution_error(&snapshot) {
            snapshot.deref();
            return Err(error);
        }

        let response =
            self.create_snapshot_response(&snapshot, None, Some(&params.snapshot_request_changes));
        self.register_snapshot(&snapshot, open_state, snapshot_file_system);
        Ok(response)
    }

    /// `s.handleUpdateSnapshot` derives a snapshot from a retained base.
    pub(crate) fn handle_update_snapshot(
        &self,
        ctx: &core_::context::Context,
        params: &UpdateSnapshotParams,
    ) -> Result<CreateSnapshotResponse, String> {
        let base_sd = self.retain_snapshot_data(params.snapshot)?;
        // `defer func() { _ = s.releaseSnapshot(params.Snapshot) }()`.
        let _base_release = SnapshotReleaseGuard {
            session: self,
            handle: Some(params.snapshot),
        };

        let default_changes;
        let changes = match &params.changes {
            Some(changes) => changes,
            None => {
                default_changes = CreateSnapshotParams::default();
                &default_changes
            }
        };
        let mut api_request = self.to_api_snapshot_request(&changes.snapshot_request_changes)?;
        api_request.user_preferences = changes.user_preferences.clone();
        if let Some(prepare) = &changes.prepare_auto_imports {
            api_request.prepare_auto_imports = prepare.to_uri(&self.get_current_directory());
        }
        let open_state = self.reconcile_snapshot_opens(
            &mut api_request,
            &SnapshotOpenState {
                open_projects: base_sd.open_projects.clone(),
                open_files: base_sd.open_files.clone(),
            },
        );
        let mut file_changes = self.to_file_change_summary(changes.file_notifications.as_ref());
        // `snapshotFileSystem := baseSD.fileSystem` — `Some` only when the
        // base stored a request filesystem (Go's `!= nil`); see the file
        // header on the placeholder.
        let mut snapshot_file_system =
            is_request_file_system(&base_sd.file_system).then(|| base_sd.file_system.clone());
        if let Some(fs_params) = &changes.file_system {
            let (base, base_source) = match &snapshot_file_system {
                Some(base) => (base.clone(), None),
                None => self.fs_and_source(),
            };
            let file_system = requestfilesystem::new_for_update(
                Some(fs_params),
                base,
                base_source,
                &self.get_current_directory(),
                &mut file_changes,
            )
            .map_err(|e| format!("{ERR_CLIENT_ERROR}: {e}"))?;
            snapshot_file_system = Some(file_system);
        }
        if let Some(fs) = &snapshot_file_system {
            api_request.file_system = Some(fs.clone());
            api_request.replace_file_system =
                changes.file_system.as_ref().is_some_and(|fs| fs.kind == requestfilesystem::Kind::Full);
        }
        let (snapshot, error) = self.snapshot_host.clone_snapshot(
            ctx,
            &base_sd.snapshot,
            file_changes,
            Some(Rc::new(api_request)),
        );
        if let Some(error) = error {
            snapshot.deref();
            return Err(format!("{ERR_CLIENT_ERROR}: failed to update snapshot: {error}"));
        }
        if let Err(error) =
            self.validate_prepared_auto_imports(ctx, &snapshot, changes.prepare_auto_imports.as_ref())
        {
            snapshot.deref();
            return Err(error);
        }
        if let Some(error) = module_resolution_error(&snapshot) {
            snapshot.deref();
            return Err(error);
        }

        let response = self.create_snapshot_response(
            &snapshot,
            Some(&*base_sd.snapshot),
            Some(&changes.snapshot_request_changes),
        );
        self.register_snapshot(&snapshot, open_state, snapshot_file_system);
        Ok(response)
    }

    /// `s.toAPISnapshotRequest` (session.go:1516).
    fn to_api_snapshot_request(
        &self,
        changes: &SnapshotRequestChangesParams,
    ) -> Result<project::snapshot::ApiSnapshotRequest, String> {
        let session = self.self_arc();
        let mut api_request = project::snapshot::ApiSnapshotRequest::default();

        for p in &changes.open_projects {
            let config_file_name = p.to_file_name(&self.get_current_directory());
            let Some(configured_project_id) =
                project::project::parse_configured_project_id(&self.path_key(&config_file_name))
            else {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: invalid configured project ID: {}",
                    config_file_name.as_string()
                ));
            };
            api_request
                .ensure_programs
                .get_or_insert_with(|| {
                    collections::Set::with_size_hint(changes.open_projects.len())
                })
                .add(configured_project_id.as_id());
            api_request
                .open_projects
                .get_or_insert_with(|| {
                    collections::Set::with_size_hint(changes.open_projects.len())
                })
                .add(config_file_name);
        }

        for p in &changes.close_projects {
            let config_path = self.path_key(&self.to_file_name(p));
            api_request
                .close_projects
                .get_or_insert_with(|| {
                    collections::Set::with_size_hint(changes.close_projects.len())
                })
                .add(config_path);
        }

        for f in &changes.open_files {
            let file_name = f.to_file_name(&self.get_current_directory());
            let path = self.path_key(&file_name);
            if !api_request.open_files.contains_key(&path) {
                api_request.open_files.insert(path.clone(), file_name.clone());
                api_request.ensure_files.insert(path, file_name);
            }
        }

        for f in &changes.close_files {
            let path = self.to_uri(f).path_key(self.case_sensitivity());
            api_request
                .close_files
                .get_or_insert_with(|| {
                    collections::Set::with_size_hint(changes.close_files.len())
                })
                .add(path);
        }

        api_request.create_programs = Vec::with_capacity(changes.create_programs.len());
        for program_params in &changes.create_programs {
            let (compiler_options, option_diagnostics) =
                if program_params.compiler_options_input.values.is_some() {
                    program_params
                        .compiler_options_input
                        .finalize(&self.get_current_directory())
                } else {
                    (program_params.compiler_options.clone(), Vec::new())
                };
            let root_file_names: Vec<tspath::RootedFilePath> = program_params
                .root_files
                .iter()
                .map(|root_file| self.to_file_name(root_file))
                .collect();
            let mut request = project::snapshot::ApiCreateProgramRequest {
                root_file_names,
                compiler_options: Some(Arc::new(compiler_options)),
                project_references: Vec::new(),
                config_file_parsing_diagnostics: Vec::new(),
                module_resolver_factory: None,
                module_resolver_id: 0,
            };
            if let Some(options) = &program_params.options {
                request.project_references = options
                    .project_references
                    .iter()
                    .map(|r| Arc::new(r.clone()))
                    .collect();
                let mut diagnostics = option_diagnostics;
                diagnostics.extend(
                    options
                        .config_file_parsing_diagnostics
                        .iter()
                        .map(|d| d.to_diagnostic()),
                );
                request.config_file_parsing_diagnostics = diagnostics;
                request.module_resolver_factory = session.module_resolver_factory(options)?;
                request.module_resolver_id = options.module_resolver.0;
            } else {
                request.config_file_parsing_diagnostics = option_diagnostics;
            }
            api_request.create_programs.push(request);
        }

        api_request.reconfigure_programs = Vec::with_capacity(changes.reconfigure_programs.len());
        let mut reconfigured_program_ids: collections::Set<project::project::SyntheticProjectId> =
            collections::Set::new();
        for program_params in &changes.reconfigure_programs {
            let Some(program_id) =
                project::project::parse_synthetic_project_id(&program_params.id.0)
            else {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: invalid synthetic project handle: {}",
                    program_params.id
                ));
            };
            if reconfigured_program_ids.has(&program_id) {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: synthetic program reconfigured more than once: {program_id}"
                ));
            }
            reconfigured_program_ids.add(program_id.clone());
            let (compiler_options, option_diagnostics) =
                if program_params.compiler_options_input.values.is_some() {
                    program_params
                        .compiler_options_input
                        .finalize(&self.get_current_directory())
                } else {
                    (program_params.compiler_options.clone(), Vec::new())
                };
            let root_file_names: Vec<tspath::RootedFilePath> = program_params
                .root_files
                .iter()
                .map(|root_file| self.to_file_name(root_file))
                .collect();
            let mut create_request = project::snapshot::ApiCreateProgramRequest {
                root_file_names,
                compiler_options: Some(Arc::new(compiler_options)),
                project_references: Vec::new(),
                config_file_parsing_diagnostics: Vec::new(),
                module_resolver_factory: None,
                module_resolver_id: 0,
            };
            if let Some(options) = &program_params.options {
                create_request.project_references = options
                    .project_references
                    .iter()
                    .map(|r| Arc::new(r.clone()))
                    .collect();
                let mut diagnostics = option_diagnostics;
                diagnostics.extend(
                    options
                        .config_file_parsing_diagnostics
                        .iter()
                        .map(|d| d.to_diagnostic()),
                );
                create_request.config_file_parsing_diagnostics = diagnostics;
                create_request.module_resolver_factory =
                    session.module_resolver_factory(options)?;
                create_request.module_resolver_id = options.module_resolver.0;
            } else {
                create_request.config_file_parsing_diagnostics = option_diagnostics;
            }
            api_request
                .reconfigure_programs
                .push(project::snapshot::ApiReconfigureProgramRequest {
                    program_id,
                    create_program_request: create_request,
                });
        }

        if !changes.remove_programs.is_empty() {
            api_request.remove_programs =
                Some(collections::Set::with_size_hint(changes.remove_programs.len()));
        }
        for program_id in &changes.remove_programs {
            if reconfigured_program_ids.has(program_id) {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: synthetic program cannot be reconfigured and removed: {program_id}"
                ));
            }
            api_request
                .remove_programs
                .as_mut()
                .expect("remove_programs allocated")
                .add(program_id.clone());
        }
        if let Some(ensure_programs) = &changes.ensure_programs {
            api_request.ensure_all_programs = ensure_programs.all;
            if !ensure_programs.projects.is_empty() && api_request.ensure_programs.is_none() {
                api_request.ensure_programs =
                    Some(collections::Set::with_size_hint(ensure_programs.projects.len()));
            }
            for program in &ensure_programs.projects {
                api_request
                    .ensure_programs
                    .as_mut()
                    .expect("ensure_programs allocated")
                    .add(program.clone());
            }
        }
        Ok(api_request)
    }

    /// `s.validatePreparedAutoImports` (session.go:1659).
    fn validate_prepared_auto_imports(
        &self,
        ctx: &core_::context::Context,
        snapshot: &project::snapshot::Snapshot,
        file: Option<&DocumentIdentifier>,
    ) -> Result<(), String> {
        let Some(file) = file else {
            return Ok(());
        };
        // `ctx.Err()` — the port's Context tracks cancellation without the
        // concrete error value.
        if ctx.is_cancelled() {
            return Err("context canceled".to_string());
        }
        let uri = file.to_uri(&self.get_current_directory());
        let proj = snapshot.get_default_project(&uri);
        let prepared = proj.is_some()
            && snapshot.auto_import_registry().is_some_and(|registry| {
                registry.is_prepared_for_importing_file(
                    &uri.file_name(),
                    &ls::autoimport::ProjectId(Rc::from(
                        proj.as_ref().unwrap().id().as_str(),
                    )),
                    snapshot.user_preferences(),
                )
            });
        if !prepared {
            // `%s` on `*DocumentIdentifier` — its `Display` prints the URI
            // or file name like Go's `String()`.
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not prepare auto-imports for {file}"
            ));
        }
        Ok(())
    }

    /// `s.toLanguageServerSnapshotUpdate` (session.go:1680) — builds the API
    /// request and reconciled open state against the canonical
    /// language-server state (already locked by the caller).
    fn to_language_server_snapshot_update(
        &self,
        changes: &SnapshotRequestChangesParams,
        state: &LanguageServerState,
    ) -> Result<LanguageServerSnapshotUpdate, String> {
        let mut api_request = self.to_api_snapshot_request(changes)?;
        let open_state = self.reconcile_snapshot_opens(
            &mut api_request,
            &SnapshotOpenState {
                open_projects: state.open_projects.clone(),
                open_files: state.open_files.clone(),
            },
        );

        if let Some(remove_programs) = &mut api_request.remove_programs {
            let ids: Vec<project::project::SyntheticProjectId> =
                remove_programs.keys().iter().cloned().collect();
            for program_id in ids {
                if !state.created_programs.has(&program_id) {
                    remove_programs.delete(&program_id);
                }
            }
        }
        for reconfigure in &api_request.reconfigure_programs {
            if !state.created_programs.has(&reconfigure.program_id) {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: synthetic program is not owned by this API session: {}",
                    reconfigure.program_id
                ));
            }
        }
        Ok(LanguageServerSnapshotUpdate {
            request: Rc::new(api_request),
            open_state,
        })
    }

    /// `s.reconcileSnapshotOpens` (session.go:1726) — reconciles the
    /// request's open/close lists with the base open state, pruning
    /// redundant operations from `api_request` and returning the state the
    /// new snapshot will track.
    fn reconcile_snapshot_opens(
        &self,
        api_request: &mut project::snapshot::ApiSnapshotRequest,
        base: &SnapshotOpenState,
    ) -> SnapshotOpenState {
        let mut state = SnapshotOpenState {
            open_projects: base.open_projects.clone(),
            open_files: base.open_files.clone(),
        };
        if let Some(close_projects) = &mut api_request.close_projects {
            let paths: Vec<tspath::PathKey> = close_projects.keys().iter().cloned().collect();
            for path in paths {
                if state.open_projects.has(&path) {
                    state.open_projects.delete(&path);
                } else {
                    close_projects.delete(&path);
                }
            }
        }
        if let Some(open_projects) = &mut api_request.open_projects {
            let names: Vec<tspath::RootedFilePath> =
                open_projects.keys().iter().cloned().collect();
            for config_file_name in names {
                let path = self.path_key(&config_file_name);
                if state.open_projects.has(&path) {
                    open_projects.delete(&config_file_name);
                } else {
                    state.open_projects.add(path);
                }
            }
        }
        if let Some(close_files) = &mut api_request.close_files {
            let paths: Vec<tspath::PathKey> = close_files.keys().iter().cloned().collect();
            for path in paths {
                if state.open_files.has(&path) {
                    state.open_files.delete(&path);
                } else {
                    close_files.delete(&path);
                }
            }
        }
        let open_file_paths: Vec<tspath::PathKey> =
            api_request.open_files.keys().cloned().collect();
        for path in open_file_paths {
            if state.open_files.has(&path) {
                api_request.open_files.remove(&path);
            } else {
                state.open_files.add(path);
            }
        }
        state
    }

    /// `s.registerSnapshot` (session.go:1763) — same-ID snapshots bump the
    /// API ref count so client handles release independently;
    /// `file_system` is `None` where Go stores nil (see the file header).
    fn register_snapshot(
        &self,
        snapshot: &Arc<project::snapshot::Snapshot>,
        open_state: SnapshotOpenState,
        file_system: Option<Arc<dyn vfs::Vfs>>,
    ) {
        let file_system = file_system.unwrap_or_else(|| self.fs());
        let handle = Self::snapshot_handle(snapshot);
        let mut snapshots = self.snapshots.write().unwrap();
        if let Some(sd) = snapshots.get(&handle) {
            // Same snapshot already stored — release the caller's ref since
            // the stored snapshot already has one, and bump the API refcount.
            snapshot.deref();
            sd.ref_count.set(sd.ref_count.get() + 1);
        } else {
            // `SnapshotData::new` is module-private; the literal is its
            // initializer plus the open-state assignment.
            let sd = Arc::new(SnapshotData {
                handle,
                snapshot: Arc::clone(&snapshot),
                file_system,
                ref_count: Cell::new(1),
                open_projects: open_state.open_projects,
                open_files: open_state.open_files,
                symbol_registry: Default::default(),
                symbol_canonical_projects: Default::default(),
                project_registries: Default::default(),
            });
            snapshots.insert(handle, sd);
        }
    }

    /// `s.handleGetCurrentLanguageServerSnapshot` (session.go:1791).
    pub(crate) fn handle_get_current_language_server_snapshot(
        &self,
        ctx: &core_::context::Context,
        params: &GetCurrentLanguageServerSnapshotParams,
    ) -> Result<CreateSnapshotResponse, String> {
        let Some(project_session) = &self.project_session else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: getCurrentLanguageServerSnapshot requires an LSP-connected API session"
            ));
        };
        let mut base_snapshot: Option<Arc<project::snapshot::Snapshot>> = None;
        // Go's `defer releaseSnapshot` is registered before
        // `languageServerUpdateMu.Unlock`; Rust drops locals in reverse
        // declaration order, so `state` (declared later) unlocks first —
        // the same LIFO order.
        let mut base_release = SnapshotReleaseGuard {
            session: self,
            handle: None,
        };
        if params.base_snapshot != 0 {
            let base_sd = self.retain_snapshot_data(params.base_snapshot)?;
            base_release.handle = Some(params.base_snapshot);
            base_snapshot = Some(Arc::clone(&base_sd.snapshot));
        }

        // `s.languageServerUpdateMu.Lock()`.
        let mut state = self.language_server_state.lock().unwrap();
        let changes = params.changes.clone().unwrap_or_default();
        let update = self
            .to_language_server_snapshot_update(&changes.snapshot_request_changes, &state)?;

        let snapshot = project_session
            .api_update(
                ctx,
                project::filechange::FileChangeSummary::default(),
                Some(update.request.clone()),
            )
            .map_err(|e| {
                format!("{ERR_CLIENT_ERROR}: failed to update language server snapshot: {e}")
            })?;

        update.commit(&mut state, &snapshot);
        let response = self.create_snapshot_response(
            &snapshot,
            base_snapshot.as_deref(),
            Some(&changes.snapshot_request_changes),
        );
        self.register_snapshot(
            &snapshot,
            SnapshotOpenState {
                open_projects: state.open_projects.clone(),
                open_files: state.open_files.clone(),
            },
            None,
        );
        Ok(response)
    }

    /// `s.handleRelease` decrements the snapshot ref count (session.go:1830).
    pub(crate) fn handle_release(
        &self,
        _ctx: &core_::context::Context,
        params: &ReleaseParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        if params.snapshot == 0 {
            return Err(format!("{ERR_CLIENT_ERROR}: empty handle"));
        }
        self.release_snapshot(params.snapshot)?;
        Ok(Some(ipc::ResponsePayload::Json(
            ipc::marshal_params(&true).map_err(|e| e.to_string())?,
        )))
    }

    /// `s.handleGetDefaultProjectForFile` (session.go:1844) — `Ok(None)` is
    /// Go's nil `*ProjectResponse` (marshals `null`).
    pub(crate) fn handle_get_default_project_for_file(
        &self,
        _ctx: &core_::context::Context,
        params: &GetDefaultProjectForFileParams,
    ) -> Result<Option<ProjectResponse>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let uri = self.to_uri(&params.file);
        let Some(proj) = sd.snapshot.get_default_project(&uri) else {
            return Ok(None);
        };
        Ok(Some(project_response(&proj)))
    }

    /// `s.handleCreateBuildOrchestrator` (session.go:1859).
    pub(crate) fn handle_create_build_orchestrator(
        &self,
        _ctx: &core_::context::Context,
        params: &CreateBuildOrchestratorParams,
    ) -> Result<CreateBuildOrchestratorResponse, String> {
        let build_sys = self.get_build_sys(params);
        let mut command = tsc_tsoptions::commandlineparser::parse_build_command_line(
            &params.root_names,
            &build_sys.fs(),
            build_sys.current_directory(),
        );
        if let Some(compiler_options) = &params.compiler_options {
            command.compiler_options = Some(compiler_options.clone());
        }
        if let Some(build_options) = &params.build_options {
            command.build_options = Some(build_options.clone());
        }
        let orchestrator = build::new_orchestrator(build::Options {
            sys: build_sys,
            command: Arc::new(command),
            testing: None,
        });
        let build_orchestrator_id = new_build_orchestrator_id();
        // `s.buildMu` — the map mutex plays the same role (Go holds it
        // across the whole call below as well).
        self.build_orchestrators
            .lock()
            .unwrap()
            .insert(build_orchestrator_id, orchestrator);
        Ok(CreateBuildOrchestratorResponse {
            build_orchestrator_id,
        })
    }

    /// `s.handleDisposeBuildOrchestrator` (session.go:1880).
    pub(crate) fn handle_dispose_build_orchestrator(
        &self,
        _ctx: &core_::context::Context,
        params: &DisposeBuildOrchestratorParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let mut orchestrators = self.build_orchestrators.lock().unwrap();
        if orchestrators.remove(&params.build_orchestrator_id).is_none() {
            return Err("build orchestrator not found while disposing".to_string());
        }
        drop(orchestrators);
        Ok(Some(ipc::ResponsePayload::Json(
            ipc::marshal_params(&true).map_err(|e| e.to_string())?,
        )))
    }

    /// `s.handleBuild` (session.go:1890) — `buildMu` stays locked across the
    /// orchestrator call, serializing builds like Go.
    pub(crate) fn handle_build(
        &self,
        ctx: &core_::context::Context,
        params: &BuildParams,
    ) -> Result<BuildResponse, String> {
        let orchestrators = self.build_orchestrators.lock().unwrap();
        let Some(orchestrator) = orchestrators.get(&params.build_orchestrator_id) else {
            return Err(format!(
                "build orchestrator not found while building {}",
                params.project
            ));
        };
        let result = orchestrator.build(ctx, &params.project);

        Ok(BuildResponse {
            status: result.result.status,
            diagnostics: build_diagnostic_responses(&result.errors),
            statistics: result.statistics,
        })
    }

    /// `s.handleBuildReferences` (session.go:1905).
    pub(crate) fn handle_build_references(
        &self,
        ctx: &core_::context::Context,
        params: &BuildParams,
    ) -> Result<BuildResponse, String> {
        let orchestrators = self.build_orchestrators.lock().unwrap();
        let Some(orchestrator) = orchestrators.get(&params.build_orchestrator_id) else {
            return Err(format!(
                "build orchestrator not found for building references for {}",
                params.project
            ));
        };
        let result = orchestrator.build_references(ctx, &params.project);

        Ok(BuildResponse {
            status: result.result.status,
            diagnostics: build_diagnostic_responses(&result.errors),
            statistics: result.statistics,
        })
    }

    /// `s.handleCleanBuild` (session.go:1920).
    pub(crate) fn handle_clean_build(
        &self,
        _ctx: &core_::context::Context,
        params: &CleanBuildParams,
    ) -> Result<CleanBuildResponse, String> {
        let orchestrators = self.build_orchestrators.lock().unwrap();
        let Some(orchestrator) = orchestrators.get(&params.build_orchestrator_id) else {
            return Err(format!(
                "build orchestrator not found while cleaning {}",
                params.project
            ));
        };
        let result = orchestrator.clean(&params.project);
        Ok(CleanBuildResponse {
            status: result.result.status,
            diagnostics: build_diagnostic_responses(&result.errors),
            statistics: result.statistics,
            files_deleted: result.files_to_delete,
        })
    }

    /// `s.handleCleanReferences` (session.go:1935).
    pub(crate) fn handle_clean_references(
        &self,
        _ctx: &core_::context::Context,
        params: &CleanBuildParams,
    ) -> Result<CleanBuildResponse, String> {
        let orchestrators = self.build_orchestrators.lock().unwrap();
        let Some(orchestrator) = orchestrators.get(&params.build_orchestrator_id) else {
            return Err(format!(
                "build orchestrator not found while cleaning references for {}",
                params.project
            ));
        };
        let result = orchestrator.clean_references(&params.project);
        Ok(CleanBuildResponse {
            status: result.result.status,
            diagnostics: build_diagnostic_responses(&result.errors),
            statistics: result.statistics,
            files_deleted: result.files_to_delete,
        })
    }

    /// `s.getBuildSys` (session.go:1950).
    fn get_build_sys(&self, params: &CreateBuildOrchestratorParams) -> Arc<dyn tsc::System> {
        let mut current_directory = params.cwd.clone();
        if current_directory.as_string().is_empty() {
            current_directory = self.get_current_directory();
        }
        Arc::new(ApiBuildSystem {
            session: self.self_arc(),
            current_directory,
            start: SystemTime::now(),
            diagnostic_registry: Arc::new(tsc::DiagnosticRegistry::default()),
        })
    }

    /// `s.createSnapshotResponse` (session.go:5096) — `base` is `None` for
    /// createSnapshot (all loaded projects) and `Some` for diffs against a
    /// retained base.
    fn create_snapshot_response(
        &self,
        snapshot: &project::snapshot::Snapshot,
        base: Option<&project::snapshot::Snapshot>,
        request: Option<&SnapshotRequestChangesParams>,
    ) -> CreateSnapshotResponse {
        let operation = self.create_snapshot_operation_response(snapshot, request);
        let Some(base) = base else {
            let projects = snapshot.project_collection.projects();
            let mut project_responses = Vec::with_capacity(projects.len());
            for proj in &projects {
                if proj.command_line.is_some() {
                    project_responses.push(project_response(proj));
                }
            }
            return CreateSnapshotResponse {
                snapshot: Self::snapshot_handle(snapshot),
                projects: project_responses,
                changes: None,
                operation: Some(operation),
            };
        };

        let project_responses = RefCell::new(Vec::new());
        let prev_projects = base.project_collection.projects_by_id();
        let next_projects = snapshot.project_collection.projects_by_id();
        diff_project_collections(
            &prev_projects,
            &next_projects,
            |_id, proj| {
                if proj.command_line.is_some() {
                    project_responses.borrow_mut().push(project_response(proj));
                }
            },
            |_id, _proj| {},
            |_id, _old_proj, new_proj| {
                if new_proj.command_line.is_some() {
                    project_responses.borrow_mut().push(project_response(new_proj));
                }
            },
        );
        let project_responses = project_responses.into_inner();
        CreateSnapshotResponse {
            snapshot: Self::snapshot_handle(snapshot),
            projects: project_responses,
            changes: Some(compute_snapshot_changes(base, snapshot)),
            operation: Some(operation),
        }
    }

    /// `s.createSnapshotOperationResponse` (session.go:5132).
    fn create_snapshot_operation_response(
        &self,
        snapshot: &project::snapshot::Snapshot,
        request: Option<&SnapshotRequestChangesParams>,
    ) -> SnapshotOperationResponse {
        let mut operation = SnapshotOperationResponse::default();
        let Some(request) = request else {
            return operation;
        };

        // PORT: Go checks `request.CreatePrograms != nil`; serde's
        // `Vec::new` default merges absent and `[]` — an explicit empty
        // array yields `createdPrograms` omitted rather than `[]`.
        if !request.create_programs.is_empty() {
            let created_programs = snapshot.created_programs();
            if created_programs.len() != request.create_programs.len() {
                panic!("created program result count does not match request");
            }
            let mut results = Vec::with_capacity(created_programs.len());
            for created_program in created_programs {
                let Some(program_id) = created_program.id().synthetic() else {
                    panic!("created program has non-synthetic project ID");
                };
                results.push(program_id);
            }
            operation.created_programs = Some(results);
        }

        if !request.open_files.is_empty() {
            let mut results = Vec::with_capacity(request.open_files.len());
            for file in &request.open_files {
                let project =
                    snapshot.get_default_project(&file.to_uri(&self.get_current_directory()));
                let Some(project) = project else {
                    panic!(
                        "no project found for opened file {}",
                        self.to_file_name(file).as_string()
                    );
                };
                results.push(OpenedFileOperationResult {
                    project: project.id().clone(),
                });
            }
            operation.opened_files = Some(results);
        }
        operation
    }
}

impl LanguageServerSnapshotUpdate {
    /// `(u *languageServerSnapshotUpdate) commit` (session.go:1706) —
    /// adopts the new open state and synchronizes the synthetic-program
    /// ownership set after a successful API update.
    fn commit(&self, state: &mut LanguageServerState, snapshot: &project::snapshot::Snapshot) {
        state.open_projects = self.open_state.open_projects.clone();
        state.open_files = self.open_state.open_files.clone();
        if let Some(remove_programs) = &self.request.remove_programs {
            for program_id in remove_programs.keys().iter() {
                state.created_programs.delete(program_id);
            }
        }
        for program in snapshot.created_programs() {
            let Some(program_id) = program.id().synthetic() else {
                panic!(
                    "created program has non-synthetic project ID: {}",
                    program.id()
                );
            };
            state.created_programs.add(program_id);
        }
    }
}

impl Default for SnapshotOpenState {
    fn default() -> Self {
        SnapshotOpenState {
            open_projects: collections::Set::new(),
            open_files: collections::Set::new(),
        }
    }
}
