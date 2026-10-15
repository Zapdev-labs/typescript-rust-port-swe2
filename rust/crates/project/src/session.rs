// Ported from tsc/internal/project/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `Session` and its lifecycle: file events, snapshot updates, schedulers
// (diagnostics refresh, idle, warm auto-import, telemetry), watchers,
// ATA triggering, language-service accessors, and diagnostics publish.

use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use tsc_contentmapper::{Host as ContentMapperHostTrait, HostOptions, Mapper, Spawner, Timings};
use tsc_core::context::Context;
use tsc_lsproto::PositionEncodingKind;
use tsc_project_logging::Logger;
use tsc_tspath::RootedDirectoryPath;
use tsc_vfs::Vfs;

use crate::ata::NpmExecutor;
use crate::checkerpool::CheckerPoolOptions;
use crate::client::Client;
use crate::parsecache::{ContentMappedParseCache, ParseCache};

/// `UpdateReason` (session.go).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum UpdateReason {
    #[default]
    Unknown,
    DidOpenFile,
    DidCloseFile,
    DidChangeCompilerOptionsForInferredProjects,
    RequestedLanguageServicePendingChanges,
    RequestedLanguageServiceProjectNotLoaded,
    RequestedLanguageServiceForFileNotOpen,
    RequestedLanguageServiceProjectDirty,
    RequestedLoadProjectTree,
    RequestedLanguageServiceWithAutoImports,
    IdleCleanDiskCache,
    DidChangeConfigFile,
    DidChangeContentMapperContributions,
}

/// `ErrNoProjectForUnknownScriptKind` identifies requests for otherwise
/// unsupported files (Go `errors.New`; compared by message string).
pub const ERR_NO_PROJECT_FOR_UNKNOWN_SCRIPT_KIND: &str =
    "no project for unknown script kind";

/// `ContentMapperContributions` (session.go).
#[derive(Clone, Default)]
pub struct ContentMapperContributions {
    pub mappers: Vec<Arc<Mapper>>,
    pub extensions: Vec<String>,
}

/// `SessionOptions` are the immutable initialization options for a session.
/// Snapshots may reference them as a pointer since they never change
/// (Go `*SessionOptions` → `Arc<SessionOptions>`).
#[derive(Clone, Default)]
pub struct SessionOptions {
    pub current_directory: RootedDirectoryPath,
    pub default_library_path: RootedDirectoryPath,
    pub typings_location: RootedDirectoryPath,
    pub position_encoding: PositionEncodingKind,
    pub watch_enabled: bool,
    pub logging_enabled: bool,
    pub telemetry_enabled: bool,
    pub push_diagnostics_enabled: bool,
    /// `RunExternalCode` allows configured content mappers to run their
    /// (external) processes, gated on workspace trust by the client. It
    /// corresponds to the `--runExternalCode` CLI flag.
    pub run_external_code: bool,
    pub debounce_delay: Duration,
    pub checker_pool_options: CheckerPoolOptions,
}

/// `SessionInit` (session.go) — inputs shared by `Session`/`NewSnapshotHost`.
pub struct SessionInit {
    pub background_ctx: Context,
    /// `Options *SessionOptions` — the pointer is shared, hence `Arc`.
    pub options: Arc<SessionOptions>,
    pub fs: Arc<dyn Vfs>,
    /// `Client` — Go's nil-able interface.
    pub client: Option<Arc<dyn Client>>,
    /// `Logger` — Go's nil-able interface.
    pub logger: Option<Arc<dyn Logger>>,
    /// `NpmExecutor` — Go's nil-able interface.
    pub npm_executor: Option<Arc<dyn NpmExecutor>>,
    /// `Spawner` launches content mapper processes. It is `None` when the
    /// host cannot spawn processes (Go nil).
    pub spawner: Option<Arc<dyn Spawner>>,
    /// `ContentMapperLogger` — Go `contentmapper.Logger` (func type → `Arc`).
    pub content_mapper_logger: Option<tsc_contentmapper::Logger>,
    /// `ParseCache` — `None` → `NewParseCache` (Go nil). `Rc` because the
    /// Go `*ParseCache` pointer is shared between the host, builders, and
    /// auto-import leases (the cache itself is `!Clone`).
    pub parse_cache: Option<Rc<ParseCache>>,
    /// `ContentMappedParseCache` — `None` → `NewContentMappedParseCache`.
    pub content_mapped_parse_cache: Option<Rc<ContentMappedParseCache>>,
}

/// `newContentMapperHost` creates the session's shared content mapper host
/// when the workspace is trusted and a spawner is available; otherwise it
/// returns `None`, and configured content mappers are rejected by the
/// config-file gate.
pub fn new_content_mapper_host(init: &SessionInit) -> Option<Arc<dyn ContentMapperHostTrait>> {
    if !init.options.run_external_code || init.spawner.is_none() {
        return None;
    }
    let diagnostic_locale = init
        .client
        .as_ref()
        .map(|c| c.get_locale())
        .unwrap_or(tsc_locale::DEFAULT);
    Some(tsc_contentmapper::new_host_with_options(
        &init.background_ctx,
        init.spawner.clone().unwrap(),
        diagnostic_locale,
        HostOptions {
            logger: init.content_mapper_logger.clone(),
        },
    ))
}

// ============================================================================
// Session — ported from tsc/internal/project/session.go @ ec47d33
// ============================================================================


/// `ClientError` — Go `error` results on the `Client` interface.
type ClientError = Box<dyn std::error::Error + Send + Sync>;
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Condvar, Mutex, RwLock};
use std::time::Instant;

use rustc_hash::FxHashMap;
use tsc_collections::{Set, SyncSet};
use tsc_core::context::CancelFunc;
use tsc_core::options_generated::{CompilerOptions, JsxEmit, ModuleKind, ModuleResolutionKind, ScriptTarget};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::tristate::Tristate;
use tsc_ls::languageservice::{LanguageService, new_language_service};
use tsc_lsconv::diagnostic_to_lsp_push;
use tsc_compiler::program::Program;
use tsc_ls::autoimport::registry::ProjectId;
use tsc_lsproto::{
    DocumentUri, FileChangeType, FileEvent, FileSystemWatcher,
    PerformanceStatsTelemetryEvent, PerformanceStatsTelemetryMeasurements,
    ProjectInfoTelemetryEvent, ProjectInfoTelemetryMeasurements,
    PublishDiagnosticsParams, TelemetryEvent,
    TextDocumentContentChangePartialOrWholeDocument, get_client_capabilities,
};
use tsc_project_logging::LogTree;
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_tspath::{CaseSensitivity, PathKey};

use crate::ata::{TypingsInstallRequest, new_typings_installer, TypingsInstaller, TypingsInstallerOptions};
use crate::background::{Queue, new_queue};
use crate::configfileregistry::ConfigFileEntry;
use crate::filechange::{FileChange, FileChangeKind, FileChangeSummary};
use crate::overlayfs::{LayeredFileSystem, Overlay, OverlayFs, new_overlay_fs};
use crate::project::{Id, Kind, ProgramUpdateKind, Project};
use crate::snapshot::{
    AtaStateChange, ProjectTreeRequest, ResourceRequest, Snapshot, SnapshotChange,
};
use crate::snapshotfs::{is_node_modules_path, is_relevant_extension};
use crate::snapshothost::{SnapshotHost, new_snapshot_host};
use crate::watch::{
    WatchedFiles, WatcherId, file_system_watcher_glob_string, new_watch_registry, WatchRegistry,
};

/// `watchRequestTimeout` — maximum time to wait for the client to respond to
/// a WatchFiles or UnwatchFiles request while holding the watches mutex.
const WATCH_REQUEST_TIMEOUT: Duration = Duration::from_secs(1);
/// `idleCacheCleanDelay`.
const IDLE_CACHE_CLEAN_DELAY: Duration = Duration::from_secs(30);
/// `performanceTelemetryInterval`.
const PERFORMANCE_TELEMETRY_INTERVAL: Duration = Duration::from_secs(5 * 60);

/// `sendShared<T>` asserts `Send` for `!Send` values moved onto a background
/// worker — Go's goroutines share `*Snapshot`/`Rc`-equivalent pointers
/// freely; the values moved this way are read under the same lock regime Go
/// holds (see the `Session` `unsafe impl`s below).
pub(crate) struct SendShared<T>(T);
impl<T> SendShared<T> {
    /// Method-call capture keeps the wrapper whole under edition-2021
    /// disjoint field capture (a `shared.0` projection would capture just
    /// the `!Send` payload).
    fn into_inner(self) -> T {
        self.0
    }
}
#[allow(unsafe_code)]
unsafe impl<T> Send for SendShared<T> {}

/// `scheduledTask` — a cancellable, generation-stamped debounce slot
/// (`scheduledSnapshotUpdateCancel`/`diagnosticsRefreshCancel` +
/// their generation counters).
#[derive(Default)]
struct ScheduledTask {
    cancel: Option<CancelFunc>,
    generation: u64,
}

/// `idleCacheClean*` — the resettable idle disk-cache-clean timer state.
#[derive(Default)]
struct IdleCacheClean {
    /// `idleCacheCleanTimer` — the pending timer's context, cancelled on
    /// reschedule (`time.Timer.Stop` semantics).
    cancel: Option<CancelFunc>,
    generation: u64,
    closed: bool,
}

/// `idleCacheCleanWG` — a `sync.WaitGroup` tracking in-flight timer runs so
/// `Close` can wait for a running clean without blocking on the timer.
#[derive(Default)]
struct IdleCacheCleanWg {
    count: Mutex<usize>,
    idle: Condvar,
}

impl IdleCacheCleanWg {
    fn add(&self) {
        *self.count.lock().unwrap() += 1;
    }
    fn done(&self) {
        let mut count = self.count.lock().unwrap();
        *count -= 1;
        if *count == 0 {
            self.idle.notify_all();
        }
    }
    fn wait(&self) {
        let mut count = self.count.lock().unwrap();
        while *count != 0 {
            count = self.idle.wait(count).unwrap();
        }
    }
}

/// `userConfigState` — `workspaceUserPreferences` + `pendingUserConfigChanges`
/// under `userConfigRWMu`.
#[derive(Default)]
struct UserConfigState {
    workspace_user_preferences: UserPreferences,
    pending_user_config_changes: bool,
}

/// `contentMapperRegistration*` — the last registered extension set and the
/// snapshot it came from, so out-of-order background tasks can't regress it.
#[derive(Default)]
struct ContentMapperRegistration {
    extensions: Vec<String>,
    snapshot_id: u64,
}

/// `type Session struct` — manages the state of an LSP session: receives
/// textDocument events and LanguageService requests and processes them into
/// immutable snapshots.
pub struct Session {
    /// Go embeds `*SnapshotHost` — a `Deref` impl provides the same
    /// pass-through member access.
    /// `pub(crate)` — `api.rs`'s `TryAdoptSnapshotInBackground` calls
    /// `s.RetainSnapshot` (same-package access in Go).
    pub(crate) host: Arc<SnapshotHost>,
    options: Arc<SessionOptions>,
    logger: Arc<dyn Logger>,
    /// `backgroundCtx`/`backgroundCancel` — the session-scoped context all
    /// background tasks derive from.
    background_ctx: Context,
    background_cancel: CancelFunc,
    case_sensitivity: CaseSensitivity,
    client: Option<Arc<dyn Client>>,
    start_time: Instant,
    npm_executor: Option<Arc<dyn NpmExecutor>>,
    /// `fs` — the session-level `*overlayFS` layered over the host FS.
    fs: Arc<OverlayFs>,
    /// `contentMapperTimings` — cumulative host timings at the most recent
    /// snapshot adoption.
    content_mapper_timings: Mutex<tsc_contentmapper::Timings>,

    content_mapper_registration: Mutex<ContentMapperRegistration>,

    /// `initialUserPreferences` — read-only after initialization.
    initial_user_preferences: Mutex<UserPreferences>,
    /// `workspaceUserPreferences` + `pendingUserConfigChanges`
    /// under `userConfigRWMu`.
    user_config: RwLock<UserConfigState>,
    /// `configureMu` — serializes `Configure`.
    configure_mu: Mutex<()>,
    compiler_options_for_inferred_projects: Mutex<Option<Arc<CompilerOptions>>>,
    typings_installer: Option<Arc<TypingsInstaller>>,
    background_queue: Queue,

    /// `snapshot` under `snapshotMu`.
    snapshot: RwLock<Option<Arc<Snapshot>>>,
    /// `snapshotUpdateMu` — serializes snapshot updates.
    /// `pub(crate)` — `api.rs`'s `APIUpdate` shares the package's private
    /// fields like Go's same-package access.
    pub(crate) snapshot_update_mu: Mutex<()>,

    /// `scheduledSnapshotUpdateCancel`/`Generation` under
    /// `scheduledSnapshotUpdateMu`.
    scheduled_snapshot_update: Mutex<ScheduledTask>,

    /// `pendingFileChanges` under `pendingFileChangesMu`.
    pending_file_changes: Mutex<Vec<FileChange>>,
    /// `pendingATAChanges` under `pendingATAChangesMu`.
    pending_ata_changes: Mutex<FxHashMap<Id, AtaStateChange>>,

    /// `diagnosticsRefreshCancel`/`Generation` under `diagnosticsRefreshMu`.
    diagnostics_refresh: Mutex<ScheduledTask>,
    /// `warmAutoImportCancel` under `warmAutoImportMu`.
    warm_auto_import_cancel: Mutex<Option<Arc<dyn Fn() + Send + Sync>>>,

    idle_cache_clean: Mutex<IdleCacheClean>,
    idle_cache_clean_wg: IdleCacheCleanWg,

    /// `performanceTelemetryCancel`.
    performance_telemetry_cancel: Mutex<Option<CancelFunc>>,
    /// `seenProjects`.
    seen_projects: SyncSet<Id>,

    /// `watches`.
    watches: WatchRegistry,

    /// `globalDiagPublishPending`.
    global_diag_publish_pending: AtomicBool,
}

// SAFETY: Go shares `*Session` across goroutines; every field is guarded by
// the same mutex regime Go uses (`snapshotMu`, `pendingFileChangesMu`, the
// various scheduler mutexes) or is immutable after construction. The
// `Rc`-based `Snapshot`/`Project`/`Program` graph stored under `snapshot` is
// accessed under those same locks — identical to the pointer sharing Go does
// between the session goroutine and background tasks.
#[allow(unsafe_code)]
unsafe impl Send for Session {}
#[allow(unsafe_code)]
unsafe impl Sync for Session {}

/// `func NewSession(init *SessionInit) *Session`.
pub fn new_session(init: SessionInit) -> Arc<Session> {
    let host = new_snapshot_host(&init);
    let (background_ctx, background_cancel) = init.background_ctx.with_cancel();
    let session_logger: Arc<dyn Logger> = init
        .logger
        .clone()
        .unwrap_or_else(|| Arc::new(tsc_project_logging::new_nop_logger()));
    let snapshot = host.new_root_snapshot_with(
        0,
        get_client_capabilities(&init.background_ctx)
            .workspace
            .did_change_watched_files
            .relative_pattern_support,
    );
    let overlay_fs = Arc::new(new_overlay_fs(
        host.fs.clone(),
        None,
        FxHashMap::default(),
        init.options.position_encoding.clone(),
    ));
    let typings_installer = if !init.options.typings_location.as_string().is_empty() {
        init.npm_executor.as_ref().map(|executor| {
            Arc::new(new_typings_installer(
                &TypingsInstallerOptions {
                    typings_location: init.options.typings_location.clone(),
                    throttle_limit: 5,
                },
                overlay_fs.clone() as Arc<dyn Vfs>,
                executor.clone(),
            ))
        })
    } else {
        None
    };
    Arc::new(Session {
        case_sensitivity: host.case_sensitivity,
        fs: overlay_fs,
        options: init.options.clone(),
        logger: session_logger,
        background_ctx,
        background_cancel,
        client: init.client.clone(),
        start_time: Instant::now(),
        npm_executor: init.npm_executor.clone(),
        content_mapper_timings: Mutex::new(
            host.content_mapper_host
                .as_ref()
                .map(|h| h.timings())
                .unwrap_or_default(),
        ),
        content_mapper_registration: Mutex::new(ContentMapperRegistration::default()),
        initial_user_preferences: Mutex::new(tsc_lsutil::new_default_user_preferences()),
        user_config: RwLock::new(UserConfigState {
            workspace_user_preferences: tsc_lsutil::new_default_user_preferences(),
            pending_user_config_changes: false,
        }),
        configure_mu: Mutex::new(()),
        compiler_options_for_inferred_projects: Mutex::new(None),
        typings_installer,
        background_queue: new_queue(),
        snapshot: RwLock::new(Some(snapshot)),
        snapshot_update_mu: Mutex::new(()),
        scheduled_snapshot_update: Mutex::new(ScheduledTask::default()),
        pending_file_changes: Mutex::new(Vec::new()),
        pending_ata_changes: Mutex::new(FxHashMap::default()),
        diagnostics_refresh: Mutex::new(ScheduledTask::default()),
        warm_auto_import_cancel: Mutex::new(None),
        idle_cache_clean: Mutex::new(IdleCacheClean::default()),
        idle_cache_clean_wg: IdleCacheCleanWg::default(),
        performance_telemetry_cancel: Mutex::new(None),
        seen_projects: SyncSet::new(),
        watches: new_watch_registry(),
        global_diag_publish_pending: AtomicBool::new(false),
        host,
    })
}

/// Go's embedded `*SnapshotHost` — `s.parseCache`, `s.fs` (host FS),
/// `s.contentMapperHost`, `s.programCounter`, etc. resolve through `Deref`.
impl Deref for Session {
    type Target = SnapshotHost;
    fn deref(&self) -> &SnapshotHost {
        &self.host
    }
}

impl Session {
    /// `s.FS()` — the session's overlay filesystem.
    pub fn fs(&self) -> &Arc<OverlayFs> {
        &self.fs
    }

    /// `s.GetCurrentDirectory` — implements `module.ResolutionHost`.
    pub fn get_current_directory(&self) -> RootedDirectoryPath {
        self.options.current_directory.clone()
    }

    /// `s.DefaultLibraryPath`.
    pub fn default_library_path(&self) -> RootedDirectoryPath {
        self.options.default_library_path.clone()
    }

    /// `s.Config` — a copy of the current configuration.
    pub fn config(&self) -> UserPreferences {
        self.user_config
            .read()
            .unwrap()
            .workspace_user_preferences
            .clone()
    }

    /// `s.backgroundContext`.
    fn background_context(&self) -> Context {
        self.with_current_locale(self.background_ctx.clone())
    }

    /// `s.WithCurrentLocale`.
    pub fn with_current_locale(&self, mut ctx: Context) -> Context {
        if let Some(client) = &self.client {
            tsc_locale::with_locale(&mut ctx, client.get_locale());
        }
        ctx
    }

    /// `s.Configure`.
    pub fn configure(self: &Arc<Self>, config: UserPreferences) {
        let _configure_guard = self.configure_mu.lock().unwrap();
        let old_config = {
            let mut user_config = self.user_config.write().unwrap();
            user_config.pending_user_config_changes = true;
            std::mem::replace(&mut user_config.workspace_user_preferences, config.clone())
        };

        if !config.locale.is_empty() && let Some(client) = &self.client {
            let old_locale = client.get_locale();
            client.set_locale(&config.locale);
            let new_locale = client.get_locale();
            if old_locale != new_locale && let Some(host) = &self.content_mapper_host {
                host.set_locale(new_locale);
            }
        }

        // Tell the client to re-request certain commands depending on user
        // preference changes.
        self.refresh_inlay_hints_if_needed(&old_config, &config);
        self.refresh_code_lens_if_needed(&old_config, &config);
        self.refresh_diagnostics_if_needed(&old_config, &config);
        self.refresh_ata_if_needed(&old_config, &config);
    }

    /// `s.InitializeWithUserConfig`.
    pub fn initialize_with_user_config(self: &Arc<Self>, config: UserPreferences) {
        *self.initial_user_preferences.lock().unwrap() = config.clone();
        self.configure(config);
    }

    /// `s.DidOpenFile`.
    pub fn did_open_file(
        self: &Arc<Self>,
        ctx: &Context,
        uri: DocumentUri,
        version: i32,
        content: String,
        language_kind: tsc_lsproto::LanguageKind,
    ) {
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
        self.cancel_scheduled_snapshot_update();
        let _update_guard = self.snapshot_update_mu.lock().unwrap();
        let (changes, overlays) = {
            let mut pending = self.pending_file_changes.lock().unwrap();
            pending.push(FileChange {
                kind: FileChangeKind::Open,
                uri: uri.clone(),
                version,
                content,
                language_kind,
                ..Default::default()
            });
            self.flush_changes_locked(ctx, &mut pending)
        };
        self.update_snapshot(
            ctx,
            overlays,
            SnapshotChange {
                reason: UpdateReason::DidOpenFile,
                file_changes: changes,
                documents: vec![uri],
                ..Default::default()
            },
            false,
        );
    }

    /// `s.SetContentMapperContributions` — atomically replaces
    /// extension-provided inferred-project mappers and discovers configured
    /// projects for matching open documents.
    pub fn set_content_mapper_contributions(
        self: &Arc<Self>,
        ctx: &Context,
        contributions: ContentMapperContributions,
        document_uris: Vec<DocumentUri>,
    ) {
        if !self.options.run_external_code {
            return;
        }
        self.cancel_scheduled_snapshot_update();
        let _update_guard = self.snapshot_update_mu.lock().unwrap();
        let (changes, overlays) = {
            let mut pending = self.pending_file_changes.lock().unwrap();
            self.flush_changes_locked(ctx, &mut pending)
        };
        self.update_snapshot(
            ctx,
            overlays,
            SnapshotChange {
                reason: UpdateReason::DidChangeContentMapperContributions,
                file_changes: changes,
                content_mapper_contributions: Some(contributions),
                configured_project_documents: document_uris,
                ..Default::default()
            },
            false,
        );
        let snapshot = self.snapshot();
        let _ = self.update_content_mapper_registrations(ctx, &snapshot);
    }

    /// `s.DidCloseFile`.
    pub fn did_close_file(self: &Arc<Self>, ctx: &Context, uri: DocumentUri) {
        let _ = ctx;
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
        self.pending_file_changes
            .lock()
            .unwrap()
            .push(FileChange {
                kind: FileChangeKind::Close,
                uri,
                ..Default::default()
            });
        self.schedule_snapshot_update(UpdateReason::DidCloseFile);
    }

    /// `s.DidChangeFile`.
    pub fn did_change_file(
        self: &Arc<Self>,
        _ctx: &Context,
        uri: DocumentUri,
        version: i32,
        changes: Vec<TextDocumentContentChangePartialOrWholeDocument>,
    ) {
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
        self.pending_file_changes
            .lock()
            .unwrap()
            .push(FileChange {
                kind: FileChangeKind::Change,
                uri: uri.clone(),
                version,
                changes,
                ..Default::default()
            });

        // Editing a content-mapped file changes the program like any source
        // edit, but the client's pull-diagnostics machinery won't re-request
        // diagnostics for dependent files — prompt a workspace refresh
        // without the debounce. Ordinary source files are handled entirely
        // client-side, so cancel any pending refresh as before.
        if self.is_content_mapper_file(&uri) {
            self.schedule_diagnostics_refresh(Duration::ZERO);
        } else {
            self.cancel_diagnostics_refresh();
        }
    }

    /// `s.isContentMapperFile`.
    fn is_content_mapper_file(&self, uri: &DocumentUri) -> bool {
        let snapshot = self.snapshot();
        let configured = snapshot.config_file_registry.content_mappers();
        let mut extensions = configured.extensions.clone();
        extensions.extend(
            snapshot
                .inferred_project_content_mapper_extensions
                .iter()
                .cloned(),
        );
        let extensions: Vec<&str> = extensions.iter().map(|s| s.as_str()).collect();
        uri.file_name().extension_is_one_of(&extensions)
    }

    /// `s.DidSaveFile`.
    pub fn did_save_file(self: &Arc<Self>, _ctx: &Context, uri: DocumentUri) {
        self.schedule_idle_cache_clean();
        self.pending_file_changes
            .lock()
            .unwrap()
            .push(FileChange {
                kind: FileChangeKind::Save,
                uri,
                ..Default::default()
            });
    }

    /// `s.DidChangeWatchedFiles`.
    pub fn did_change_watched_files(self: &Arc<Self>, _ctx: &Context, changes: &[FileEvent]) {
        let mut file_changes = Vec::with_capacity(changes.len());
        let mut has_relevant_change = false;
        let mut has_config_change = false;
        let snapshot = self.snapshot();
        let config_file_registry = &snapshot.config_file_registry;
        let (content_mapper_extensions, content_mapper_watched_files) =
            snapshot.content_mapper_watch_state();
        let content_mapper_extension_refs: Vec<&str> = content_mapper_extensions
            .iter()
            .map(|e| e.as_str())
            .collect();
        for change in changes {
            let kind = match change.type_ {
                t if t == FileChangeType::Created => FileChangeKind::WatchCreate,
                t if t == FileChangeType::Changed => FileChangeKind::WatchChange,
                t if t == FileChangeType::Deleted => FileChangeKind::WatchDelete,
                _ => continue, // Ignore unknown change types.
            };
            file_changes.push(FileChange {
                kind,
                uri: change.uri.clone(),
                ..Default::default()
            });

            if !has_config_change
                && config_file_registry
                    .is_tracked(&change.uri.path_key(self.case_sensitivity))
            {
                has_config_change = true;
            }

            if !has_relevant_change {
                let file_path = change.uri.path();
                let path = self
                    .case_sensitivity
                    .path_key(&file_path)
                    .remove_trailing_directory_separator();
                if content_mapper_watched_files.has(&path) {
                    has_relevant_change = true;
                    continue;
                }
                let extension = path.extension();
                if extension.is_empty() {
                    // Extensionless paths might be directories. For
                    // creations/changes, check the file system; for deletions,
                    // consult the current snapshot cache.
                    if kind != FileChangeKind::WatchDelete {
                        has_relevant_change = self.fs.directory_exists(
                            &tsc_tspath::rooted_directory_path_from_path(file_path),
                        );
                    } else {
                        let snapshot_guard = self.snapshot.read().unwrap();
                        let snapshot = snapshot_guard.as_ref().unwrap();
                        if snapshot.fs.cache_directories.contains_key(&path)
                            || snapshot.has_overlay_within(&path)
                            || is_node_modules_path(&path)
                        {
                            has_relevant_change = true;
                        }
                    }
                } else if is_relevant_extension(extension)
                    || path.extension_is_one_of(&content_mapper_extension_refs)
                {
                    has_relevant_change = true;
                }
            }
        }

        self.pending_file_changes
            .lock()
            .unwrap()
            .extend(file_changes);

        if has_relevant_change {
            // Schedule a debounced diagnostics refresh only for paths that can
            // affect the TypeScript program.
            self.schedule_diagnostics_refresh(self.options.debounce_delay);
        }
        if has_config_change {
            // Config file diagnostics are pushed on snapshot updates rather
            // than pulled, so they must not depend on the client re-pulling
            // diagnostics in response to the refresh request above.
            self.schedule_snapshot_update(UpdateReason::DidChangeConfigFile);
        }
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
    }

    /// `s.DidChangeCompilerOptionsForInferredProjects`.
    pub fn did_change_compiler_options_for_inferred_projects(
        self: &Arc<Self>,
        ctx: &Context,
        options: Arc<CompilerOptions>,
    ) {
        *self.compiler_options_for_inferred_projects.lock().unwrap() = Some(options.clone());
        self.update_snapshot(
            ctx,
            self.fs.overlays(),
            SnapshotChange {
                reason: UpdateReason::DidChangeCompilerOptionsForInferredProjects,
                compiler_options_for_inferred_projects: Some(options),
                ..Default::default()
            },
            false,
        );
    }

    /// `s.ScheduleDiagnosticsRefresh`.
    pub fn schedule_diagnostics_refresh_default(self: &Arc<Self>) {
        self.schedule_diagnostics_refresh(self.options.debounce_delay);
    }

    /// `s.scheduleDiagnosticsRefresh` — schedules a coalesced workspace
    /// diagnostics refresh after `delay`. A delay of 0 refreshes as soon as
    /// the background queue runs the task.
    pub fn schedule_diagnostics_refresh(self: &Arc<Self>, delay: Duration) {
        let generation = {
            let mut refresh = self.diagnostics_refresh.lock().unwrap();
            if refresh.cancel.is_some() {
                refresh.cancel.as_ref().unwrap().cancel();
                self.logger.log(format_args!("Delaying scheduled diagnostics refresh..."));
            } else {
                self.logger.log(format_args!("Scheduling new diagnostics refresh..."));
            }
            let (debounce_ctx, cancel) = self.background_context().with_cancel();
            refresh.generation += 1;
            let generation = refresh.generation;
            refresh.cancel = Some(cancel.clone());
            let me = Arc::downgrade(self);
            self.background_queue.enqueue(&debounce_ctx, move |ctx| {
                let Some(me) = me.upgrade() else { return };
                defer_cancel(cancel);
                if delay > Duration::ZERO {
                    // Wait out the debounce window; a newer event cancels this one.
                    if ctx.wait_cancelled_timeout(delay) {
                        return;
                    }
                } else if ctx.is_cancelled() {
                    return;
                }

                {
                    let mut refresh = me.diagnostics_refresh.lock().unwrap();
                    if refresh.generation != generation {
                        return;
                    }
                    refresh.cancel = None;
                }

                if me.options.logging_enabled {
                    me.logger.log(format_args!("Running scheduled diagnostics refresh"));
                }
                let ctx = me.background_context();
                if let Some(client) = &me.client
                    && let Err(err) = client.refresh_diagnostics(&ctx)
                    && me.options.logging_enabled
                {
                    me.logger
                        .logf(format_args!("Error refreshing diagnostics: {}", err));
                }
            });
            generation
        };
        let _ = generation;
    }

    /// `s.cancelDiagnosticsRefresh`.
    fn cancel_diagnostics_refresh(&self) {
        let mut refresh = self.diagnostics_refresh.lock().unwrap();
        if let Some(cancel) = refresh.cancel.take() {
            cancel.cancel();
            self.logger
                .log(format_args!("Canceled scheduled diagnostics refresh"));
            refresh.generation += 1;
        }
    }

    /// `s.ScheduleSnapshotUpdate`.
    pub fn schedule_snapshot_update(self: &Arc<Self>, reason: UpdateReason) {
        let mut scheduled = self.scheduled_snapshot_update.lock().unwrap();
        if let Some(cancel) = &scheduled.cancel {
            cancel.cancel();
            if self.options.logging_enabled {
                self.logger
                    .log(format_args!("Delaying scheduled snapshot update..."));
            }
        } else if self.options.logging_enabled {
            self.logger
                .log(format_args!("Scheduling new snapshot update..."));
        }

        let (debounce_ctx, cancel) = self.background_context().with_cancel();
        scheduled.generation += 1;
        let generation = scheduled.generation;
        scheduled.cancel = Some(cancel.clone());
        let me = Arc::downgrade(self);
        self.background_queue.enqueue(&debounce_ctx, move |ctx| {
            let Some(me) = me.upgrade() else { return };
            defer_cancel(cancel);
            // Sleep for the debounce delay.
            if ctx.wait_cancelled_timeout(me.options.debounce_delay) {
                return;
            }

            {
                let mut scheduled = me.scheduled_snapshot_update.lock().unwrap();
                if scheduled.generation != generation {
                    return;
                }
                scheduled.cancel = None;
            }

            if me.options.logging_enabled {
                me.logger
                    .log(format_args!("Running scheduled snapshot update"));
            }

            let _update_guard = me.snapshot_update_mu.lock().unwrap();
            let (file_changes, overlays, ata_changes, new_config) = me.flush_changes(ctx);
            if file_changes.is_empty() && ata_changes.is_empty() && new_config.is_none() {
                return;
            }
            me.update_snapshot(
                ctx,
                overlays,
                SnapshotChange {
                    reason,
                    file_changes,
                    ata_changes,
                    new_config,
                    ..Default::default()
                },
                false,
            );
        });
    }

    /// `s.cancelScheduledSnapshotUpdate`.
    /// `pub(crate)` — `api.rs` (same package in Go).
    pub(crate) fn cancel_scheduled_snapshot_update(&self) {
        let mut scheduled = self.scheduled_snapshot_update.lock().unwrap();
        if let Some(cancel) = scheduled.cancel.take() {
            cancel.cancel();
            if self.options.logging_enabled {
                self.logger
                    .log(format_args!("Canceled scheduled snapshot update"));
            }
            scheduled.generation += 1;
        }
    }

    /// `s.cancelWarmAutoImportCache`.
    fn cancel_warm_auto_import_cache(&self) {
        let mut warm = self.warm_auto_import_cancel.lock().unwrap();
        if let Some(cancel) = warm.take() {
            cancel();
        }
    }

    /// `s.scheduleIdleCacheClean` — resets the 30s idle disk-cache timer.
    fn schedule_idle_cache_clean(self: &Arc<Self>) {
        let mut idle = self.idle_cache_clean.lock().unwrap();
        if idle.closed {
            return;
        }
        if let Some(cancel) = idle.cancel.take() {
            cancel.cancel();
            self.idle_cache_clean_wg.done();
        }

        self.idle_cache_clean_wg.add();
        let (timer_ctx, cancel) = self.background_ctx.with_cancel();
        idle.generation += 1;
        let generation = idle.generation;
        idle.cancel = Some(cancel);

        let me = Arc::downgrade(self);
        std::thread::spawn(move || {
            // `time.AfterFunc` — wait for the delay or cancellation.
            if timer_ctx.wait_cancelled_timeout(IDLE_CACHE_CLEAN_DELAY) {
                if let Some(me) = me.upgrade() {
                    me.idle_cache_clean_wg.done();
                }
                return;
            }
            let Some(me) = me.upgrade() else { return };
            let _run_guard = IdleWgGuard { wg: &me.idle_cache_clean_wg };
            {
                let mut idle = me.idle_cache_clean.lock().unwrap();
                if idle.generation == generation {
                    idle.cancel = None;
                }
            }
            let _update_guard = me.snapshot_update_mu.lock().unwrap();
            me.cancel_scheduled_snapshot_update();

            let ctx = me.background_context();
            let (file_changes, overlays, ata_changes, new_config) = me.flush_changes(&ctx);
            me.update_snapshot(
                &ctx,
                overlays,
                SnapshotChange {
                    reason: UpdateReason::IdleCleanDiskCache,
                    file_changes,
                    ata_changes,
                    new_config,
                    clean_file_cache: true,
                    ..Default::default()
                },
                false,
            );
            // Go: `go func() { runtime.GC() }()` — no Rust equivalent.
        });
    }

    /// `s.cancelIdleCacheClean`.
    fn cancel_idle_cache_clean(&self) {
        let mut idle = self.idle_cache_clean.lock().unwrap();
        if let Some(cancel) = idle.cancel.take() {
            cancel.cancel();
            self.idle_cache_clean_wg.done();
        }
    }

    /// `s.closeIdleCacheClean`.
    fn close_idle_cache_clean(&self) {
        {
            let mut idle = self.idle_cache_clean.lock().unwrap();
            idle.closed = true;
            if let Some(cancel) = idle.cancel.take() {
                cancel.cancel();
                self.idle_cache_clean_wg.done();
            }
        }
        self.idle_cache_clean_wg.wait();
    }

    /// `s.StartPerformanceTelemetry` — periodic performance telemetry; call
    /// once after the session is initialized.
    pub fn start_performance_telemetry(self: &Arc<Self>) {
        if !self.options.telemetry_enabled {
            return;
        }
        let (ctx, cancel) = self.background_context().with_cancel();
        *self.performance_telemetry_cancel.lock().unwrap() = Some(cancel);
        let me = Arc::downgrade(self);
        self.background_queue.enqueue(&ctx, move |ctx| {
            let Some(me) = me.upgrade() else { return };
            loop {
                if ctx.wait_cancelled_timeout(PERFORMANCE_TELEMETRY_INTERVAL) {
                    return;
                }
                match &me.client {
                    Some(client) if client.is_active() => {
                        me.send_performance_telemetry(ctx);
                    }
                    _ => continue,
                }
            }
        });
    }

    /// `s.stopPerformanceTelemetry`.
    fn stop_performance_telemetry(&self) {
        if let Some(cancel) = self.performance_telemetry_cancel.lock().unwrap().take() {
            cancel.cancel();
        }
    }

    /// `s.sendPerformanceTelemetry`.
    ///
    /// PORT: Go reports `runtime/metrics` values (heap sizes, GC counters,
    /// goroutine count). Rust has no GC/runtime equivalent, so those
    /// measurements are 0 — only process/session-derived stats are filled.
    fn send_performance_telemetry(&self, ctx: &Context) {
        if self.client.is_none() || !self.options.telemetry_enabled {
            return;
        }
        let snapshot = self.snapshot();

        let mut measurements = PerformanceStatsTelemetryMeasurements {
            open_file_count: snapshot.overlays().len() as f64,
            uptime_seconds: self.start_time.elapsed().as_secs_f64(),
            project_count: snapshot.project_collection.projects().len() as f64,
            config_count: snapshot.config_file_registry.configs.len() as f64,
            cached_disk_file_count: snapshot.fs.cache_files.len() as f64,
            ..Default::default()
        };

        // System memory — `/proc/meminfo` (Linux only; elsewhere 0, matching
        // Go's os-stat failure path which leaves the fields unset).
        #[cfg(target_os = "linux")]
        if let Ok(meminfo) = std::fs::read_to_string("/proc/meminfo") {
            let mut total = 0f64;
            let mut available = 0f64;
            for line in meminfo.lines() {
                if let Some(v) = line.strip_prefix("MemTotal:") {
                    total = v.trim().trim_end_matches(" kB").parse().unwrap_or(0.0) * 1024.0;
                } else if let Some(v) = line.strip_prefix("MemAvailable:") {
                    available = v.trim().trim_end_matches(" kB").parse().unwrap_or(0.0) * 1024.0;
                }
            }
            measurements.system_mem_total = total;
            measurements.system_mem_used = total - available;
        }

        // Auto-import registry stats.
        if let Some(registry) = snapshot.auto_import_registry() {
            let stats = registry.get_cache_stats();
            measurements.auto_import_project_bucket_count =
                stats.project_buckets.len() as f64;
            measurements.auto_import_node_modules_bucket_count =
                stats.node_modules_buckets.len() as f64;
            measurements.auto_import_unique_package_count = stats.unique_package_count as f64;
            for b in &stats.project_buckets {
                measurements.auto_import_project_export_count += b.export_count as f64;
                measurements.auto_import_project_file_count += b.file_count as f64;
            }
            for b in &stats.node_modules_buckets {
                measurements.auto_import_node_modules_export_count += b.export_count as f64;
                measurements.auto_import_node_modules_file_count += b.file_count as f64;
                if b.dependency_names.is_none() {
                    measurements.auto_import_node_modules_unfiltered_bucket_count += 1.0;
                }
            }
        }

        let ctx = self.with_current_locale(ctx.clone());
        if let Some(client) = &self.client
            && let Err(err) = client.send_telemetry(
                &ctx,
                &TelemetryEvent {
                    performance_stats_telemetry_event: Some(
                        PerformanceStatsTelemetryEvent {
                            measurements: Some(measurements),
                            ..Default::default()
                        },
                    ),
                    ..Default::default()
                },
            )
            && self.options.logging_enabled
        {
            self.logger
                .logf(format_args!("Error sending performance telemetry: {}", err));
        }
    }

    /// `s.sendProjectInfoTelemetryForNewProjects`.
    fn send_project_info_telemetry_for_new_projects(
        &self,
        old_snapshot: &Snapshot,
        new_snapshot: &Snapshot,
    ) {
        if !self.options.telemetry_enabled {
            return;
        }
        let ctx = self.background_context();
        let old_ids: std::collections::HashSet<Id> = old_snapshot
            .project_collection
            .projects_by_id()
            .into_iter()
            .map(|(id, _)| id)
            .collect();
        for (_, project) in new_snapshot.project_collection.projects_by_id() {
            if !old_ids.contains(&project.id) {
                self.send_project_info_telemetry(&ctx, &project);
            }
        }
    }

    /// `s.sendProjectInfoTelemetry`.
    fn send_project_info_telemetry(&self, ctx: &Context, project: &Rc<Project>) {
        let Some(client) = &self.client else { return };
        if !self.options.telemetry_enabled || self.seen_projects.has(&project.id) {
            return;
        }
        if project.program.is_none() || project.command_line.is_none() {
            return;
        }
        let info = self.collect_project_info_telemetry(project);
        if let Err(err) = client.send_telemetry(ctx, &info) {
            if self.options.logging_enabled {
                self.logger
                    .logf(format_args!("Error sending project info telemetry: {}", err));
            }
            return;
        }
        self.seen_projects.add(project.id.clone());
    }

    /// `s.collectProjectInfoTelemetry`.
    fn collect_project_info_telemetry(&self, project: &Rc<Project>) -> TelemetryEvent {
        let default_opts = CompilerOptions::default();
        let opts = project
            .command_line
            .as_ref()
            .and_then(|cl| cl.compiler_options())
            .unwrap_or(&default_opts);

        let config_file_name = if project.kind == Kind::Configured {
            let base_name = project.config_file_name().base_name();
            if base_name == "tsconfig.json" || base_name == "jsconfig.json" {
                base_name.to_string()
            } else {
                "other".to_string()
            }
        } else {
            "other".to_string()
        };

        let project_type = if project.kind == Kind::Configured {
            "configured"
        } else {
            "inferred"
        };

        let mut props = std::collections::BTreeMap::new();
        props.insert("configFileName".to_string(), config_file_name);
        props.insert("projectType".to_string(), project_type.to_string());
        props.insert("version".to_string(), tsc_core::version::version().to_string());

        // Compiler options — booleans and enum string names, no paths.
        let mut compiler_options = serde_json::Map::new();
        let set_tristate = |m: &mut serde_json::Map<String, serde_json::Value>,
                            key: &str,
                            v: Tristate| {
            if v == tsc_core::tristate::TS_TRUE {
                m.insert(key.to_string(), serde_json::Value::Bool(true));
            } else if v == tsc_core::tristate::TS_FALSE {
                m.insert(key.to_string(), serde_json::Value::Bool(false));
            }
        };
        set_tristate(&mut compiler_options, "strict", opts.strict);
        set_tristate(&mut compiler_options, "noImplicitAny", opts.no_implicit_any);
        set_tristate(&mut compiler_options, "noImplicitThis", opts.no_implicit_this);
        set_tristate(
            &mut compiler_options,
            "strictNullChecks",
            opts.strict_null_checks,
        );
        set_tristate(
            &mut compiler_options,
            "strictFunctionTypes",
            opts.strict_function_types,
        );
        set_tristate(
            &mut compiler_options,
            "strictBindCallApply",
            opts.strict_bind_call_apply,
        );
        set_tristate(
            &mut compiler_options,
            "strictPropertyInitialization",
            opts.strict_property_initialization,
        );
        set_tristate(
            &mut compiler_options,
            "strictBuiltinIteratorReturn",
            opts.strict_builtin_iterator_return,
        );
        set_tristate(
            &mut compiler_options,
            "useUnknownInCatchVariables",
            opts.use_unknown_in_catch_variables,
        );
        set_tristate(
            &mut compiler_options,
            "exactOptionalPropertyTypes",
            opts.exact_optional_property_types,
        );
        set_tristate(&mut compiler_options, "allowJs", opts.allow_js);
        set_tristate(&mut compiler_options, "checkJs", opts.check_js);
        set_tristate(&mut compiler_options, "noEmit", opts.no_emit);
        set_tristate(&mut compiler_options, "declaration", opts.declaration);
        set_tristate(&mut compiler_options, "composite", opts.composite);
        set_tristate(
            &mut compiler_options,
            "isolatedModules",
            opts.isolated_modules,
        );
        set_tristate(&mut compiler_options, "skipLibCheck", opts.skip_lib_check);
        set_tristate(&mut compiler_options, "incremental", opts.incremental);
        if opts.target != ScriptTarget::None {
            compiler_options.insert(
                "target".to_string(),
                serde_json::Value::String(opts.target.to_string()),
            );
        }
        if opts.module != ModuleKind::None {
            compiler_options.insert(
                "module".to_string(),
                serde_json::Value::String(opts.module.to_string()),
            );
        }
        if opts.module_resolution != ModuleResolutionKind::Unknown
        {
            compiler_options.insert(
                "moduleResolution".to_string(),
                serde_json::Value::String(opts.module_resolution.to_string()),
            );
        }
        if opts.jsx != JsxEmit::None {
            compiler_options.insert(
                "jsx".to_string(),
                serde_json::Value::String(opts.jsx.to_string()),
            );
        }
        if let Ok(b) = serde_json::to_string(&compiler_options) {
            props.insert("compilerOptions".to_string(), b);
        }

        // Config file shape.
        if let Some(raw_map) = project
            .command_line
            .as_ref()
            .and_then(|cl| cl.raw.as_ref())
            .and_then(|raw| raw.as_map())
        {
            let has = |key: &str| {
                if raw_map.has(key) {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            };
            props.insert("extends".to_string(), has("extends"));
            props.insert("files".to_string(), has("files"));
            props.insert("include".to_string(), has("include"));
            props.insert("exclude".to_string(), has("exclude"));
        }

        TelemetryEvent {
            project_info_telemetry_event: Some(ProjectInfoTelemetryEvent {
                event_name: tsc_lsproto::StringLiteralLanguageServerProjectInfo,
                telemetry_purpose: tsc_lsproto::StringLiteralUsage,
                properties: Some(props),
                measurements: Some(count_file_stats(
                    project.program.as_ref().unwrap(),
                )),
            }),
            ..Default::default()
        }
    }

    /// `s.Snapshot()` — the session's current snapshot. `Arc` replaces Go's
    /// ref/deref protocol.
    pub fn snapshot(&self) -> Arc<Snapshot> {
        Arc::clone(
            self.snapshot
                .read()
                .unwrap()
                .as_ref()
                .expect("snapshot accessed after session close"),
        )
    }

    /// `s.getSnapshot` — flushes pending changes and updates the session's
    /// snapshot if needed for the given request. `caller_ref` is a no-op in
    /// Rust (`Arc` handles the reference); kept for Go parity.
    pub fn get_snapshot(
        self: &Arc<Self>,
        ctx: &Context,
        request: ResourceRequest,
        _caller_ref: bool,
    ) -> Arc<Snapshot> {
        let _update_guard = self.snapshot_update_mu.lock().unwrap();
        self.cancel_scheduled_snapshot_update();

        let (file_changes, overlays, ata_changes, new_config) = self.flush_changes(ctx);
        if !file_changes.is_empty() || !ata_changes.is_empty() || new_config.is_some() {
            let mut change = SnapshotChange {
                reason: UpdateReason::RequestedLanguageServicePendingChanges,
                file_changes,
                ata_changes,
                new_config,
                ..Default::default()
            };
            change.set_resource_request(request);
            return self.update_snapshot(ctx, overlays, change, true).unwrap();
        }

        // If there are no pending file changes, try the current snapshot.
        let snapshot = self.snapshot();
        let mut update_reason = UpdateReason::Unknown;
        if !request.projects.is_empty() {
            update_reason = UpdateReason::RequestedLanguageServiceProjectDirty;
        } else if request.project_tree.is_some() {
            update_reason = UpdateReason::RequestedLoadProjectTree;
        } else if !request.auto_imports.as_str().is_empty() {
            update_reason = UpdateReason::RequestedLanguageServiceWithAutoImports;
        } else {
            for document in &request.documents {
                let project = snapshot.get_default_project(document);
                if project.is_none() {
                    update_reason = UpdateReason::RequestedLanguageServiceProjectNotLoaded;
                } else if project.as_ref().unwrap().dirty {
                    update_reason = UpdateReason::RequestedLanguageServiceProjectDirty;
                }
            }
            if update_reason == UpdateReason::Unknown {
                for document in &request.configured_project_documents {
                    if snapshot.is_open_file(&document.file_name()) {
                        let project = snapshot.get_default_project(document);
                        if project.is_none() {
                            update_reason =
                                UpdateReason::RequestedLanguageServiceProjectNotLoaded;
                        } else if project.as_ref().unwrap().dirty {
                            update_reason =
                                UpdateReason::RequestedLanguageServiceProjectDirty;
                        }
                    } else {
                        update_reason = UpdateReason::RequestedLanguageServiceForFileNotOpen;
                    }
                }
            }
        }
        if update_reason == UpdateReason::Unknown {
            return snapshot;
        }
        drop(snapshot);

        let mut change = SnapshotChange {
            reason: update_reason,
            ..Default::default()
        };
        change.set_resource_request(request);
        self.update_snapshot(ctx, overlays, change, true).unwrap()
    }

    /// `s.getSnapshotAndDefaultProject`.
    ///
    /// PORT: Rust returns the snapshot + project and lets the caller build
    /// the `LanguageService` (which borrows the snapshot) — see
    /// [`SessionLanguageService`].
    pub fn get_snapshot_and_default_project(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
        caller_ref: bool,
    ) -> Result<(Arc<Snapshot>, Rc<Project>), String> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: vec![uri.clone()],
                ..Default::default()
            },
            caller_ref,
        );
        let project = snapshot.get_default_project(uri);
        match project {
            Some(project) => Ok((snapshot, project)),
            None => {
                if let Some(file) = snapshot.get_file(&uri.file_name())
                    && file.kind() == tsc_core::scriptkind::ScriptKind::Unknown
                {
                    return Err(format!(
                        "{}: no project found for URI {}",
                        ERR_NO_PROJECT_FOR_UNKNOWN_SCRIPT_KIND,
                        uri.as_str()
                    ));
                }
                Err(format!("no project found for URI {}", uri.as_str()))
            }
        }
    }

    /// `s.GetLanguageService` — returns a [`SessionLanguageService`] owning
    /// the snapshot/project; `LanguageService` borrows are built on demand.
    pub fn get_language_service(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
    ) -> Result<SessionLanguageService, String> {
        let (snapshot, project) = self.get_snapshot_and_default_project(ctx, uri, false)?;
        Ok(SessionLanguageService {
            snapshot,
            project,
            active_file: uri.file_name().as_string().to_string(),
        })
    }

    /// `s.GetLanguageServiceAndProjectsForFile` — `(default project, all
    /// language-service projects containing the file)`; the
    /// `SessionLanguageService` covers the default service.
    pub fn get_language_service_and_projects_for_file(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
    ) -> Result<(SessionLanguageService, Vec<Rc<Project>>), String> {
        let service = self.get_language_service(ctx, uri)?;
        // !!! TODO: sheetal: Get other projects that contain the file with
        // symlink
        let all_projects = service
            .snapshot
            .get_language_service_projects_containing_file(uri);
        Ok((service, all_projects))
    }

    /// `s.GetProjectsForFile`.
    pub fn get_projects_for_file(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
    ) -> Result<Vec<Rc<Project>>, String> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                configured_project_documents: vec![uri.clone()],
                ..Default::default()
            },
            false,
        );
        // !!! TODO: sheetal: Get other projects that contain the file with
        // symlink
        Ok(snapshot.get_language_service_projects_containing_file(uri))
    }

    /// `s.GetLanguageServicesForDocumentsLoadingProjectTree` — returns the
    /// snapshot and every language-service project after loading the project
    /// trees. Callers build `LanguageService`s via
    /// `SessionLanguageService::language_service` or directly.
    pub fn get_language_services_for_documents_loading_project_tree(
        self: &Arc<Self>,
        ctx: &Context,
        uris: &[DocumentUri],
    ) -> (Arc<Snapshot>, Vec<Rc<Project>>) {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: uris.to_vec(),
                project_tree: Some(ProjectTreeRequest::new(None)),
                ..Default::default()
            },
            false,
        );
        let projects = snapshot
            .project_collection
            .language_service_projects()
            .into_iter()
            .filter(|p| p.get_program().is_some())
            .collect();
        (snapshot, projects)
    }

    /// `s.GetLanguageServiceForProjectWithFile`.
    pub fn get_language_service_for_project_with_file(
        self: &Arc<Self>,
        ctx: &Context,
        project: &Rc<Project>,
        uri: &DocumentUri,
    ) -> Option<SessionLanguageService> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                projects: vec![project.id.clone()],
                ..Default::default()
            },
            false,
        );
        // Ensure we have an updated project.
        let project = snapshot
            .project_collection
            .get_project(&project.id)?
            .clone();
        // If the program doesn't contain this file any more, ignore it.
        if !project.has_file(&uri.file_name()) {
            return None;
        }
        Some(SessionLanguageService {
            snapshot,
            project,
            active_file: uri.file_name().as_string().to_string(),
        })
    }

    /// `s.WithSnapshotLoadingProjectTree`.
    pub fn with_snapshot_loading_project_tree(
        self: &Arc<Self>,
        ctx: &Context,
        requested_project_trees: &Set<PathKey>,
        f: impl FnOnce(&Snapshot),
    ) {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                project_tree: Some(ProjectTreeRequest::new(Some(
                    requested_project_trees.clone(),
                ))),
                ..Default::default()
            },
            true,
        );
        f(&snapshot);
    }

    /// `s.WithSnapshotForDocument`.
    pub fn with_snapshot_for_document(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
        f: impl FnOnce(&Snapshot),
    ) {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: vec![uri.clone()],
                ..Default::default()
            },
            true,
        );
        f(&snapshot);
    }

    /// `s.GetCurrentLanguageServiceWithAutoImports`.
    pub fn get_current_language_service_with_auto_imports(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
    ) -> Result<SessionLanguageService, String> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: vec![uri.clone()],
                auto_imports: uri.clone(),
                ..Default::default()
            },
            false,
        );
        let Some(project) = snapshot.get_default_project(uri) else {
            return Err(format!("no project found for URI {}", uri.as_str()));
        };
        Ok(SessionLanguageService {
            snapshot,
            project,
            active_file: uri.file_name().as_string().to_string(),
        })
    }

    /// `s.WithLanguageServiceAndSnapshot` — acquires a snapshot and a
    /// `SessionLanguageService` for `uri`, then calls `f` with both. The
    /// closure receives a `LanguageService` built on the held snapshot.
    /// The returned `async_work` closure keeps the snapshot alive until
    /// called (Go's returned `func() error`).
    pub fn with_language_service_and_snapshot<R>(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &DocumentUri,
        f: impl FnOnce(LanguageService<'_>, &Arc<Snapshot>) -> (Option<R>, Option<String>),
    ) -> Result<impl FnOnce() -> R, String> {
        let (snapshot, project) = self.get_snapshot_and_default_project(ctx, uri, true)?;
        let language_service = new_language_service(
            ProjectId(Rc::from(project.id.as_str())),
            project.get_program().unwrap().clone(),
            &*snapshot,
            &uri.file_name().as_string(),
        );
        let (async_work, err) = f(language_service, &snapshot);
        if let Some(err) = err {
            return Err(err);
        }
        let async_work = async_work.ok_or_else(|| "no async work".to_string())?;
        Ok(move || async_work)
    }

    /// `s.GetLanguageServiceWithAutoImports` — clones `base_snapshot` with
    /// auto-import preparation; adoption happens in the background.
    pub fn get_language_service_with_auto_imports(
        self: &Arc<Self>,
        ctx: &Context,
        base_snapshot: &Arc<Snapshot>,
        uri: &DocumentUri,
    ) -> Result<SessionLanguageService, String> {
        let new_snapshot = self.host.clone_snapshot_with_auto_imports(
            ctx,
            base_snapshot,
            uri,
            Some(&self.logger),
        );
        let Some(project) = new_snapshot.get_default_project(uri) else {
            return Err(format!("no project found for URI {}", uri.as_str()));
        };
        self.try_adopt_snapshot_change_in_background(base_snapshot, &new_snapshot);
        Ok(SessionLanguageService {
            snapshot: new_snapshot,
            project,
            active_file: uri.file_name().as_string().to_string(),
        })
    }

    /// `s.tryAdoptSnapshotChangeInBackground`.
    /// `pub(crate)` — `api.rs` (same package in Go).
    pub(crate) fn try_adopt_snapshot_change_in_background(
        self: &Arc<Self>,
        base_snapshot: &Arc<Snapshot>,
        new_snapshot: &Arc<Snapshot>,
    ) {
        let ctx = self.background_context();
        let me = Arc::downgrade(self);
        let base_snapshot = SendShared(Arc::clone(base_snapshot));
        let new_snapshot = SendShared(Arc::clone(new_snapshot));
        self.background_queue.enqueue(&ctx, move |_ctx| {
            if let Some(me) = me.upgrade() {
                me.adopt_snapshot_change(&base_snapshot.into_inner(), &new_snapshot.into_inner());
            }
        });
    }

    /// `s.adoptSnapshotChange` — promotes a cloned snapshot as the session's
    /// current snapshot, or discards it if the session has moved on.
    fn adopt_snapshot_change(&self, base_snapshot: &Arc<Snapshot>, new_snapshot: &Arc<Snapshot>) {
        let mut current = self.snapshot.write().unwrap();
        let old_snapshot = current.as_ref().map(|s| s.id);
        if old_snapshot == Some(base_snapshot.id) {
            // Session hasn't moved on; adopt the new snapshot.
            let old = current.replace(Arc::clone(new_snapshot)).unwrap();
            let content_mapper_timings = self.take_content_mapper_timing_delta();
            drop(current);
            if self.options.logging_enabled {
                self.logger.log(format_args!(
                    "Adopted snapshot {} (parent {}) as current session snapshot (replacing {})",
                    new_snapshot.id, new_snapshot.parent_id, old.id
                ));
                if new_snapshot.builder_logs.is_some() {
                    self.logger.log(format_args!("{}", new_snapshot.builder_logs));
                }
                self.log_content_mapper_timings(&content_mapper_timings);
            }
            drop(old);
        } else {
            // Session has moved on to a newer snapshot; discard this one.
            drop(current);
            if self.options.logging_enabled {
                self.logger.log(format_args!(
                    "Discarded snapshot {} (parent {}); session has moved on to snapshot {:?}",
                    new_snapshot.id, new_snapshot.parent_id, old_snapshot
                ));
                if new_snapshot.builder_logs.is_some() {
                    let logs = new_snapshot.builder_logs.to_string();
                    if !logs.is_empty() {
                        self.logger.log(format_args!(
                            "--- Discarded snapshot {} builder logs (NOT adopted) ---",
                            new_snapshot.id
                        ));
                        self.logger.log(format_args!("{}", logs));
                        self.logger.log(format_args!(
                            "--- End discarded snapshot {} builder logs ---",
                            new_snapshot.id
                        ));
                    }
                }
            }
        }
    }

    /// `s.UpdateSnapshot`.
    pub fn update_snapshot(
        self: &Arc<Self>,
        ctx: &Context,
        overlays: FxHashMap<PathKey, Arc<Overlay>>,
        change: SnapshotChange,
        caller_ref: bool,
    ) -> Option<Arc<Snapshot>> {
        // `warm_auto_import_cache` reads `change.file_changes.changed` —
        // capture it before the change is consumed by the clone.
        let warm_changed = change.file_changes.changed.clone();
        let (old_snapshot, new_snapshot, content_mapper_timings) = {
            let mut current = self.snapshot.write().unwrap();
            let old_snapshot = Arc::clone(current.as_ref().unwrap());
            let ctx = if tsc_locale::has_locale(ctx) {
                ctx.clone()
            } else {
                self.with_current_locale(ctx.clone())
            };
            let new_snapshot = old_snapshot.clone(
                &ctx,
                change,
                overlays,
                Some(&self.logger),
                self.client.as_ref(),
            );
            // A failed API request may have mutated only a prefix of its
            // clone; it must never become canonical session state.
            if new_snapshot.api_error.is_some() {
                return if caller_ref { Some(new_snapshot) } else { None };
            }
            let content_mapper_timings = if !Arc::ptr_eq(&new_snapshot, &old_snapshot) {
                self.take_content_mapper_timing_delta()
            } else {
                Timings::default()
            };
            if caller_ref {
                new_snapshot.ref_();
            }
            *current = Some(Arc::clone(&new_snapshot));
            (old_snapshot, new_snapshot, content_mapper_timings)
        };

        // Enqueue ATA updates if needed.
        if self.typings_installer.is_some() && !self.config().is_ata_disabled() {
            self.trigger_ata_for_updated_projects(&new_snapshot);
        }

        // Enqueue logging, watch updates, and diagnostic refresh tasks.
        // !!! userPreferences/configuration updates
        let me = Arc::downgrade(self);
        let ctx = self.background_context();
        let old_snapshot = SendShared(old_snapshot);
        let new_snapshot_for_queue = SendShared(Arc::clone(&new_snapshot));
        let warm_changed = SendShared(warm_changed);
        self.background_queue.enqueue(&ctx, move |ctx| {
            let Some(me) = me.upgrade() else { return };
            let old_snapshot = &old_snapshot.into_inner();
            let new_snapshot = &new_snapshot_for_queue.into_inner();
            let warm_changed = &warm_changed.into_inner();
            if me.options.logging_enabled {
                me.logger.log(format_args!(
                    "Adopted snapshot {} (parent {}) as current session snapshot (replacing {})",
                    new_snapshot.id, new_snapshot.parent_id, old_snapshot.id
                ));
                if new_snapshot.builder_logs.is_some() {
                    me.logger
                        .log(format_args!("{}", new_snapshot.builder_logs));
                }
                me.log_project_changes(old_snapshot, new_snapshot);
                me.log_content_mapper_timings(&content_mapper_timings);
                me.logger.log(format_args!(""));
            }
            if me.options.watch_enabled
                && let Err(err) = me.update_watches(old_snapshot, new_snapshot)
                && me.options.logging_enabled
            {
                me.logger.log(format_args!("{}", err));
            }
            let _ = me.update_content_mapper_registrations(ctx, new_snapshot);
            me.publish_program_diagnostics(old_snapshot, new_snapshot);
            me.send_project_info_telemetry_for_new_projects(old_snapshot, new_snapshot);
            me.warm_auto_import_cache(ctx, warm_changed, old_snapshot, new_snapshot);
        });

        Some(new_snapshot)
    }

    /// `s.takeContentMapperTimingDelta`.
    fn take_content_mapper_timing_delta(&self) -> Timings {
        let Some(host) = &self.content_mapper_host else {
            return Timings::default();
        };
        let current = host.timings();
        let mut previous = self.content_mapper_timings.lock().unwrap();
        let delta = current.since(&previous);
        *previous = current;
        delta
    }

    /// `s.logContentMapperTimings`.
    fn log_content_mapper_timings(&self, timings: &Timings) {
        if timings.request_wait.is_zero()
            && !has_content_mapper_operation_timings(&timings.mappers)
        {
            return;
        }
        self.logger
            .log(format_args!("Content mapper timings since previous snapshot adoption:"));
        if !timings.request_wait.is_zero() {
            self.logger
                .logf(format_args!("  Request wait time: {:?}", timings.request_wait));
        }
        let mut identities: Vec<&String> = timings.mappers.keys().collect();
        identities.sort();
        for identity in identities {
            let mapper = &timings.mappers[identity];
            if !has_content_mapper_operation_timing(mapper) {
                continue;
            }
            self.logger.logf(format_args!("  {}:", identity));
            if mapper.spawn.count != 0 {
                self.logger.logf(format_args!(
                    "    Initializations: {} ({:?})",
                    mapper.spawn.count,
                    mapper.spawn.duration + mapper.initialize.duration
                ));
            }
            if mapper.open_project.count != 0 {
                self.logger.logf(format_args!(
                    "    openProject requests: {} ({:?})",
                    mapper.open_project.count, mapper.open_project.duration
                ));
            }
            if mapper.close_project.count != 0 {
                self.logger.logf(format_args!(
                    "    closeProject requests: {} ({:?})",
                    mapper.close_project.count, mapper.close_project.duration
                ));
            }
            if mapper.transform.count != 0 {
                self.logger.logf(format_args!(
                    "    Transforms: {} ({:?})",
                    mapper.transform.count, mapper.transform.duration
                ));
            }
        }
    }

    /// `s.WaitForBackgroundTasks` — testing hook.
    pub fn wait_for_background_tasks(&self) {
        self.cancel_idle_cache_clean();
        self.background_queue.wait();
    }

    /// `s.flushChanges` — drains all pending state under their locks.
    /// `pub(crate)` — `api.rs` (same package in Go).
    pub(crate) fn flush_changes(
        &self,
        ctx: &Context,
    ) -> (
        FileChangeSummary,
        FxHashMap<PathKey, Arc<Overlay>>,
        FxHashMap<Id, AtaStateChange>,
        Option<UserPreferences>,
    ) {
        let mut pending = self.pending_file_changes.lock().unwrap();
        let pending_ata_changes = {
            let mut ata = self.pending_ata_changes.lock().unwrap();
            std::mem::take(&mut *ata)
        };
        let (file_changes, overlays) = self.flush_changes_locked(ctx, &mut pending);
        let mut user_config = self.user_config.write().unwrap();
        let new_prefs = if user_config.pending_user_config_changes {
            Some(user_config.workspace_user_preferences.clone())
        } else {
            None
        };
        user_config.pending_user_config_changes = false;
        (file_changes, overlays, pending_ata_changes, new_prefs)
    }

    /// `s.flushChangesLocked` — `pending` must be the lock guard of
    /// `pending_file_changes`.
    fn flush_changes_locked(
        &self,
        _ctx: &Context,
        pending: &mut Vec<FileChange>,
    ) -> (FileChangeSummary, FxHashMap<PathKey, Arc<Overlay>>) {
        if pending.is_empty() {
            return (FileChangeSummary::default(), self.fs.overlays());
        }
        let start = Instant::now();
        let change_count = pending.len();
        let changes = std::mem::take(pending);
        let (summary, overlays) = self.fs.process_changes(changes);
        if self.options.logging_enabled {
            self.logger.log(format_args!(
                "Processed {} file changes in {:?}",
                change_count,
                start.elapsed()
            ));
        }
        (summary, overlays)
    }

    /// `s.updateWatch` — reconcile a `WatchedFiles` pair: register new globs
    /// with the client (rolling back on failure) and unregister removed
    /// ones. Returns the accumulated errors.
    fn update_watch<T>(
        &self,
        ctx: &Context,
        old_watcher: Option<&Arc<WatchedFiles<T>>>,
        new_watcher: Option<&Arc<WatchedFiles<T>>>,
    ) -> Vec<ClientError> {
        let mut errors = Vec::new();
        if let Some(new_watcher) = new_watcher {
            let w = new_watcher.watchers();
            let watchers: Vec<Arc<FileSystemWatcher>> = w
                .workspace_watchers
                .iter()
                .chain(w.outside_workspace_watchers.iter())
                .cloned()
                .collect();
            if !watchers.is_empty() {
                let mut new_watchers: Vec<(WatcherId, Arc<FileSystemWatcher>)> = Vec::new();
                for (i, watcher) in watchers.iter().enumerate() {
                    let glob_id: WatcherId = format!("{}.{}", w.watcher_id, i);
                    if self.watches.acquire(watcher, glob_id.clone()) {
                        new_watchers.push((glob_id, watcher.clone()));
                    }
                }
                let mut watch_errors = Vec::new();
                for (id, watcher) in &new_watchers {
                    // Fresh timeout per client call.
                    let (call_ctx, call_cancel) = ctx.with_timeout(WATCH_REQUEST_TIMEOUT);
                    let err = self.client.as_ref().map(|client| {
                        client.watch_files(&call_ctx, id, std::slice::from_ref(watcher))
                    });
                    call_cancel.cancel();
                    match err {
                        Some(Err(err)) => watch_errors.push(err),
                        _ => {
                            if old_watcher.is_none() {
                                self.logger.log(format_args!("Added new watch: {}", id));
                            } else {
                                self.logger.log(format_args!("Updated watch: {}", id));
                            }
                            self.logger.log(format_args!(
                                "\t{}",
                                file_system_watcher_glob_string(watcher)
                            ));
                            self.logger.log(format_args!(""));
                        }
                    }
                }
                if !watch_errors.is_empty() {
                    // Roll back ALL newly-acquired watchers on any failure
                    // to keep refcounts clean.
                    for (_, watcher) in &new_watchers {
                        self.watches.release(watcher);
                    }
                    self.watches.mark_pending(&w.watcher_id);
                    errors.extend(watch_errors);
                } else {
                    self.watches.clear_pending(&w.watcher_id);
                }
                if !w.ignored_paths.is_empty() {
                    self.logger.logf(format_args!(
                        "{} paths ineligible for watching",
                        w.ignored_paths.len()
                    ));
                    if self.logger.is_verbose() {
                        for path in &w.ignored_paths {
                            self.logger.log(format_args!("\t{}", path.as_string()));
                        }
                    }
                }
            }
        }
        if let Some(old_watcher) = old_watcher {
            let w = old_watcher.watchers();
            let watchers: Vec<Arc<FileSystemWatcher>> = w
                .workspace_watchers
                .iter()
                .chain(w.outside_workspace_watchers.iter())
                .cloned()
                .collect();
            if !watchers.is_empty() {
                let mut removed_ids: Vec<WatcherId> = Vec::new();
                for watcher in &watchers {
                    if let Some(id) = self.watches.release(watcher) {
                        removed_ids.push(id);
                    }
                }
                for id in &removed_ids {
                    let (call_ctx, call_cancel) = ctx.with_timeout(WATCH_REQUEST_TIMEOUT);
                    let err = self
                        .client
                        .as_ref()
                        .map(|client| client.unwatch_files(&call_ctx, id));
                    call_cancel.cancel();
                    match err {
                        Some(Err(err)) => errors.push(err),
                        _ => {
                            if new_watcher.is_none() {
                                self.logger.log(format_args!("Removed watch: {}", id));
                            }
                        }
                    }
                }
            }
        }
        errors
    }

    /// `s.updateContentMapperRegistrations` — registers the union of
    /// content-mapper extensions with the client when it changes.
    fn update_content_mapper_registrations(
        &self,
        ctx: &Context,
        snapshot: &Snapshot,
    ) -> Result<(), ClientError> {
        let Some(client) = &self.client else {
            return Ok(());
        };
        let content_mappers = snapshot.config_file_registry.content_mappers();
        let mut extensions = content_mappers.extensions.clone();
        extensions.extend(
            snapshot
                .inferred_project_content_mapper_extensions
                .iter()
                .cloned(),
        );
        extensions.sort();
        extensions.dedup();

        let mut registration = self.content_mapper_registration.lock().unwrap();
        // Background tasks may finish out of order; never let an older
        // snapshot's task overwrite the registration of a newer one.
        if snapshot.id <= registration.snapshot_id {
            return Ok(());
        }
        if extensions == registration.extensions {
            registration.snapshot_id = snapshot.id;
            return Ok(());
        }
        if let Err(err) = client.register_content_mapper_extensions(ctx, &extensions) {
            if self.options.logging_enabled {
                self.logger.log(format_args!("{}", err));
            }
            return Err(err);
        }
        registration.extensions = extensions;
        registration.snapshot_id = snapshot.id;
        Ok(())
    }

    /// `s.updateWatches`.
    fn update_watches(&self, old_snapshot: &Snapshot, new_snapshot: &Snapshot) -> Result<(), ClientError> {
        let mut errors = Vec::new();
        let start = Instant::now();
        let ctx = self.background_context();

        // Config file entry watches.
        let mut seen_new: FxHashMap<PathKey, &ConfigFileEntry> = FxHashMap::default();
        for (path, new_entry) in new_snapshot.config_file_registry.configs.iter() {
            seen_new.insert(path.clone(), new_entry);
            match old_snapshot.config_file_registry.configs.get(path) {
                None => {
                    errors.extend(self.update_watch(&ctx, None, new_entry.root_files_watch.as_ref()));
                }
                Some(old_entry) => {
                    if old_entry.root_files_watch.as_ref().map(|w| w.id())
                        != new_entry.root_files_watch.as_ref().map(|w| w.id())
                    {
                        errors.extend(self.update_watch(
                            &ctx,
                            old_entry.root_files_watch.as_ref(),
                            new_entry.root_files_watch.as_ref(),
                        ));
                    }
                }
            }
        }
        for (path, old_entry) in old_snapshot.config_file_registry.configs.iter() {
            if !new_snapshot.config_file_registry.configs.contains_key(path) {
                errors.extend(self.update_watch(&ctx, old_entry.root_files_watch.as_ref(), None));
            }
        }
        // Retry config watchers whose IDs didn't change but whose previous
        // registration failed.
        for (path, new_entry) in new_snapshot.config_file_registry.configs.iter() {
            if let Some(old_entry) = old_snapshot.config_file_registry.configs.get(path)
                && old_entry.root_files_watch.as_ref().map(|w| w.id())
                    == new_entry.root_files_watch.as_ref().map(|w| w.id())
                && let Some(watch) = &new_entry.root_files_watch
                && self.watches.is_pending(&watch.id())
            {
                errors.extend(self.update_watch(&ctx, None, Some(watch)));
            }
        }

        // Project watches — diff by ID (Go's `DiffOrderedMaps`).
        let old_projects: FxHashMap<Id, Rc<Project>> = old_snapshot
            .project_collection
            .projects_by_id()
            .into_iter()
            .collect();
        let new_projects: FxHashMap<Id, Rc<Project>> = new_snapshot
            .project_collection
            .projects_by_id()
            .into_iter()
            .collect();
        for (id, new_project) in &new_projects {
            match old_projects.get(id) {
                None => {
                    errors.extend(self.update_watch(
                        &ctx,
                        None,
                        new_project.program_files_watch.as_ref(),
                    ));
                    errors.extend(
                        self.update_watch(&ctx, None, new_project.typings_watch.as_ref()),
                    );
                    errors.extend(
                        self.update_watch(&ctx, None, new_project.content_mapper_watch.as_ref()),
                    );
                }
                Some(old_project) => {
                    if old_project.program_files_watch.as_ref().map(|w| w.id())
                        != new_project.program_files_watch.as_ref().map(|w| w.id())
                    {
                        errors.extend(self.update_watch(
                            &ctx,
                            old_project.program_files_watch.as_ref(),
                            new_project.program_files_watch.as_ref(),
                        ));
                    } else if let Some(watch) = &new_project.program_files_watch
                        && self.watches.is_pending(&watch.id())
                    {
                        errors.extend(self.update_watch(&ctx, None, Some(watch)));
                    }
                    if old_project.typings_watch.as_ref().map(|w| w.id())
                        != new_project.typings_watch.as_ref().map(|w| w.id())
                    {
                        errors.extend(self.update_watch(
                            &ctx,
                            old_project.typings_watch.as_ref(),
                            new_project.typings_watch.as_ref(),
                        ));
                    } else if let Some(watch) = &new_project.typings_watch
                        && self.watches.is_pending(&watch.id())
                    {
                        errors.extend(self.update_watch(&ctx, None, Some(watch)));
                    }
                    if old_project.content_mapper_watch.as_ref().map(|w| w.id())
                        != new_project.content_mapper_watch.as_ref().map(|w| w.id())
                    {
                        errors.extend(self.update_watch(
                            &ctx,
                            old_project.content_mapper_watch.as_ref(),
                            new_project.content_mapper_watch.as_ref(),
                        ));
                    } else if let Some(watch) = &new_project.content_mapper_watch
                        && self.watches.is_pending(&watch.id())
                    {
                        errors.extend(self.update_watch(&ctx, None, Some(watch)));
                    }
                }
            }
        }
        for (id, removed_project) in &old_projects {
            if !new_projects.contains_key(id) {
                errors.extend(self.update_watch(
                    &ctx,
                    removed_project.program_files_watch.as_ref(),
                    None,
                ));
                errors.extend(
                    self.update_watch(&ctx, removed_project.typings_watch.as_ref(), None),
                );
                errors.extend(
                    self.update_watch(&ctx, removed_project.content_mapper_watch.as_ref(), None),
                );
            }
        }

        if old_snapshot.auto_imports_watch.as_ref().map(|w| w.id())
            != new_snapshot.auto_imports_watch.as_ref().map(|w| w.id())
        {
            errors.extend(self.update_watch(
                &ctx,
                old_snapshot.auto_imports_watch.as_ref(),
                new_snapshot.auto_imports_watch.as_ref(),
            ));
        } else if let Some(watch) = &new_snapshot.auto_imports_watch
            && self.watches.is_pending(&watch.id())
        {
            errors.extend(self.update_watch(&ctx, None, Some(watch)));
        }

        if !errors.is_empty() {
            return Err(format!("errors updating watches: {:?}", errors).into());
        } else if self.options.logging_enabled {
            self.logger
                .log(format_args!("Updated watches in {:?}", start.elapsed()));
        }
        Ok(())
    }

    /// `s.NpmInstall`.
    pub fn npm_install(
        &self,
        ctx: &Context,
        cwd: RootedDirectoryPath,
        npm_install_args: &[String],
    ) -> Result<Vec<u8>, ClientError> {
        self.npm_executor
            .as_ref()
            .ok_or_else(|| ClientError::from("npm executor not available"))?
            .npm_install(ctx, &cwd, npm_install_args)
    }

    /// `s.refreshInlayHintsIfNeeded`.
    fn refresh_inlay_hints_if_needed(&self, old_prefs: &UserPreferences, new_prefs: &UserPreferences) {
        if old_prefs.inlay_hints_preferences != new_prefs.inlay_hints_preferences
            && let Some(client) = &self.client
            && let Err(err) = client.refresh_inlay_hints(&self.background_context())
            && self.options.logging_enabled
        {
            self.logger
                .logf(format_args!("Error refreshing inlay hints: {}", err));
        }
    }

    /// `s.refreshCodeLensIfNeeded`.
    fn refresh_code_lens_if_needed(&self, old_prefs: &UserPreferences, new_prefs: &UserPreferences) {
        if old_prefs.code_lens_user_preferences != new_prefs.code_lens_user_preferences
            && let Some(client) = &self.client
            && let Err(err) = client.refresh_code_lens(&self.background_context())
            && self.options.logging_enabled
        {
            self.logger
                .logf(format_args!("Error refreshing code lens: {}", err));
        }
    }

    /// `s.refreshDiagnosticsIfNeeded`.
    fn refresh_diagnostics_if_needed(self: &Arc<Self>, old_prefs: &UserPreferences, new_prefs: &UserPreferences) {
        if old_prefs.custom_config_file_name != new_prefs.custom_config_file_name
            || old_prefs.report_style_checks_as_warnings != new_prefs.report_style_checks_as_warnings
            || old_prefs.validate_enabled != new_prefs.validate_enabled
        {
            self.schedule_diagnostics_refresh(self.options.debounce_delay);
        }
    }

    /// `s.refreshATAIfNeeded`.
    fn refresh_ata_if_needed(self: &Arc<Self>, old_prefs: &UserPreferences, new_prefs: &UserPreferences) {
        if old_prefs.is_ata_disabled() && !new_prefs.is_ata_disabled() {
            // ATA was re-enabled; schedule a diagnostics refresh so the next
            // snapshot update re-triggers ATA for existing projects.
            self.schedule_diagnostics_refresh(self.options.debounce_delay);
        }
    }

    /// `s.publishProgramDiagnostics`.
    fn publish_program_diagnostics(&self, old_snapshot: &Snapshot, new_snapshot: &Snapshot) {
        if !self.options.push_diagnostics_enabled {
            return;
        }
        if new_snapshot.user_preferences().validate_enabled == tsc_core::tristate::TS_FALSE {
            if old_snapshot.user_preferences().validate_enabled == tsc_core::tristate::TS_FALSE {
                return;
            }
            let old_open_projects = old_snapshot
                .project_collection
                .get_open_configured_projects();
            for (_, old_project) in old_snapshot.project_collection.projects_by_id() {
                if let Some(configured_id) = old_project.id.configured()
                    && old_open_projects.has(&configured_id)
                {
                    self.publish_project_diagnostics(
                        &old_project,
                        Vec::new(),
                        old_snapshot,
                    );
                }
            }
            return;
        }

        let ctx = self.background_context();
        let old_projects: FxHashMap<Id, Rc<Project>> = old_snapshot
            .project_collection
            .projects_by_id()
            .into_iter()
            .collect();
        let new_projects: FxHashMap<Id, Rc<Project>> = new_snapshot
            .project_collection
            .projects_by_id()
            .into_iter()
            .collect();
        let old_open_projects = old_snapshot
            .project_collection
            .get_open_configured_projects();
        let new_open_projects = new_snapshot
            .project_collection
            .get_open_configured_projects();

        for (id, added_project) in &new_projects {
            if old_projects.contains_key(id) {
                continue;
            }
            let Some(configured_id) = added_project.id.configured() else {
                continue;
            };
            if !should_publish_program_diagnostics(added_project, new_snapshot.id)
                || !new_open_projects.has(&configured_id)
            {
                continue;
            }
            self.publish_project_diagnostics(
                added_project,
                added_project.get_project_diagnostics(),
                new_snapshot,
            );
        }
        for (id, removed_project) in &old_projects {
            if new_projects.contains_key(id) || removed_project.kind != Kind::Configured {
                continue;
            }
            self.publish_project_diagnostics(removed_project, Vec::new(), old_snapshot);
        }
        for (id, new_project) in &new_projects {
            // Go's "common" callback receives `oldProject` but ignores it.
            let Some(_old_project) = old_projects.get(id) else {
                continue;
            };
            let Some(configured_id) = new_project.id.configured() else {
                continue;
            };
            if should_publish_program_diagnostics(new_project, new_snapshot.id)
                && new_open_projects.has(&configured_id)
            {
                self.publish_project_diagnostics(
                    new_project,
                    new_project.get_project_diagnostics(),
                    new_snapshot,
                );
            }
        }
        // Sync diagnostics for projects whose open-file state changed
        // without a program update.
        for (project_id, new_project) in &new_projects {
            if new_project.kind != Kind::Configured {
                continue;
            }
            let Some(old_project) = old_projects.get(project_id) else {
                continue; // Handled by added project case above
            };
            let Some(configured_id) = new_project.id.configured() else {
                continue;
            };
            let new_has_open_files = new_open_projects.has(&configured_id);
            let old_has_open_files = old_open_projects.has(&configured_id);
            if new_has_open_files
                && !old_has_open_files
                && (Rc::ptr_eq(new_project, old_project)
                    || !should_publish_program_diagnostics(new_project, new_snapshot.id))
            {
                // Project reopened without a program update.
                self.publish_project_diagnostics(
                    new_project,
                    new_project.get_project_diagnostics(),
                    new_snapshot,
                );
            } else if !new_has_open_files && old_has_open_files {
                // Project closed.
                self.publish_project_diagnostics(new_project, Vec::new(), new_snapshot);
            }
        }
        let _ = ctx;
    }

    /// `s.publishProjectDiagnostics` — `project` supplies the config-file
    /// URI and (Go's diagnostic file pointers) the program's node arenas.
    fn publish_project_diagnostics(
        &self,
        project: &Rc<Project>,
        diagnostics: Vec<tsc_ast::diagnostic::DiagnosticRef>,
        snapshot: &Snapshot,
    ) {
        let diagnostics = if self.config().validate_enabled == tsc_core::tristate::TS_FALSE {
            Vec::new()
        } else {
            diagnostics
        };
        let ctx = self.with_current_locale(self.background_context());
        let converters = snapshot.converters();
        let mut lsp_diagnostics = Vec::with_capacity(diagnostics.len());
        for diag in &diagnostics {
            let node_id = tsc_ast::diagnostic::lock_diagnostic(diag)
                .file()
                .and_then(|f| f.node);
            let nodes = node_id
                .and_then(|n| project.program.as_ref().map(|p| p.nodes(n.file_index())))
                .unwrap_or_default();
            lsp_diagnostics.push(diagnostic_to_lsp_push(&ctx, &converters, diag, &nodes));
        }

        if let Some(client) = &self.client
            && let Err(err) = client.publish_diagnostics(
                &ctx,
                &PublishDiagnosticsParams {
                    uri: tsc_lsconv::file_name_to_document_uri(&project.config_file_name()),
                    diagnostics: Some(lsp_diagnostics),
                    version: None,
                },
            )
            && self.options.logging_enabled
        {
            self.logger
                .logf(format_args!("Error publishing diagnostics: {}", err));
        }
    }

    /// `s.EnqueuePublishGlobalDiagnostics` — coalesced via
    /// `globalDiagPublishPending`.
    pub fn enqueue_publish_global_diagnostics(self: &Arc<Self>) {
        if !self.options.push_diagnostics_enabled
            || self.config().validate_enabled == tsc_core::tristate::TS_FALSE
        {
            return;
        }
        if self
            .global_diag_publish_pending
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            let ctx = self.background_context();
            let me = Arc::downgrade(self);
            self.background_queue.enqueue(&ctx, move |ctx| {
                if let Some(me) = me.upgrade() {
                    me.publish_global_diagnostics(ctx);
                }
            });
        }
    }

    /// `s.publishGlobalDiagnostics`.
    fn publish_global_diagnostics(self: &Arc<Self>, ctx: &Context) {
        self.global_diag_publish_pending
            .store(false, Ordering::SeqCst);
        let snapshot = self.snapshot();
        for project in snapshot.project_collection.projects() {
            if project.kind != Kind::Configured || project.checker_pool.is_none() {
                continue;
            }
            if project
                .checker_pool
                .as_ref()
                .unwrap()
                .take_new_global_diagnostics()
            {
                self.publish_project_diagnostics(
                    &project,
                    project.get_project_diagnostics(),
                    &snapshot,
                );
            }
        }
        let _ = ctx;
    }

    /// `s.triggerATAForUpdatedProjects`.
    fn trigger_ata_for_updated_projects(self: &Arc<Self>, new_snapshot: &Arc<Snapshot>) {
        for project in new_snapshot.project_collection.projects() {
            if !project.should_trigger_ata(new_snapshot.id) {
                continue;
            }
            let ctx = self.background_context();
            let me = Arc::downgrade(self);
            let project = SendShared(project.clone());
            self.background_queue.enqueue(&ctx, move |ctx| {
                let Some(me) = me.upgrade() else { return };
                let project = &project.into_inner();
                let log_tree = if me.options.logging_enabled {
                    LogTree::new_log_tree(format!(
                        "Triggering ATA for project {}",
                        project.id
                    ))
                } else {
                    LogTree::none()
                };

                let typings_info = project.compute_typings_info();
                let request = TypingsInstallRequest {
                    project_id: project.id.to_string(),
                    typings_info: typings_info.clone(),
                    file_names: project
                        .program
                        .as_ref()
                        .map(|p| {
                            p.source_files()
                                .iter()
                                .map(|file| {
                                    p.nodes(file.file_index())[*file]
                                        .as_source_file()
                                        .file_name
                                        .clone()
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    project_root_path: project.project_directory.clone(),
                    fs: me.fs.clone(),
                    logger: Arc::new(log_tree.clone()) as Arc<dyn Logger>,
                };

                let project_display_name =
                    project.display_name(&me.options.current_directory);
                if let Some(client) = &me.client {
                    client.progress_start(
                        &tsc_diagnostics::Installing_types_for_0,
                        &[project_display_name.clone()],
                    );
                }
                let result = me
                    .typings_installer
                    .as_ref()
                    .map(|installer| installer.install_typings(ctx, &request));
                if let Some(client) = &me.client {
                    client.progress_finish(
                        &tsc_diagnostics::Installing_types_for_0,
                        &[project_display_name],
                    );
                }
                match result {
                    Some(Err(err)) => {
                        if log_tree.is_some() {
                            me.logger.log(format_args!(
                                "ATA installation failed for project {}: {}",
                                project.id, err
                            ));
                            me.logger.log(format_args!("{}", log_tree));
                        }
                    }
                    Some(Ok(result)) => {
                        if result.typings_files != project.typings_files {
                            let mut pending = me.pending_ata_changes.lock().unwrap();
                            pending.insert(
                                project.id.clone(),
                                AtaStateChange {
                                    typings_info: Some(typings_info),
                                    typings_files: result.typings_files,
                                    typings_files_to_watch: result.files_to_watch,
                                    logs: log_tree,
                                },
                            );
                            drop(pending);
                            me.schedule_diagnostics_refresh(me.options.debounce_delay);
                        }
                    }
                    None => {}
                }
            });
        }
    }

    /// `s.warmAutoImportCache` — when a single open file changed, clone the
    /// snapshot with auto-import preparation on a cancellable context and
    /// adopt it if the session hasn't moved on.
    fn warm_auto_import_cache(
        self: &Arc<Self>,
        ctx: &Context,
        changed_uris: &Set<DocumentUri>,
        _old_snapshot: &Arc<Snapshot>,
        new_snapshot: &Arc<Snapshot>,
    ) {
        if changed_uris.len() != 1 {
            return;
        }
        let changed_file = changed_uris.keys().iter().next().unwrap().clone();
        if !new_snapshot.is_open_file(&changed_file.file_name()) {
            return;
        }
        let prefs = new_snapshot.user_preferences();
        if prefs.completion_preferences.include_completions_for_module_exports == tsc_core::tristate::TS_FALSE {
            return;
        }
        let Some(project) = new_snapshot.get_default_project(&changed_file) else {
            return;
        };
        if new_snapshot
            .auto_import_registry()
            .is_some_and(|registry| {
                registry.is_prepared_for_importing_file(
                    &changed_file.file_name(),
                    &ProjectId(Rc::from(project.id.as_str())),
                    prefs,
                )
            })
        {
            return;
        }

        // Cancel any previous auto-import warming and create a new
        // cancellable context.
        let (warm_ctx, cancel) = ctx.with_cancel();
        {
            let mut warm = self.warm_auto_import_cancel.lock().unwrap();
            if let Some(prev) = warm.take() {
                prev();
            }
            if !warm_ctx.is_cancelled() {
                let logger = self.logger.clone();
                let file_name = changed_file.file_name().as_string().to_string();
                let warm_ctx_inner = warm_ctx.clone();
                warm.replace(Arc::new(move || {
                    if warm_ctx_inner.is_cancelled() {
                        return;
                    }
                    logger.logf(format_args!(
                        "Cancelling auto-import warming for file {}",
                        file_name
                    ));
                    cancel.cancel();
                }));
            }
        }

        if warm_ctx.is_cancelled() {
            return;
        }

        // Clone the snapshot with auto-imports using `warm_ctx` so the
        // expensive extraction work is cancelled if a file change arrives.
        // This runs inline — `warm_auto_import_cache` itself is called from
        // a background-queue task (Go's warmAutoImportCache body).
        let warm_change = SnapshotChange {
            reason: UpdateReason::RequestedLanguageServiceWithAutoImports,
            documents: vec![changed_file.clone()],
            auto_imports: changed_file,
            ..Default::default()
        };
        let cloned_snapshot = new_snapshot.clone(
            &warm_ctx,
            warm_change,
            new_snapshot.overlays(),
            Some(&self.logger),
            self.client.as_ref(),
        );

        // If cancelled during clone, discard the incomplete result.
        if warm_ctx.is_cancelled() {
            return;
        }
        // Conditionally adopt: if the session hasn't moved past
        // `new_snapshot`, promote the clone so future requests benefit from
        // the warmed cache.
        self.adopt_snapshot_change(new_snapshot, &cloned_snapshot);
    }

    /// `s.Close`.
    pub fn close(&self) {
        self.cancel_scheduled_snapshot_update();
        self.cancel_diagnostics_refresh();
        self.cancel_warm_auto_import_cache();
        self.close_idle_cache_clean();
        self.stop_performance_telemetry();
        self.background_cancel.cancel();
        self.background_queue.close();

        let _update_guard = self.snapshot_update_mu.lock().unwrap();
        let snapshot = self.snapshot.write().unwrap().take();
        drop(snapshot); // releases the session's reference (Go: snapshot.Deref())

        self.host.close();
    }

    /// `s.logProjectChanges` — logs projects added/removed/updated between
    /// snapshots.
    fn log_project_changes(&self, old_snapshot: &Snapshot, new_snapshot: &Snapshot) {
        let mut logged_project_changes = false;
        let mut log_project = |project: &Rc<Project>| {
            let builder = project.print(
                self.logger.is_verbose(),
                self.logger.is_verbose(),
            );
            self.logger.log(format_args!("{}", builder));
            logged_project_changes = true;
        };

        let old_projects: Vec<(Id, Rc<Project>)> =
            old_snapshot.project_collection.projects_by_id();
        let new_projects: Vec<(Id, Rc<Project>)> =
            new_snapshot.project_collection.projects_by_id();
        let old_map: FxHashMap<Id, Rc<Project>> = old_projects.into_iter().collect();

        for (id, new_project) in &new_projects {
            match old_map.get(id) {
                None => log_project(new_project), // New project added
                Some(old_project) => {
                    // Project updated — log only on new-files program update.
                    if new_project.program_update_kind == ProgramUpdateKind::NewFiles
                        && !Rc::ptr_eq(new_project, old_project)
                    {
                        log_project(new_project);
                    }
                }
            }
        }
        let new_ids: std::collections::HashSet<Id> =
            new_projects.iter().map(|(id, _)| id.clone()).collect();
        for (id, removed_project) in &old_map {
            if !new_ids.contains(id) {
                self.logger.logf(format_args!(
                    "\nProject '{}' removed\n{}",
                    removed_project.id, SESSION_HR
                ));
                logged_project_changes = true;
            }
        }

        if logged_project_changes || self.logger.is_verbose() {
            self.log_cache_stats(new_snapshot);
        }
    }

    /// `s.logCacheStats`.
    fn log_cache_stats(&self, snapshot: &Snapshot) {
        let mut parse_cache_size = 0usize;
        let mut extended_config_count = 0usize;
        if self.logger.is_verbose() {
            parse_cache_size = self.host.parse_cache.entry_count();
            extended_config_count = self.host.extended_config_cache.entry_count();
        }
        self.logger.log(format_args!("\n======== Cache Statistics ========"));
        self.logger.logf(format_args!(
            "Open file count:   {:6}",
            snapshot.overlays().len()
        ));
        self.logger.logf(format_args!(
            "Cached disk files: {:6}",
            snapshot.fs.cache_files.len()
        ));
        self.logger.logf(format_args!(
            "Realpath aliases:  {:6}",
            snapshot.fs.node_modules_realpath_aliases.len()
        ));
        self.logger.logf(format_args!(
            "Project count:     {:6}",
            snapshot.project_collection.projects().len()
        ));
        self.logger.logf(format_args!(
            "Config count:      {:6}",
            snapshot.config_file_registry.configs.len()
        ));
        if self.logger.is_verbose() {
            self.logger.logf(format_args!(
                "Parse cache size:           {:6}",
                parse_cache_size
            ));
            self.logger.logf(format_args!(
                "Program count:              {:6}",
                self.host.program_counter.len()
            ));
            self.logger.logf(format_args!(
                "Extended config cache size: {:6}",
                extended_config_count
            ));

            self.logger.log(format_args!("Auto Imports:"));
            let auto_import_stats =
                tsc_ls::host::Host::auto_import_registry(snapshot).get_cache_stats();
            self.logger.logf(format_args!(
                "\tUnique packages (by realpath): {}",
                auto_import_stats.unique_package_count
            ));
            if !auto_import_stats.project_buckets.is_empty() {
                self.logger.log(format_args!("\tProject buckets:"));
                for bucket in &auto_import_stats.project_buckets {
                    self.logger.logf(format_args!(
                        "\t\t{}{}:",
                        bucket.name,
                        if bucket.state.dirty() { " (dirty)" } else { "" }
                    ));
                    self.logger.logf(format_args!("\t\t\tFiles: {}", bucket.file_count));
                    self.logger
                        .logf(format_args!("\t\t\tExports: {}", bucket.export_count));
                }
            }
            if !auto_import_stats.node_modules_buckets.is_empty() {
                self.logger.log(format_args!("\tnode_modules buckets:"));
                for bucket in &auto_import_stats.node_modules_buckets {
                    self.logger.logf(format_args!(
                        "\t\t{}{}:",
                        bucket.name,
                        if bucket.state.dirty() { " (dirty)" } else { "" }
                    ));
                    if let Some(dirty_packages) = &bucket.state.dirty_packages {
                        for package_name in dirty_packages.keys() {
                            self.logger.logf(format_args!(
                                "\t\t\tNeeds granular update: {}",
                                package_name
                            ));
                        }
                    }
                    if let Some(dependency_names) = &bucket.dependency_names {
                        self.logger.logf(format_args!(
                            "\t\t\tCollected packages: {}",
                            dependency_names.len()
                        ));
                    } else {
                        self.logger.logf(format_args!(
                            "\t\t\tCollected packages: all, due to no package.json!"
                        ));
                    }
                    self.logger.logf(format_args!(
                        "\t\t\tTotal packages: {}",
                        bucket.package_names.as_ref().map_or(0, |p| p.len())
                    ));
                    self.logger.logf(format_args!("\t\t\tFiles: {}", bucket.file_count));
                    self.logger
                        .logf(format_args!("\t\t\tExports: {}", bucket.export_count));
                    match &bucket.state.recursive_search_packages {
                        None => self
                            .logger
                            .log(format_args!("\t\t\tRecursive search: all")),
                        Some(packages) if !packages.is_empty() => {
                            self.logger.logf(format_args!(
                                "\t\t\tRecursive search: {} packages",
                                packages.len()
                            ));
                        }
                        _ => self
                            .logger
                            .log(format_args!("\t\t\tRecursive search: none")),
                    }
                }
            }
        }
    }
}

/// Go's `(*Snapshot, *Project, *ls.LanguageService)` triples — the
/// `LanguageService` borrows the snapshot's `ls.Host`, so Rust carries the
/// owning `Arc`s and builds services on demand.
pub struct SessionLanguageService {
    pub snapshot: Arc<Snapshot>,
    pub project: Rc<Project>,
    /// `activeFile` — the file whose preferences configure the service.
    pub active_file: String,
}

impl SessionLanguageService {
    /// `ls.NewLanguageService(project.ID(), project.GetProgram(), snapshot,
    /// activeFile)`.
    pub fn language_service(&self) -> LanguageService<'_> {
        new_language_service(
            ProjectId(Rc::from(self.project.id.as_str())),
            self.project.get_program().unwrap().clone(),
            &*self.snapshot,
            &self.active_file,
        )
    }

    /// The program backing the service (Go `project.GetProgram()`).
    pub fn program(&self) -> Rc<Program> {
        self.project.get_program().unwrap().clone()
    }
}

/// `func deferCancel(cancel)` — `defer cancel()` as a drop guard for queue
/// tasks.
fn defer_cancel(cancel: CancelFunc) -> impl Drop {
    struct Guard(Option<CancelFunc>);
    impl Drop for Guard {
        fn drop(&mut self) {
            if let Some(cancel) = self.0.take() {
                cancel.cancel();
            }
        }
    }
    let _ = &cancel; // keep the binding live past capture
    Guard(Some(cancel))
}

/// Drop guard for the idle-cache-clean wait group — `wg.Done()` on scope
/// exit (Go's `defer s.idleCacheCleanWG.Done()`).
struct IdleWgGuard<'a> {
    wg: &'a IdleCacheCleanWg,
}
impl Drop for IdleWgGuard<'_> {
    fn drop(&mut self) {
        self.wg.done();
    }
}

/// `hr` — the horizontal rule logged between project dumps.
const SESSION_HR: &str = "-----------------------------------------------";

/// `shouldPublishProgramDiagnostics`.
fn should_publish_program_diagnostics(p: &Rc<Project>, snapshot_id: u64) -> bool {
    p.kind == Kind::Configured
        && p.program.is_some()
        && p.program_last_update == snapshot_id
        && p.program_update_kind as u8 > ProgramUpdateKind::Cloned as u8
}

/// `hasContentMapperOperationTimings`.
fn has_content_mapper_operation_timings(
    timings: &FxHashMap<String, tsc_contentmapper::MapperTimings>,
) -> bool {
    timings.values().any(has_content_mapper_operation_timing)
}

/// `hasContentMapperOperationTiming`.
fn has_content_mapper_operation_timing(timing: &tsc_contentmapper::MapperTimings) -> bool {
    timing.spawn.count != 0
        || timing.open_project.count != 0
        || timing.close_project.count != 0
        || timing.transform.count != 0
}

/// `countFileStats` — file-count/size measurements for project telemetry.
fn count_file_stats(program: &Program) -> ProjectInfoTelemetryMeasurements {
    let mut measurements = ProjectInfoTelemetryMeasurements::default();
    for file in program.source_files() {
        let nodes = program.nodes(file.file_index());
        let source_file = nodes[file].as_source_file();
        let size = nodes[file].end() as f64;
        match source_file.script_kind {
            k if k == ScriptKind::Js => {
                measurements.js_file_count += 1.0;
                measurements.js_file_size += size;
            }
            k if k == ScriptKind::Jsx => {
                measurements.jsx_file_count += 1.0;
                measurements.jsx_file_size += size;
            }
            k if k == ScriptKind::Ts => {
                measurements.ts_file_count += 1.0;
                measurements.ts_file_size += size;
            }
            k if k == ScriptKind::Tsx => {
                measurements.tsx_file_count += 1.0;
                measurements.tsx_file_size += size;
            }
            _ if source_file.is_declaration_file => {
                measurements.dts_file_count += 1.0;
                measurements.dts_file_size += size;
            }
            _ => {}
        }
    }
    measurements
}
