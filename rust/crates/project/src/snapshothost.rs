// Ported from tsc/internal/project/snapshothost.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `SnapshotHost` owns the services shared by a collection of immutable
// snapshots: session options, host filesystem, parse caches, extended
// config cache, program counter, and the content mapper host.

use std::cell::Cell;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use rustc_hash::FxHashMap;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_contentmapper::ParsedSourceFile;
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_lsproto::{DocumentUri, WatchKind};
use tsc_lsutil::new_default_user_preferences;
use tsc_project_logging::Logger;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath};
use tsc_vfs::Vfs;

use crate::configfileregistry::ConfigFileRegistry;
use crate::extendedconfigcache::{ExtendedConfigCache, new_extended_config_cache};
use crate::filechange::FileChangeSummary;
use crate::overlayfs::new_overlay_fs;
use crate::parsecache::{
    ContentMappedParseCache, ParseCache, ParseCacheKey, new_content_mapped_parse_cache,
    new_parse_cache, new_parse_cache_key,
};
use crate::programcounter::ProgramCounter;
use crate::projectcollection::{ApiState, ProjectCollection, open_file_paths};
use crate::refcountcache::RefCountCacheOptions;
use crate::session::{SessionInit, SessionOptions, UpdateReason, new_content_mapper_host};
use crate::snapshot::{
    ApiSnapshotRequest, NodeModulesDirectories, Snapshot, SnapshotChange,
};
use crate::snapshotfs::SnapshotFs;
use crate::watch::{
    PatternsAndIgnored, WatchedFiles, get_recursive_glob_pattern, new_watched_files,
};

/// `SourceFileLease` — a parse-cache reference acquired by the host;
/// `release` derefs it exactly once (Go `releaseOnce sync.Once` →
/// `Cell<bool>` — the lease is single-threaded like the rest of the
//  pipeline).
pub struct SourceFileLease {
    cache: Rc<ParseCache>,
    key: ParseCacheKey,
    source_file: Arc<Mutex<ParsedSourceFile>>,
    released: Cell<bool>,
}

impl SourceFileLease {
    /// `l.SourceFile` — the leased (file, arena) pair standing in for Go's
    /// `*ast.SourceFile`.
    pub fn source_file(&self) -> &Arc<Mutex<ParsedSourceFile>> {
        &self.source_file
    }

    /// `l.Release`.
    pub fn release(&self) {
        if !self.released.replace(true) {
            self.cache.deref(&self.key);
        }
    }
}

/// `SnapshotHost` owns the services shared by a collection of immutable
/// snapshots.
pub struct SnapshotHost {
    /// `options`.
    pub options: Arc<SessionOptions>,
    /// `caseSensitivity`.
    pub case_sensitivity: CaseSensitivity,
    /// `fs` — the session host filesystem (Go `vfs.FS`).
    pub fs: Arc<dyn Vfs>,

    /// `parseCache`.
    pub parse_cache: Rc<ParseCache>,
    /// `contentMappedParseCache`.
    pub content_mapped_parse_cache: Rc<ContentMappedParseCache>,
    /// `extendedConfigCache`.
    pub extended_config_cache: Rc<ExtendedConfigCache>,
    /// `programCounter`.
    pub program_counter: ProgramCounter,
    /// `contentMapperHost` — `None` when the workspace is untrusted or no
    /// spawner is available (Go nil).
    pub content_mapper_host: Option<Arc<dyn tsc_contentmapper::Host>>,

    /// `snapshotID`.
    snapshot_id: AtomicU64,
}

impl SnapshotHost {
    /// `s.nextSnapshotID`.
    pub fn next_snapshot_id(&self) -> u64 {
        self.snapshot_id.fetch_add(1, Ordering::SeqCst) + 1
    }

    /// `s.AcquireSourceFile`.
    pub fn acquire_source_file(
        &self,
        options: SourceFileParseOptions,
        text: String,
        script_kind: ScriptKind,
    ) -> SourceFileLease {
        let file_handle =
            crate::overlayfs::new_cached_file_handle(options.file_name.clone(), text);
        let key = new_parse_cache_key(options, file_handle.hash(), script_kind);
        SourceFileLease {
            cache: self.parse_cache.clone(),
            source_file: self.parse_cache.acquire(key.clone(), &file_handle),
            key,
            released: Cell::new(false),
        }
    }

    /// `s.AcquireExistingSourceFile` — `None` is Go's nil return.
    pub fn acquire_existing_source_file(&self, key: &ParseCacheKey) -> Option<SourceFileLease> {
        let source_file = self.parse_cache.acquire_existing(key)?;
        Some(SourceFileLease {
            cache: self.parse_cache.clone(),
            key: key.clone(),
            source_file,
            released: Cell::new(false),
        })
    }

    /// `s.NewRootSnapshot` creates an independent root snapshot.
    pub fn new_root_snapshot(self: &Arc<Self>) -> Arc<Snapshot> {
        self.new_root_snapshot_with(0, false)
    }

    /// `s.RetainSnapshot` adds a reference to a snapshot owned by this host.
    pub fn retain_snapshot(&self, snapshot: &Snapshot) {
        snapshot.ref_();
    }

    /// `s.CloneSnapshot` derives a snapshot from `base_snapshot` without
    /// adopting it as any canonical session state or performing session
    /// side effects. Returns the snapshot and its `apiError` (Go's
    /// `(*Snapshot, error)` pair).
    pub fn clone_snapshot(
        &self,
        ctx: &Context,
        base_snapshot: &Arc<Snapshot>,
        file_changes: FileChangeSummary,
        api_request: Option<Rc<ApiSnapshotRequest>>,
    ) -> (Arc<Snapshot>, Option<String>) {
        let mut change = SnapshotChange {
            file_changes,
            ..Default::default()
        };
        if let Some(api_request) = api_request {
            change.api_request = Some(api_request.clone());
            change.fs = api_request
                .file_system
                .clone()
                .map(crate::overlayfs::LayeredFsInput::Plain);
            change.file_system_override = api_request.file_system.is_some();
            change.replace_file_system = api_request.replace_file_system;
            change.new_config = api_request.user_preferences.clone();
            if !api_request.prepare_auto_imports.as_str().is_empty() {
                change.set_resource_request(
                    base_snapshot.resource_request_for_document(&api_request.prepare_auto_imports),
                );
                change.auto_imports = api_request.prepare_auto_imports.clone();
            }
        }
        let snapshot = self.update(ctx, base_snapshot, change);
        let api_error = snapshot.api_error().map(str::to_owned);
        (snapshot, api_error)
    }

    /// `s.update` derives a snapshot from `base_snapshot` without adopting
    /// it as any canonical session state or performing session side
    /// effects.
    pub fn update(
        &self,
        ctx: &Context,
        base_snapshot: &Arc<Snapshot>,
        change: SnapshotChange,
    ) -> Arc<Snapshot> {
        base_snapshot.clone(ctx, change, base_snapshot.overlays(), None, None)
    }

    /// `s.CloneSnapshotWithAutoImports` derives a snapshot with auto-import
    /// preparation without adopting the clone in the background.
    pub fn clone_snapshot_with_auto_imports(
        &self,
        ctx: &Context,
        base_snapshot: &Arc<Snapshot>,
        uri: &DocumentUri,
        logger: Option<&Arc<dyn Logger>>,
    ) -> Arc<Snapshot> {
        let mut change = SnapshotChange {
            reason: UpdateReason::RequestedLanguageServiceWithAutoImports,
            fs: Some(crate::overlayfs::LayeredFsInput::Layered(
                base_snapshot.fs.fs.clone(),
            )),
            file_system_override: base_snapshot.has_file_system_override(),
            ..Default::default()
        };
        change.set_resource_request(base_snapshot.resource_request_for_document(uri));
        change.auto_imports = uri.clone();
        base_snapshot.clone(ctx, change, base_snapshot.overlays(), logger, None)
    }

    /// `s.newRootSnapshot` — `id` seeds the snapshot ID (0 for fresh
    /// sessions); `relative_pattern_support` comes from the client's
    /// `didChangeWatchedFiles` capabilities.
    pub(crate) fn new_root_snapshot_with(
        self: &Arc<Self>,
        id: u64,
        relative_pattern_support: bool,
    ) -> Arc<Snapshot> {
        let file_system: Arc<dyn crate::overlayfs::LayeredFileSystem> = Arc::new(
            new_overlay_fs(
                self.fs.clone(),
                None,
                FxHashMap::default(),
                self.options.position_encoding.clone(),
            ),
        );
        Arc::new(self.new_snapshot(
            id,
            Arc::new(SnapshotFs {
                case_sensitivity: self.case_sensitivity,
                fs: file_system,
                cache_files: FxHashMap::default(),
                cache_directories: FxHashMap::default(),
                read_files: Default::default(),
                node_modules_realpath_aliases: FxHashMap::default(),
            }),
            ConfigFileRegistry::default(),
            None,
            new_default_user_preferences(),
            None,
            Some(new_watched_files(
                "auto-import",
                WatchKind(
                    WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0,
                ),
                relative_pattern_support,
                NodeModulesDirectories::default(),
                |node_modules_dirs| {
                    let mut patterns: Vec<String> = node_modules_dirs
                        .values()
                        .map(get_recursive_glob_pattern)
                        .collect();
                    patterns.sort();
                    PatternsAndIgnored {
                        patterns_inside_workspace: patterns,
                        ..Default::default()
                    }
                },
            )),
        ))
    }

    /// `(host *SnapshotHost) newSnapshot`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_snapshot(
        self: &Arc<Self>,
        id: u64,
        fs: Arc<SnapshotFs>,
        config_file_registry: ConfigFileRegistry,
        compiler_options_for_inferred_projects: Option<Arc<CompilerOptions>>,
        user_preferences: tsc_lsutil::UserPreferences,
        auto_imports: Option<Rc<tsc_ls::autoimport::Registry>>,
        auto_imports_watch: Option<Arc<WatchedFiles<NodeModulesDirectories>>>,
    ) -> Snapshot {
        let overlays = fs.fs.overlays();
        Snapshot {
            host: self.clone(),
            id,
            parent_id: 0,
            ref_count: std::sync::atomic::AtomicI32::new(1),
            line_maps: elsa::FrozenMap::new(),
            fs,
            project_collection: Rc::new(ProjectCollection {
                case_sensitivity: self.case_sensitivity,
                config_file_registry: None,
                file_default_projects: FxHashMap::default(),
                configured_projects: FxHashMap::default(),
                synthetic_projects: FxHashMap::default(),
                open_files: open_file_paths(&overlays),
                inferred_project: None,
                api_state: ApiState::default(),
                open_configured_projects: OnceLock::new(),
            }),
            config_file_registry,
            auto_imports,
            auto_imports_watch,
            compiler_options_for_inferred_projects,
            inferred_project_content_mappers: Vec::new(),
            inferred_project_content_mapper_extensions: Vec::new(),
            user_preferences,
            content_mapper_watch_state: OnceLock::new(),
            builder_logs: Default::default(),
            api_error: None,
            file_system_override: false,
            created_programs: Vec::new(),
        }
    }

    /// `s.FS`.
    pub fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }

    /// `s.GetCurrentDirectory`.
    pub fn get_current_directory(&self) -> RootedDirectoryPath {
        self.options.current_directory.clone()
    }

    /// `s.DefaultLibraryPath`.
    pub fn default_library_path(&self) -> RootedDirectoryPath {
        self.options.default_library_path.clone()
    }

    /// `s.Close`.
    pub fn close(&self) {
        if let Some(host) = &self.content_mapper_host {
            let _ = host.close();
        }
    }
}

/// `NewSnapshotHost`.
pub fn new_snapshot_host(init: &SessionInit) -> Arc<SnapshotHost> {
    let parse_cache = init
        .parse_cache
        .clone()
        .unwrap_or_else(|| Rc::new(new_parse_cache(RefCountCacheOptions::default())));
    let content_mapped_parse_cache = init
        .content_mapped_parse_cache
        .clone()
        .unwrap_or_else(|| {
            Rc::new(new_content_mapped_parse_cache(
                RefCountCacheOptions::default(),
            ))
        });

    Arc::new(SnapshotHost {
        options: init.options.clone(),
        case_sensitivity: init.fs.case_sensitivity(),
        fs: init.fs.clone(),
        parse_cache,
        content_mapped_parse_cache,
        extended_config_cache: Rc::new(new_extended_config_cache()),
        program_counter: ProgramCounter::new(),
        content_mapper_host: new_content_mapper_host(init),
        snapshot_id: AtomicU64::new(0),
    })
}
