// Ported from tsc/internal/project/snapshot.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Immutable session snapshot: layered filesystem, project collection,
// config-file registry, auto-import registry, user preferences, and
// atomic refcounted lifetime. `Snapshot` is shared via `Arc` —
// `ref`/`try_ref`/`deref` mirror Go's `refCount`/`Deref`/`dispose`.
//
// PORT: the Go pipeline is single-threaded, so project-layer values are
// `Rc` (see `checkerpool.rs`); `Snapshot` is therefore `!Send`/`!Sync` like
// the compiler objects it holds. The atomic refcount still mirrors Go's
// `atomic.Int32` semantics and the panics on misuse.

use std::rc::Rc;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::Instant;

use elsa::FrozenMap;
use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_collections::Set;
use tsc_contentmapper::Mapper;
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::projectreference::ProjectReference;
use tsc_lsconv::{Converters, LspLineMap, new_converters};
use tsc_lsproto::DocumentUri;
use tsc_lsutil::UserPreferences;
use tsc_module::cache::ResolverOptions;
use tsc_module::types::Resolver;
use tsc_project_logging::{LogTree, Logger};
use tsc_sourcemap::EcmaLineInfo;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::{Vfs, vfsmatch};

use crate::ata::TypingsInfo;
use crate::autoimport::new_auto_import_registry_clone_host;
use crate::client::Client;
use crate::configfileregistry::ConfigFileRegistry;
use crate::filechange::FileChangeSummary;
use crate::overlayfs::{
    FileHandle, LayeredFileSystem, LayeredFsInput, Overlay, layer_overlay_file_system,
    layered_as_vfs,
};
use crate::parsecache::{
    content_mapped_parse_cache_key_for_duplicate, content_mapped_parse_cache_key_for_file,
    parse_cache_key_for_duplicate, parse_cache_key_for_file,
};
use crate::project::{Id, ProgramUpdateKind, Project, SyntheticProjectId};
use crate::projectcollection::ProjectCollection;
use crate::projectcollectionbuilder::new_project_collection_builder;
use crate::session::{ContentMapperContributions, UpdateReason};
use crate::snapshotfs::{
    FileSource, SnapshotFs, SnapshotFsBuilder, SourceFs, new_snapshot_fs_builder_from_source,
    new_source_fs,
};
use crate::snapshothost::SnapshotHost;
use crate::watch::WatchedFiles;

/// `emptyLspLineMap` — Go's `getLineMap` may return nil, which would
/// nil-deref inside `lsconv`; a shared empty map is the least-surprise
/// stand-in for a missing file.
static EMPTY_LSP_LINE_MAP: LspLineMap = LspLineMap {
    line_starts: Vec::new(),
    ascii_only: true,
};

/// `AutoImportsWatchInput` — `map[tspath.PathKey]tspath.RootedDirectoryPath`.
pub type NodeModulesDirectories = FxHashMap<PathKey, RootedDirectoryPath>;

/// `Snapshot` (snapshot.go).
pub struct Snapshot {
    /// `host`.
    pub host: Arc<SnapshotHost>,
    /// `id`.
    pub(crate) id: u64,
    /// `parentId`.
    pub(crate) parent_id: u64,
    /// `refCount`.
    pub(crate) ref_count: AtomicI32,

    /// `converters` — `lsconv.Converters` borrows `&'a LspLineMap` from the
    /// snapshot's files, so it can't be stored self-referentially. Line
    /// maps are interned here (one per file, matching the Go `fileBase`
    /// cache) and `converters()` builds the `Converters` on demand.
    /// `elsa` requires `StableDeref` values, hence the `Box`.
    pub(crate) line_maps: FrozenMap<PathKey, Box<LspLineMap>>,

    // Immutable state, cloned between snapshots
    /// `fs`.
    pub fs: Arc<SnapshotFs>,
    /// `ProjectCollection`.
    pub project_collection: Rc<ProjectCollection>,
    /// `ConfigFileRegistry`.
    pub config_file_registry: ConfigFileRegistry,
    /// `AutoImports` — the `ls/autoimport` registry for this snapshot.
    /// `Rc` matches the rest of the snapshot graph (see `project_collection`);
    /// snapshots are cross-thread via `Fragile` like programs are.
    pub auto_imports: Option<Rc<tsc_ls::autoimport::Registry>>,
    /// `autoImportsWatch`.
    pub(crate) auto_imports_watch:
        Option<Arc<WatchedFiles<NodeModulesDirectories>>>,
    /// `compilerOptionsForInferredProjects`.
    pub(crate) compiler_options_for_inferred_projects: Option<Arc<CompilerOptions>>,
    /// `inferredProjectContentMappers`.
    pub(crate) inferred_project_content_mappers: Vec<Arc<Mapper>>,
    /// `inferredProjectContentMapperExtensions`.
    pub(crate) inferred_project_content_mapper_extensions: Vec<String>,
    /// `userPreferences`.
    pub(crate) user_preferences: UserPreferences,
    /// `contentMapperWatchStateOnce` — `(extensions, watchedFiles)` filled
    /// once by `content_mapper_watch_state`.
    pub(crate) content_mapper_watch_state: OnceLock<(Vec<String>, Set<PathKey>)>,

    /// `builderLogs`.
    pub(crate) builder_logs: LogTree,
    /// `apiError`.
    pub(crate) api_error: Option<String>,
    /// `fileSystemOverride` indicates that this snapshot was built from a
    /// filesystem supplied by an API update rather than the session host
    /// filesystem.
    pub(crate) file_system_override: bool,

    /// `createdPrograms`.
    pub(crate) created_programs: Vec<Rc<Project>>,
}

/// `snapshotOverlays`.
fn snapshot_overlays(fs: &SnapshotFs) -> FxHashMap<PathKey, Arc<Overlay>> {
    fs.fs.overlays()
}

/// `overlayFileHandles`.
fn overlay_file_handles(
    overlays: &FxHashMap<PathKey, Arc<Overlay>>,
) -> FxHashMap<PathKey, Arc<dyn FileHandle>> {
    overlays
        .iter()
        .map(|(path, overlay)| {
            (
                path.clone(),
                overlay.clone() as Arc<dyn FileHandle>,
            )
        })
        .collect()
}

/// Panic logging guard for Go's `defer/recover` block in `Clone` — on
/// panic while cloning, print the in-progress logs before re-panicking
/// (`Drop` during unwind replaces the recover+panic pair).
struct CloneLogGuard<'a> {
    session_logger: Option<&'a Arc<dyn Logger>>,
    logger: &'a LogTree,
}

impl Drop for CloneLogGuard<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            if let Some(session_logger) = self.session_logger {
                session_logger.log(format_args!("{}", self.logger));
            }
        }
    }
}

impl Snapshot {
    /// `s.contentMapperWatchState()`.
    fn content_mapper_watch_state(&self) -> &(Vec<String>, Set<PathKey>) {
        self.content_mapper_watch_state.get_or_init(|| {
            let mut content_mapper_extensions =
                self.config_file_registry.content_mappers().extensions;
            content_mapper_extensions
                .extend(self.inferred_project_content_mapper_extensions.iter().cloned());
            content_mapper_extensions.sort();
            content_mapper_extensions.dedup();

            let mut content_mapper_watched_files = Set::new();
            for project in self.project_collection.projects() {
                if let Some(files) = &project.content_mapper_watched_files {
                    for path in files.keys() {
                        content_mapper_watched_files.add(path.clone());
                    }
                }
            }
            (content_mapper_extensions, content_mapper_watched_files)
        })
    }

    /// `s.overlays()`.
    pub fn overlays(&self) -> FxHashMap<PathKey, Arc<Overlay>> {
        snapshot_overlays(&self.fs)
    }

    /// `s.CreatedPrograms()`.
    pub fn created_programs(&self) -> &[Rc<Project>] {
        &self.created_programs
    }

    /// `s.resourceRequestForDocument`.
    pub fn resource_request_for_document(&self, uri: &DocumentUri) -> ResourceRequest {
        let path = uri.path_key(self.case_sensitivity());
        let mut request = ResourceRequest {
            documents: vec![uri.clone()],
            ..Default::default()
        };
        for project in self.project_collection.synthetic_projects() {
            if project.contains_file(&path)
                || project.host.as_ref().is_some_and(|host| {
                    host.source_fs().seen_file_or_missing_parent_directory(&path)
                })
            {
                request.projects.push(project.id.clone());
            }
        }
        request
    }

    /// `s.processFileChanges`.
    fn process_file_changes(
        &self,
        fs: &SnapshotFsBuilder,
        mut file_changes: FileChangeSummary,
        logger: &LogTree,
        content_mapper_contributions: Option<&ContentMapperContributions>,
        previous_overlays: &FxHashMap<PathKey, Arc<Overlay>>,
        overlays: &FxHashMap<PathKey, Arc<Overlay>>,
    ) -> FileChangeSummary {
        file_changes = fs.fs.expand_file_changes(file_changes);
        let previous_open_files = overlay_file_handles(previous_overlays);
        let open_files = overlay_file_handles(overlays);
        if file_changes.has_excessive_watch_events() {
            let invalidate_start = Instant::now();
            if file_changes.invalidate_all {
                fs.invalidate_cache();
                logger.logf(format_args!(
                    "InvalidateAll: invalidated file cache in {:?}",
                    invalidate_start.elapsed()
                ));
            } else if !fs.watch_changes_overlap_cache(
                &file_changes,
                &previous_open_files,
                &open_files,
            ) {
                // All watch changes/deletes are files we haven't seen; should
                // be irrelevant to us (probably an external tool's build or
                // something)
                file_changes.changed = Set::new();
                file_changes.deleted = Set::new();
            } else if file_changes.includes_watch_change_outside_node_modules {
                fs.invalidate_cache();
                logger.logf(format_args!(
                    "Excessive watch changes detected, invalidated file cache in {:?}",
                    invalidate_start.elapsed()
                ));
            } else {
                fs.invalidate_node_modules_cache();
                logger.logf(format_args!(
                    "npm install detected, invalidated node_modules cache in {:?}",
                    invalidate_start.elapsed()
                ));
            }
        } else {
            let content_mapper_extensions = match content_mapper_contributions {
                None => self.content_mapper_watch_state().0.clone(),
                Some(contributions) => {
                    let mut extensions =
                        self.config_file_registry.content_mappers().extensions;
                    extensions.extend(contributions.extensions.iter().cloned());
                    extensions
                }
            };
            let content_mapper_watched_files = &self.content_mapper_watch_state().1;
            file_changes = fs.expand_and_filter_watch_events(
                file_changes,
                &content_mapper_extensions,
                Some(content_mapper_watched_files),
                &previous_open_files,
                &open_files,
            );
            file_changes = self.fs.expand_realpath_aliases(file_changes);
            file_changes = fs.mark_dirty_files(file_changes);
            file_changes = fs.convert_open_and_close_to_changes(
                file_changes,
                &previous_open_files,
                &open_files,
            );
        }
        for path in open_files.keys() {
            if let Some(entry) = fs.cache_files.load(path) {
                fs.delete_cache_entry(&entry);
            }
        }
        file_changes
    }

    /// `s.GetDefaultProject`.
    pub fn get_default_project(&self, uri: &DocumentUri) -> Option<Rc<Project>> {
        self.project_collection
            .get_default_project(&uri.path_key(self.case_sensitivity()))
    }

    /// `s.GetLanguageServiceProjectsContainingFile` — does not consider
    /// synthetic projects (ones created by API via `createProgram`).
    ///
    /// PORT: Go returns `[]ls.Project`; `Rc<Project>` stands in until
    /// `tsc-ls` compiles (see `projectcollection.rs`).
    pub fn get_language_service_projects_containing_file(
        &self,
        uri: &DocumentUri,
    ) -> Vec<Rc<Project>> {
        let file_name = uri.file_name();
        let path = self.case_sensitivity().path_key(&file_name.as_path());
        // TODO!! sheetal may be change this to handle symlinks!!
        self.project_collection
            .get_language_service_projects_containing_file(&path)
    }

    /// `s.GetFile`.
    pub fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.fs.get_file(file_name)
    }

    /// `s.LSPLineMap` — `None` is Go's nil return.
    pub fn lsp_line_map(&self, file_name: &RootedFilePath) -> Option<&LspLineMap> {
        let path = self.case_sensitivity().path_key(&file_name.as_path());
        if let Some(map) = self.line_maps.get(&path) {
            return Some(map);
        }
        let file = self.fs.get_file(file_name)?;
        Some(self.line_maps.insert(path, Box::new(file.lsp_line_map().clone())))
    }

    /// `s.GetECMALineInfo` — cloned out of the file's `OnceLock` cache;
    /// `None` is Go's nil.
    pub fn get_ecma_line_info(&self, file_name: &RootedFilePath) -> Option<EcmaLineInfo> {
        self.fs
            .get_file(file_name)
            .map(|file| file.ecma_line_info().clone())
    }

    /// `s.GetPreferences` — `_activeFile` is unused, as in Go.
    pub fn get_preferences(&self, _active_file: &str) -> &UserPreferences {
        &self.user_preferences
    }

    /// `s.UserPreferences`.
    pub fn user_preferences(&self) -> &UserPreferences {
        &self.user_preferences
    }

    /// `s.Converters` — built per call over the interned line maps (Go
    /// stores one `*lsconv.Converters`; construction is a boxed closure, so
    /// per-call is equivalent).
    pub fn converters(&self) -> Converters<'_> {
        new_converters(self.host.options.position_encoding.clone(), |file_name| {
            self.lsp_line_map(file_name).unwrap_or(&EMPTY_LSP_LINE_MAP)
        })
    }

    /// `s.AutoImportRegistry`.
    pub fn auto_import_registry(&self) -> Option<&tsc_ls::autoimport::Registry> {
        self.auto_imports.as_deref()
    }

    /// `s.ID`.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// `s.CaseSensitivity`.
    pub fn case_sensitivity(&self) -> tsc_tspath::CaseSensitivity {
        self.fs.case_sensitivity
    }

    /// `s.isOpenFile`.
    pub fn is_open_file(&self, file_name: &RootedFilePath) -> bool {
        self.overlays()
            .contains_key(&self.case_sensitivity().path_key(&file_name.as_path()))
    }

    /// `s.hasOverlayWithin`.
    pub fn has_overlay_within(&self, path: &PathKey) -> bool {
        for overlay_path in self.overlays().keys() {
            if path.contains_path(overlay_path) {
                return true;
            }
        }
        false
    }

    /// `FileSystem` returns the filesystem backing this snapshot.
    pub fn file_system(&self) -> Arc<dyn LayeredFileSystem> {
        self.fs.fs.clone()
    }

    /// `HasFileSystemOverride` reports whether this snapshot uses an
    /// API-supplied filesystem instead of the session host filesystem.
    pub fn has_file_system_override(&self) -> bool {
        self.file_system_override
    }

    /// `s.ReadFile`.
    pub fn read_file(&self, file_name: &RootedFilePath) -> Option<String> {
        let handle = self.get_file(file_name)?;
        Some(handle.content().to_string())
    }

    /// `s.DirectoryExists`.
    pub fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.fs.fs.directory_exists(path)
    }

    /// `s.FileExists`.
    pub fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.fs.fs.file_exists(path)
    }

    /// `s.GetDirectories`.
    pub fn get_directories(&self, path: &RootedDirectoryPath) -> Vec<String> {
        self.fs.fs.get_accessible_entries(path).directories
    }

    /// `s.ReadDirectory`.
    pub fn read_directory(
        &self,
        path: &RootedDirectoryPath,
        extensions: &[&str],
        excludes: &[String],
        includes: &[String],
        depth: i64,
    ) -> Vec<RootedFilePath> {
        vfsmatch::read_directory(
            &layered_as_vfs(self.fs.fs.clone()),
            path,
            extensions,
            excludes,
            includes,
            depth,
        )
    }

    /// `s.FS` — the snapshot filesystem as a `sourceFS` (Go `vfs.FS`).
    pub fn fs(&self) -> SourceFs {
        new_source_fs(false, self.fs.clone() as Arc<dyn FileSource>)
    }

    /// `s.GetCurrentDirectory`.
    pub fn get_current_directory(&self) -> RootedDirectoryPath {
        self.host.get_current_directory()
    }

    /// `s.ContentMapperExtensions`.
    pub fn content_mapper_extensions(&self) -> &[String] {
        &self.content_mapper_watch_state().0
    }

    /// `s.builderLogs` — the builder logs produced while cloning this
    /// snapshot (`None`-shaped `LogTree` when logging was disabled).
    pub fn builder_logs(&self) -> &LogTree {
        &self.builder_logs
    }

    /// `s.apiError` — the error stored by a failed `HandleAPIRequest`.
    pub fn api_error(&self) -> Option<&str> {
        self.api_error.as_deref()
    }

    /// `s.Clone` derives the next immutable snapshot from this one.
    ///
    /// PORT: `fs`/`overlays`/`client` are `Option`s of Go's nil-able
    /// parameters. The `ProjectCollectionBuilder` calls are sibling stubs
    /// (`unimplemented!`) until `projectcollectionbuilder.go` is ported.
    pub fn clone(
        self: &Arc<Self>,
        ctx: &Context,
        mut change: SnapshotChange,
        overlays: FxHashMap<PathKey, Arc<Overlay>>,
        session_logger: Option<&Arc<dyn Logger>>,
        client: Option<&Arc<dyn Client>>,
    ) -> Arc<Snapshot> {
        if let Some(api_error) = &self.api_error {
            panic!("cannot clone snapshot with API error: {api_error}");
        }
        let store = &self.host;
        let logging = store.options.logging_enabled && session_logger.is_some();
        let mut logger = LogTree::none();
        if logging {
            logger = LogTree::new_log_tree(format!("Cloning snapshot {}", self.id));
        }

        // Print in-progress logs immediately if cloning fails (Go
        // defer/recover).
        let _panic_guard = CloneLogGuard {
            session_logger: if logging { session_logger } else { None },
            logger: &logger,
        };

        if logging {
            let get_details = |change: &SnapshotChange| -> String {
                let mut details = String::new();
                if !change.documents.is_empty() {
                    details += &format!(" Documents: {:?}", change.documents);
                }
                if !change.configured_project_documents.is_empty() {
                    details += &format!(
                        " ConfiguredProjectDocuments: {:?}",
                        change.configured_project_documents
                    );
                }
                if !change.projects.is_empty() {
                    details += &format!(" Projects: {:?}", change.projects);
                }
                if let Some(tree) = &change.project_tree {
                    details += &format!(" ProjectTree: {:?}", tree.projects());
                }
                details
            };
            match change.reason {
                UpdateReason::DidOpenFile => logger.logf(format_args!(
                    "Reason: DidOpenFile - {}",
                    change.file_changes.opened
                )),
                UpdateReason::DidCloseFile => logger.logf(format_args!(
                    "Reason: DidCloseFile - {:?}",
                    change.file_changes.closed.keys()
                )),
                UpdateReason::DidChangeCompilerOptionsForInferredProjects => logger
                    .logf(format_args!(
                        "Reason: DidChangeCompilerOptionsForInferredProjects"
                    )),
                UpdateReason::RequestedLanguageServicePendingChanges => logger.logf(
                    format_args!(
                        "Reason: RequestedLanguageService (pending file changes) - {}",
                        get_details(&change)
                    ),
                ),
                UpdateReason::RequestedLanguageServiceProjectNotLoaded => logger.logf(
                    format_args!(
                        "Reason: RequestedLanguageService (project not loaded) - {}",
                        get_details(&change)
                    ),
                ),
                UpdateReason::RequestedLanguageServiceForFileNotOpen => logger.logf(
                    format_args!(
                        "Reason: RequestedLanguageService (file not open) - {}",
                        get_details(&change)
                    ),
                ),
                UpdateReason::RequestedLanguageServiceProjectDirty => logger.logf(
                    format_args!(
                        "Reason: RequestedLanguageService (project dirty) - {}",
                        get_details(&change)
                    ),
                ),
                UpdateReason::RequestedLoadProjectTree => logger.logf(format_args!(
                    "Reason: RequestedLoadProjectTree - {}",
                    get_details(&change)
                )),
                UpdateReason::IdleCleanDiskCache => {
                    logger.logf(format_args!("Reason: IdleCleanDiskCache"))
                }
                UpdateReason::DidChangeConfigFile => logger.logf(format_args!(
                    "Reason: DidChangeConfigFile - {}",
                    get_details(&change)
                )),
                UpdateReason::DidChangeContentMapperContributions => logger.logf(
                    format_args!(
                        "Reason: DidChangeContentMapperContributions - {}",
                        get_details(&change)
                    ),
                ),
                _ => {}
            }
        }

        let start = Instant::now();
        let mut inferred_content_mappers = self.inferred_project_content_mappers.clone();
        let mut inferred_content_mapper_extensions =
            self.inferred_project_content_mapper_extensions.clone();
        if let Some(contributions) = &change.content_mapper_contributions {
            inferred_content_mappers = contributions.mappers.clone();
            inferred_content_mapper_extensions = contributions.extensions.clone();
        }
        let base_fs = match &change.fs {
            Some(fs) => fs.clone(),
            None => LayeredFsInput::Plain(store.fs.clone()),
        };
        // Total replacements and returning to the session host must not
        // retain files from the previous filesystem. Layers invalidate only
        // their per-path changes, including the first layer over a
        // host-backed snapshot.
        if change.replace_file_system || self.file_system_override && !change.file_system_override
        {
            change.file_changes.invalidate_all = true;
        }
        let layered_fs = layer_overlay_file_system(
            base_fs,
            overlays,
            store.options.position_encoding.clone(),
        );
        let overlays = layered_fs.overlays();
        let fs = Arc::new(new_snapshot_fs_builder_from_source(
            layered_fs,
            self.fs.cache_files.clone(),
            self.fs.cache_directories.clone(),
            self.fs.node_modules_realpath_aliases.clone(),
        ));
        change.file_changes = self.process_file_changes(
            &fs,
            change.file_changes,
            &logger,
            change.content_mapper_contributions.as_ref(),
            &self.overlays(),
            &overlays,
        );

        let compiler_options_for_inferred_projects = match &change
            .compiler_options_for_inferred_projects
        {
            Some(options) => Some(options.clone()),
            None => self.compiler_options_for_inferred_projects.clone(),
        };

        // Compute effective customConfigFileName from user preferences
        let custom_config_file_name = match &change.new_config {
            Some(new_config) => new_config.custom_config_file_name.clone(),
            None => self
                .config_file_registry
                .custom_config_file_name
                .clone(),
        };

        let new_snapshot_id = store.next_snapshot_id();
        let mut project_collection_builder = new_project_collection_builder(
            ctx,
            new_snapshot_id,
            fs.clone(),
            overlays.clone(),
            self.project_collection.clone(),
            &self.config_file_registry,
            &self.project_collection.api_state,
            compiler_options_for_inferred_projects.clone(),
            inferred_content_mappers.clone(),
            inferred_content_mapper_extensions.clone(),
            store.options.clone(),
            custom_config_file_name,
            store.parse_cache.clone(),
            store.content_mapped_parse_cache.clone(),
            store.extended_config_cache.clone(),
            store.content_mapper_host.clone(),
            client.cloned(),
        );

        if !change.ata_changes.is_empty() {
            project_collection_builder
                .did_update_ata_state(&change.ata_changes, &logger.fork("DidUpdateATAState"));
        }

        project_collection_builder
            .did_change_custom_config_file_name(&logger.fork("DidChangeCustomConfigFileName"));
        if change.compiler_options_for_inferred_projects.is_some() {
            if let Some(inferred) = project_collection_builder.inferred_project.clone() {
                let command_line = inferred.command_line.as_ref().expect(
                    "inferred project must have a command line",
                );
                project_collection_builder.update_inferred_project(
                    command_line.file_names().to_vec(),
                    change.compiler_options_for_inferred_projects.clone(),
                    command_line.project_references().to_vec(),
                    command_line.errors.lock().unwrap().clone(),
                    command_line.content_mappers().to_vec(),
                    &logger.fork("DidChangeCompilerOptionsForInferredProjects"),
                );
            }
        }
        if change.content_mapper_contributions.is_some() {
            project_collection_builder.did_change_content_mapper_contributions(
                &logger.fork("DidChangeContentMapperContributions"),
            );
        }
        if let Some(new_config) = &change.new_config {
            project_collection_builder.did_change_user_preferences(
                &self.user_preferences,
                new_config,
                &logger.fork("DidChangeUserPreferences"),
            );
        }

        if !change.file_changes.is_empty() {
            project_collection_builder
                .did_change_files(&change.file_changes, &logger.fork("DidChangeFiles"));
        }

        let mut api_error = None;
        if let Some(api_request) = &change.api_request {
            api_error = project_collection_builder
                .handle_api_request(api_request, &logger.fork("HandleAPIRequest"))
                .err();
        }

        for uri in &change.documents {
            project_collection_builder.did_request_file(
                uri.clone(),
                false, /* configuredProjectsOnly */
                &logger.fork("DidRequestFile"),
            );
        }

        for uri in &change.configured_project_documents {
            project_collection_builder.did_request_file(
                uri.clone(),
                true, /* configuredProjectsOnly */
                &logger.fork("DidRequestFile (optional)"),
            );
        }

        for project_id in &change.projects {
            project_collection_builder
                .did_request_project(project_id, &logger.fork("DidRequestProject"));
        }

        if let Some(project_tree) = &change.project_tree {
            project_collection_builder.did_request_project_trees(
                project_tree,
                &logger.fork("DidRequestProjectTrees"),
            );
        }

        let (project_collection, config_file_registry) =
            project_collection_builder.finalize(&logger);

        let mut projects_with_new_program_structure: std::collections::HashMap<
            tsc_ls::autoimport::ProjectId,
            bool,
        > = std::collections::HashMap::new();
        for project in project_collection.projects() {
            if project.program_last_update == new_snapshot_id
                && project.program_update_kind != ProgramUpdateKind::Cloned
            {
                projects_with_new_program_structure.insert(
                    tsc_ls::autoimport::ProjectId(Rc::from(project.id.as_str())),
                    project.program_update_kind == ProgramUpdateKind::NewFiles,
                );
            }
        }

        // Clean cached files not touched by any open project on file open,
        // close, delete, or when explicitly requested (e.g. by an idle
        // timer).
        let should_clean_file_cache = change.clean_file_cache
            || !change.file_changes.opened.as_str().is_empty()
            || !change.file_changes.reopened.as_str().is_empty()
            || change.file_changes.closed.len() > 0
            || change.file_changes.deleted.len() > 0;
        if should_clean_file_cache {
            // The set of seen files can change only if a program was
            // constructed (not cloned) during this snapshot. When
            // cleanFileCache is explicitly set, always attempt cleaning.
            if !projects_with_new_program_structure.is_empty() || change.clean_file_cache {
                let clean_files_start = Instant::now();
                let mut removed_files = 0;
                fs.cache_files.range(|entry| {
                    for project in project_collection.projects() {
                        if let Some(host) = &project.host {
                            if host.source_fs().seen_file(&entry.key()) {
                                return true;
                            }
                        }
                    }
                    entry.delete();
                    removed_files += 1;
                    true
                });
                logger.logf(format_args!(
                    "Removed {} cached file(s) in {:?}",
                    removed_files,
                    clean_files_start.elapsed()
                ));
            }
        }

        let config = match &change.new_config {
            Some(new_config) => new_config.clone(),
            None => self.user_preferences.clone(),
        };

        let auto_import_host = Rc::new(crate::autoimport::new_auto_import_registry_clone_host(
            project_collection.clone(),
            store.parse_cache.clone(),
            fs.clone(),
        ));
        let open_files: std::collections::HashMap<PathKey, RootedFilePath> = overlays
            .iter()
            .map(|(path, overlay)| (path.clone(), overlay.file_name().clone()))
            .collect();
        let mut prepare_auto_imports = PathKey::default();
        let mut prepare_auto_imports_file_name = RootedFilePath::default();
        if !change.auto_imports.as_str().is_empty() {
            prepare_auto_imports = change.auto_imports.path_key(self.case_sensitivity());
            prepare_auto_imports_file_name = change.auto_imports.file_name();
        }
        let old_auto_imports = self.auto_imports.clone().unwrap_or_else(|| {
            Rc::new(tsc_ls::autoimport::Registry::new(
                store.case_sensitivity,
                self.user_preferences.clone(),
            ))
        });
        let auto_imports_result = old_auto_imports.clone_registry(
            ctx,
            tsc_ls::autoimport::registry::RegistryChange {
                requested_file: prepare_auto_imports,
                requested_file_name: prepare_auto_imports_file_name,
                open_files,
                changed: change.file_changes.changed.clone(),
                created: change.file_changes.created.clone(),
                deleted: change.file_changes.deleted.clone(),
                rebuilt_programs: projects_with_new_program_structure,
                user_preferences: change.new_config.clone(),
            },
            auto_import_host.clone() as Rc<dyn tsc_ls::autoimport::registry::RegistryCloneHost>,
            store.options.current_directory.clone(),
            &logger.fork("UpdateAutoImports"),
        );
        let mut auto_imports_watch = None;
        let mut auto_imports = None;
        if let Ok(new_registry) = auto_imports_result {
            auto_imports_watch = self
                .auto_imports_watch
                .as_ref()
                .map(|w| w.clone_with(new_registry.node_modules_directories()));
            auto_imports = Some(Rc::new(new_registry));
        }

        let (snapshot_fs, _) = fs.finalize();
        let snapshot_fs = Arc::new(snapshot_fs);
        let mut new_snapshot = store.new_snapshot(
            new_snapshot_id,
            snapshot_fs.clone(),
            ConfigFileRegistry::default(),
            compiler_options_for_inferred_projects,
            config,
            auto_imports,
            auto_imports_watch,
        );
        new_snapshot.parent_id = self.id;
        new_snapshot.project_collection = project_collection;
        new_snapshot.config_file_registry = config_file_registry;
        new_snapshot.inferred_project_content_mappers = inferred_content_mappers;
        new_snapshot.inferred_project_content_mapper_extensions =
            inferred_content_mapper_extensions;
        new_snapshot.builder_logs = logger.clone();
        new_snapshot.api_error = api_error;
        new_snapshot.file_system_override = change.file_system_override;
        new_snapshot.created_programs = project_collection_builder.created_programs;

        for project in new_snapshot.project_collection.projects() {
            if let Some(program) = &project.program {
                store.program_counter.ref_(program);
                if project.program_last_update == new_snapshot_id {
                    // If the program was updated during this clone, the
                    // project and its host are new and still retain
                    // references to the builder. Freezing clears the builder
                    // reference so it's GC'd and to ensure the project can't
                    // access any data not already in the snapshot during
                    // use. (See the comment in snapshot.go for the full
                    // explanation.)
                    if let Some(host) = &project.host {
                        host.freeze(
                            snapshot_fs.clone(),
                            new_snapshot.config_file_registry.clone(),
                        );
                    }
                }
            }
        }
        for config in new_snapshot.config_file_registry.configs.values() {
            if let Some(command_line) = &config.command_line {
                if let Some(config_file) = command_line.config_file.as_ref() {
                    for file in config_file.extended_source_files() {
                        store.extended_config_cache.add_owner(
                            &store
                                .case_sensitivity
                                .path_key(&file.as_path()),
                            new_snapshot.id,
                        );
                    }
                }
            }
        }

        tsc_ls::autoimport::registry::RegistryCloneHost::dispose(&*auto_import_host);

        logger.logf(format_args!(
            "Finished cloning snapshot {} into snapshot {} in {:?}",
            self.id,
            new_snapshot.id,
            start.elapsed()
        ));
        Arc::new(new_snapshot)
    }

    /// `s.ref` — increments the snapshot's reference count, preventing it
    /// from being disposed until a corresponding `deref` is called. The
    /// snapshot must still be alive (`refCount > 0`) when `ref` is called.
    pub fn ref_(&self) {
        if self.ref_count.fetch_add(1, Ordering::SeqCst) <= 0 {
            panic!(
                "snapshot {}: ref on disposed snapshot, parentId={}",
                self.id, self.parent_id
            );
        }
    }

    /// `s.tryRef` — attempts to increment the snapshot's reference count.
    /// If the snapshot is already disposed (`refCount == 0`), it returns
    /// false without modifying the count. On success the caller must
    /// eventually call `deref`.
    pub fn try_ref(&self) -> bool {
        loop {
            let rc = self.ref_count.load(Ordering::SeqCst);
            if rc <= 0 {
                return false;
            }
            if self
                .ref_count
                .compare_exchange(rc, rc + 1, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                return true;
            }
        }
    }

    /// `s.Deref` — decrements the snapshot's reference count. When the
    /// count reaches zero, the snapshot is disposed and its store-owned
    /// resources are released.
    pub fn deref(&self) {
        let old = self.ref_count.fetch_sub(1, Ordering::SeqCst);
        let rc = old - 1;
        if rc < 0 {
            panic!(
                "snapshot {}: ref count below zero, parentId={}",
                self.id, self.parent_id
            );
        }
        if rc == 0 {
            self.dispose();
        }
    }

    /// `s.dispose`.
    fn dispose(&self) {
        let store = &self.host;
        for project in self.project_collection.projects() {
            let Some(program) = &project.program else {
                continue;
            };
            if !store.program_counter.deref(program) {
                continue;
            }
            if let Some(content_mapper_project) = program.content_mapper_project() {
                let _ = content_mapper_project.close();
            }
            // This program is no longer referenced by any snapshot. Mark its
            // checker pool as discarded so its idle-cleanup timer stops
            // keeping the pool alive, allowing the pool and any idle
            // checkers it still references to be reclaimed when the pool is
            // garbage-collected.
            if let Some(checker_pool) = &project.checker_pool {
                checker_pool.discard();
            }
            for file in program.source_files() {
                let nodes = program.nodes(file.file_index());
                let source_file = nodes[file].as_source_file();
                if !source_file.is_content_mapper_failure_stub()
                    && !source_file.is_content_mapper_supplemental()
                {
                    if !source_file.content_mapper().is_empty() {
                        store
                            .content_mapped_parse_cache
                            .deref(&content_mapped_parse_cache_key_for_file(&nodes, file));
                    } else {
                        store
                            .parse_cache
                            .deref(&parse_cache_key_for_file(&nodes, file));
                    }
                }
            }
            for file in program.duplicate_source_files() {
                if !file.is_content_mapper_failure_stub {
                    if !file.content_mapper.is_empty() {
                        store
                            .content_mapped_parse_cache
                            .deref(&content_mapped_parse_cache_key_for_duplicate(file));
                    } else {
                        store
                            .parse_cache
                            .deref(&parse_cache_key_for_duplicate(file));
                    }
                }
            }
        }
        for config in self.config_file_registry.configs.values() {
            if let Some(command_line) = &config.command_line {
                for file in command_line.extended_source_files() {
                    store.extended_config_cache.release(
                        &store.case_sensitivity.path_key(&file.as_path()),
                        self.id,
                    );
                }
            }
        }
    }
}

/// `APICreateProgramRequest`.
pub struct ApiCreateProgramRequest {
    pub root_file_names: Vec<RootedFilePath>,
    pub compiler_options: Option<Arc<CompilerOptions>>,
    pub project_references: Vec<Arc<ProjectReference>>,
    pub config_file_parsing_diagnostics: Vec<DiagnosticRef>,
    /// `ModuleResolverFactory` — Go's nil-able interface.
    pub module_resolver_factory: Option<Arc<dyn ModuleResolverFactory>>,
    pub module_resolver_id: u64,
}

/// `ModuleResolverFactory`.
pub trait ModuleResolverFactory: Send + Sync {
    /// `NewResolver` — returns the resolver plus the Go-style cleanup
    /// function.
    fn new_resolver(
        &self,
        ctx: &Context,
        options: ResolverOptions,
    ) -> (Arc<dyn Resolver>, Box<dyn FnOnce() + Send>);
}

/// `APIReconfigureProgramRequest`.
pub struct ApiReconfigureProgramRequest {
    pub program_id: SyntheticProjectId,
    /// Go embeds `APICreateProgramRequest`.
    pub create_program_request: ApiCreateProgramRequest,
}

/// `APISnapshotRequest`.
#[derive(Default)]
pub struct ApiSnapshotRequest {
    pub user_preferences: Option<UserPreferences>,
    /// `PrepareAutoImports` — the zero `DocumentUri` is Go's `""`.
    pub prepare_auto_imports: DocumentUri,
    pub open_projects: Option<Set<RootedFilePath>>,
    pub close_projects: Option<Set<PathKey>>,
    pub open_files: FxHashMap<PathKey, RootedFilePath>,
    pub close_files: Option<Set<PathKey>>,
    pub create_programs: Vec<ApiCreateProgramRequest>,
    pub reconfigure_programs: Vec<ApiReconfigureProgramRequest>,
    pub remove_programs: Option<Set<SyntheticProjectId>>,
    pub ensure_programs: Option<Set<Id>>,
    pub ensure_all_programs: bool,
    pub ensure_files: FxHashMap<PathKey, RootedFilePath>,
    /// `FileSystem` — Go's nil-able `vfs.FS`.
    pub file_system: Option<Arc<dyn Vfs>>,
    /// `ReplaceFileSystem` indicates a total filesystem replacement.
    /// Layers use per-path file changes instead of invalidating all
    /// inherited state.
    pub replace_file_system: bool,
}

/// `ProjectTreeRequest` — if `referenced_projects` is `None`, all project
/// trees need to be loaded, otherwise only those that are referenced.
#[derive(Default)]
pub struct ProjectTreeRequest {
    referenced_projects: Option<Set<PathKey>>,
}

impl ProjectTreeRequest {
    /// `referencedProjects` — `None` means "all projects" (Go nil).
    pub fn new(referenced_projects: Option<Set<PathKey>>) -> Self {
        ProjectTreeRequest {
            referenced_projects,
        }
    }

    /// `p.IsAllProjects`.
    pub fn is_all_projects(&self) -> bool {
        self.referenced_projects.is_none()
    }

    /// `p.IsProjectReferenced`.
    pub fn is_project_referenced(&self, project_id: &PathKey) -> bool {
        self.referenced_projects
            .as_ref()
            .is_some_and(|s| s.has(project_id))
    }

    /// `p.Projects`.
    pub fn projects(&self) -> Vec<PathKey> {
        match &self.referenced_projects {
            None => Vec::new(),
            Some(set) => set.keys().iter().cloned().collect(),
        }
    }
}

/// `ResourceRequest`.
#[derive(Default)]
pub struct ResourceRequest {
    /// `Documents` are URIs that were requested by the client. The new
    /// snapshot should ensure projects for these URIs have loaded programs.
    pub documents: Vec<DocumentUri>,
    /// `ConfiguredProjectDocuments` are URIs for which configured projects
    /// should be loaded (if disableSolutionSearching/
    /// disableReferencedProjectLoad settings allow), but no inferred
    /// project should be created if no configured project is found. This is
    /// used by cross-project operations like find-all-references.
    pub configured_project_documents: Vec<DocumentUri>,
    /// `Projects` — update requested projects; used when we want the LS
    /// from all the projects the file can be part of.
    pub projects: Vec<Id>,
    /// `ProjectTree` — update and ensure project trees that reference the
    /// projects; used to compute the solution and project tree so we can
    /// find references across all the projects in the solution irrespective
    /// of which project is open.
    pub project_tree: Option<ProjectTreeRequest>,
    /// `AutoImports` is the document URI for which auto imports should be
    /// prepared.
    pub auto_imports: DocumentUri,
}

/// `SnapshotChange`.
#[derive(Default)]
pub struct SnapshotChange {
    /// Go embeds `ResourceRequest` — the request fields are flattened here.
    /// `Documents`.
    pub documents: Vec<DocumentUri>,
    /// `ConfiguredProjectDocuments`.
    pub configured_project_documents: Vec<DocumentUri>,
    /// `Projects`.
    pub projects: Vec<Id>,
    /// `ProjectTree`.
    pub project_tree: Option<ProjectTreeRequest>,
    /// `AutoImports`.
    pub auto_imports: DocumentUri,

    /// `reason`.
    pub reason: UpdateReason,
    /// `fs` overrides the session filesystem for this snapshot. It is used
    /// by API snapshots that supply their own memory or cache filesystem.
    pub fs: Option<LayeredFsInput>,
    /// `fileSystemOverride`.
    pub file_system_override: bool,
    /// `replaceFileSystem`.
    pub replace_file_system: bool,
    /// `fileChanges` are the changes that have occurred since the last
    /// snapshot.
    pub file_changes: FileChangeSummary,
    /// `compilerOptionsForInferredProjects` — only set when the value in
    /// the next snapshot should change; `None` copies the previous
    /// snapshot's value.
    pub compiler_options_for_inferred_projects: Option<Arc<CompilerOptions>>,
    /// `contentMapperContributions`.
    pub content_mapper_contributions: Option<ContentMapperContributions>,
    /// `newConfig`.
    pub new_config: Option<UserPreferences>,
    /// `ataChanges` contains ATA-related changes to apply to projects in
    /// the new snapshot.
    pub ata_changes: FxHashMap<Id, AtaStateChange>,
    /// `apiRequest` — `Rc` mirrors Go's `*APISnapshotRequest` sharing.
    pub api_request: Option<Rc<ApiSnapshotRequest>>,
    /// `cleanFileCache` triggers cleaning of cached files not referenced
    /// by any open project.
    pub clean_file_cache: bool,
}

/// `ATAStateChange` — a change to a project's ATA state.
pub struct AtaStateChange {
    /// `TypingsInfo` — the new typings info for the project.
    pub typings_info: Option<TypingsInfo>,
    /// `TypingsFiles` — the new list of typing files for the project.
    pub typings_files: Vec<RootedFilePath>,
    /// `TypingsFilesToWatch` — the new list of typing files to watch for
    /// changes.
    pub typings_files_to_watch: Vec<RootedPath>,
    /// `Logs`.
    pub logs: LogTree,
}

impl SnapshotChange {
    /// `change.ResourceRequest = req` — assigns the Go-embedded
    /// `ResourceRequest` fields in one shot.
    pub fn set_resource_request(&mut self, request: ResourceRequest) {
        self.documents = request.documents;
        self.configured_project_documents = request.configured_project_documents;
        self.projects = request.projects;
        self.project_tree = request.project_tree;
        self.auto_imports = request.auto_imports;
    }
}
