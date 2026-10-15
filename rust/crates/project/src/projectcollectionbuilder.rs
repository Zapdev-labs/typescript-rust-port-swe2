// Ported from tsc/internal/project/projectcollectionbuilder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go's `dirty.Value[*Project]` unifies `*SyncMapEntry` and `*Box` behind
//   one interface; [`ProjectEntry`] plays that role (an enum over the two
//   `SyncMapEntry` kinds and a borrow of the inferred-project `dirty.Box`).
// - Go's `entry.Locked(fn)` blocks serialize against other goroutines; this
//   port runs the whole builder on one thread (`Rc<Project>` is `!Send`),
//   so `Locked` collapses to direct `value`/`change` calls. For the same
//   reason `ChangeIf(cond, apply)` becomes an eager `cond(entry.value())`
//   followed by `entry.change(apply)` — identical under a single thread.
// - `change`/`change_if` apply closures get `&mut Rc<Project>`; the dirty
//   copy-on-write guarantee (`Cloneable::clone_value`) means the `Rc` is
//   uniquely owned at apply time, so `Rc::get_mut` is the faithful
//   equivalent of Go mutating the cloned `*Project`.
// - `newCompilerHost(project, builder)` captures `*Project`/`*Builder`
//   pointers in Go; [`BuilderHandle`]/[`ProjectHandleData`] are `Send +
//   Sync` snapshot views implementing [`CompilerHostBuilder`]/
//   [`CompilerHostProject`]. `!Send` payloads (parse caches, the registry
//   builder, `ParsedCommandLine`) ride in `fragile::Fragile`, matching the
//   precedent set by `config_file_registry` in `compilerhost.rs`.
// - `BreadthFirstSearchParallelEx` in `findOrCreateDefaultConfiguredProjectWorker`
//   becomes the sequential `breadth_first_search_ex` — Go's parallelism
//   cannot change the outcome (lowest index wins) and the closures capture
//   `Rc`/`RefCell` state. `core.NewWorkGroup(false)` in
//   `DidRequestProjectTrees` likewise becomes inline sequential calls.

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use fragile::Fragile;
use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_collections::{Set, SyncSet};
use tsc_contentmapper::Mapper;
use tsc_core::bfs::{
    BreadthFirstSearchLevel, BreadthFirstSearchOptions, breadth_first_search_ex,
};
use tsc_core::context::Context;
use tsc_core::core::get_script_kind_from_file_name;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::projectreference::ProjectReference;
use tsc_dirty::{Box as DirtyBox, SyncMap as DirtySyncMap, SyncMapEntry};
use tsc_lsproto::{DocumentUri, FileChangeType};
use tsc_lsutil::UserPreferences;
use tsc_project_logging::{LogTree, Logger};
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::client::Client;
use crate::compilerhost::{
    CompilerHostBuilder, CompilerHostProject, ProjectHostHandle, new_compiler_host,
};
use crate::configfileregistry::ConfigFileRegistry;
use crate::configfileregistrybuilder::{
    ChangeFileResult, ConfigFileRegistryBuilder, new_config_file_registry_builder,
};
use crate::extendedconfigcache::ExtendedConfigCache;
use crate::filechange::FileChangeSummary;
use crate::overlayfs::{FileHandle, Overlay};
use crate::parsecache::{ContentMappedParseCache, ParseCache};
use crate::project::{
    ConfiguredProjectId, Id, Kind, ProgramUpdateKind, Project, SyntheticProjectId,
    configured_project_id_from_path_key, new_configured_project,
    new_inferred_project, new_inferred_project_command_line, new_synthetic_project,
    InferredProjectId,
};
use crate::projectcollection::{ApiState, ProjectCollection, open_file_paths};
use crate::session::SessionOptions;
use crate::snapshot::{
    ApiSnapshotRequest, AtaStateChange, ModuleResolverFactory, ProjectTreeRequest,
};
use crate::snapshotfs::{FileSource, SnapshotFsBuilder};
use crate::watch::get_typings_locations_globs;

/// `type projectLoadKind int` (projectcollectionbuilder.go).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProjectLoadKind {
    Find = 0,
    Create = 1,
}

/// `BuilderHandle` — the `Send + Sync` snapshot of `ProjectCollectionBuilder`
/// state that `compilerHost` retains (Go captures `b` directly).
pub struct BuilderHandle {
    session_options: SessionOptions,
    fs: Arc<dyn FileSource>,
    /// `Fragile` — `Rc` payloads cross the `Send + Sync` trait seam; all
    /// access is single-threaded (see the `config_file_registry` PORT note
    /// in `compilerhost.rs`).
    parse_cache: Fragile<Rc<ParseCache>>,
    content_mapped_parse_cache: Fragile<Rc<ContentMappedParseCache>>,
    config_file_registry_builder: Fragile<Arc<ConfigFileRegistryBuilder>>,
    ctx: Context,
    content_mapper_host: Option<Arc<dyn tsc_contentmapper::Host>>,
}

impl BuilderHandle {
    fn new(builder: &ProjectCollectionBuilder) -> BuilderHandle {
        BuilderHandle {
            session_options: (*builder.session_options).clone(),
            fs: builder.fs.clone() as Arc<dyn FileSource>,
            parse_cache: Fragile::new(builder.parse_cache.clone()),
            content_mapped_parse_cache: Fragile::new(
                builder.content_mapped_parse_cache.clone(),
            ),
            config_file_registry_builder: Fragile::new(
                builder.config_file_registry_builder.clone(),
            ),
            ctx: builder.ctx.clone(),
            content_mapper_host: builder.content_mapper_host.clone(),
        }
    }
}

/// `var _ CompilerHostBuilder = (*BuilderHandle)(nil)`.
impl CompilerHostBuilder for BuilderHandle {
    fn session_options(&self) -> &SessionOptions {
        &self.session_options
    }
    fn fs(&self) -> Arc<dyn FileSource> {
        self.fs.clone()
    }
    fn parse_cache(&self) -> Rc<ParseCache> {
        self.parse_cache.get().clone()
    }
    fn content_mapped_parse_cache(&self) -> Rc<ContentMappedParseCache> {
        self.content_mapped_parse_cache.get().clone()
    }
    fn config_file_registry_builder(&self) -> Arc<ConfigFileRegistryBuilder> {
        self.config_file_registry_builder.get().clone()
    }
    fn ctx(&self) -> Context {
        self.ctx.clone()
    }
    fn content_mapper_host(&self) -> Option<Arc<dyn tsc_contentmapper::Host>> {
        self.content_mapper_host.clone()
    }
}

/// `ProjectHandleData` — the `Send + Sync` snapshot of `Project` state that
/// `compilerHost` retains (Go captures `project` directly). The command line
/// with typings files is captured eagerly: the project's command line and
/// typings files do not change between host creation and use.
pub struct ProjectHandleData {
    config_file_path: PathKey,
    id: Id,
    /// `Fragile` — `Arc<ParsedCommandLine>` is `!Sync` (see `BuilderHandle`).
    command_line_with_typings_files: Fragile<Arc<ParsedCommandLine>>,
}

impl ProjectHandleData {
    fn new(project: &Project) -> ProjectHandleData {
        ProjectHandleData {
            config_file_path: project.config_file_path.clone(),
            id: project.id.clone(),
            command_line_with_typings_files: Fragile::new(
                project.get_command_line_with_typings_files(),
            ),
        }
    }
}

/// `var _ CompilerHostProject = (*ProjectHandleData)(nil)`.
impl CompilerHostProject for ProjectHandleData {
    fn config_file_path(&self) -> &PathKey {
        &self.config_file_path
    }
    fn id(&self) -> &Id {
        &self.id
    }
    fn get_command_line_with_typings_files(&self) -> Arc<ParsedCommandLine> {
        self.command_line_with_typings_files.get().clone()
    }
}

/// `ProjectEntry` — Go's `dirty.Value[*Project]` parameter type: a handle to
/// one project slot in a dirty map. `SyncMapEntry` is an `Arc`-backed
/// handle (Go `*SyncMapEntry`); the inferred project's `dirty.Box` is
/// borrowed (`Box<Option<Rc<Project>>>` — the `Option` is Go's nil `*Project`).
///
/// PORT: `apply` closures receive `&mut Rc<Project>`; `Rc::get_mut` unwraps
/// it — the dirty COW (`Cloneable::clone_value`) guarantees the `Rc` is
/// unique at apply time, so `get_mut` is Go's mutation of the cloned
/// `*Project`.
enum ProjectEntry<'b> {
    Configured(SyncMapEntry<ConfiguredProjectId, Rc<Project>>),
    Synthetic(SyncMapEntry<SyntheticProjectId, Rc<Project>>),
    Inferred(&'b DirtyBox<Option<Rc<Project>>>),
}

impl ProjectEntry<'_> {
    /// `entry.Value()` — `None` is Go's nil `*Project` (deleted/empty).
    fn value(&self) -> Option<Rc<Project>> {
        match self {
            ProjectEntry::Configured(entry) => entry.value(),
            ProjectEntry::Synthetic(entry) => entry.value(),
            ProjectEntry::Inferred(b) => b.value().flatten(),
        }
    }

    /// `entry.Change(apply)`.
    fn change(&self, apply: impl FnOnce(&mut Rc<Project>)) {
        match self {
            ProjectEntry::Configured(entry) => entry.change(apply),
            ProjectEntry::Synthetic(entry) => entry.change(apply),
            ProjectEntry::Inferred(b) => b.change(|value| {
                apply(
                    value
                        .as_mut()
                        .expect("change applied to nil inferred project"),
                );
            }),
        }
    }

    /// `entry.Delete()`.
    fn delete(&self) {
        match self {
            ProjectEntry::Configured(entry) => entry.delete(),
            ProjectEntry::Synthetic(entry) => entry.delete(),
            ProjectEntry::Inferred(b) => b.delete(),
        }
    }
}

/// `searchNode`/`searchNodeKey`/`searchResult` — the BFS node payload for
/// `findOrCreateDefaultConfiguredProjectWorker`.
#[derive(Clone)]
struct SearchNode {
    config_file_name: RootedFilePath,
    load_kind: ProjectLoadKind,
    logger: LogTree,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct SearchNodeKey {
    config_file_name: RootedFilePath,
    load_kind: ProjectLoadKind,
}

struct SearchResult {
    project: Option<SyncMapEntry<ConfiguredProjectId, Rc<Project>>>,
    retain: Set<PathKey>,
}

/// `ProjectCollectionBuilder` tracks changes made on top of a previous
/// `ProjectCollection`, producing a new clone with `finalize()` after all
/// changes have been made.
pub struct ProjectCollectionBuilder {
    /// `contentMapperHost`.
    pub content_mapper_host: Option<Arc<dyn tsc_contentmapper::Host>>,

    /// `ctx`.
    pub ctx: Context,
    /// `fs` — the `*snapshotFSBuilder`.
    pub fs: Arc<SnapshotFsBuilder>,
    /// `overlays`.
    pub overlays: FxHashMap<PathKey, Arc<Overlay>>,
    /// `base`.
    pub base: Rc<ProjectCollection>,
    /// `compilerOptionsForInferredProjects`.
    pub compiler_options_for_inferred_projects: Option<Arc<CompilerOptions>>,
    /// `inferredContentMappers`.
    pub inferred_content_mappers: Vec<Arc<Mapper>>,
    /// `inferredContentMapperExtensions`.
    pub inferred_content_mapper_extensions: Vec<String>,
    /// `configFileRegistryBuilder`.
    pub config_file_registry_builder: Arc<ConfigFileRegistryBuilder>,

    /// `client` — optional; used for project loading notifications.
    pub client: Option<Arc<dyn Client>>,

    /// `parseCache`/`contentMappedParseCache`/`extendedConfigCache`.
    pub parse_cache: Rc<ParseCache>,
    pub content_mapped_parse_cache: Rc<ContentMappedParseCache>,
    pub extended_config_cache: Rc<ExtendedConfigCache>,
    /// `sessionOptions`.
    pub session_options: Arc<SessionOptions>,

    /// `newSnapshotID`.
    pub new_snapshot_id: u64,
    /// `programStructureChanged`/`defaultProjectsInvalidated`/
    /// `openFilesChanged` — `Cell` so shared (`&self`) helpers can update
    /// them like Go's plain fields.
    pub program_structure_changed: Cell<bool>,
    pub default_projects_invalidated: Cell<bool>,
    pub open_files_changed: Cell<bool>,

    /// `fileDefaultProjects`.
    pub file_default_projects: RefCell<FxHashMap<PathKey, Id>>,
    /// `configuredProjects` — `dirty.SyncMap[ConfiguredProjectID, *Project]`.
    pub configured_projects: DirtySyncMap<ConfiguredProjectId, Rc<Project>>,
    /// `syntheticProjects`.
    pub synthetic_projects: DirtySyncMap<SyntheticProjectId, Rc<Project>>,
    /// `inferredProject` — `dirty.Box[*Project]`; the `Option` payload is
    /// Go's nil `*Project`.
    pub inferred_project: DirtyBox<Option<Rc<Project>>>,
    /// `createdPrograms`.
    pub created_programs: RefCell<Vec<Rc<Project>>>,

    /// `apiState`.
    pub api_state: RefCell<ApiState>,
}

/// `newProjectCollectionBuilder`.
#[allow(clippy::too_many_arguments)]
pub fn new_project_collection_builder(
    ctx: &Context,
    new_snapshot_id: u64,
    fs: Arc<SnapshotFsBuilder>,
    overlays: FxHashMap<PathKey, Arc<Overlay>>,
    old_project_collection: Rc<ProjectCollection>,
    old_config_file_registry: &ConfigFileRegistry,
    old_api_state: &ApiState,
    compiler_options_for_inferred_projects: Option<Arc<CompilerOptions>>,
    inferred_content_mappers: Vec<Arc<Mapper>>,
    inferred_content_mapper_extensions: Vec<String>,
    session_options: Arc<SessionOptions>,
    custom_config_file_name: String,
    parse_cache: Rc<ParseCache>,
    content_mapped_parse_cache: Rc<ContentMappedParseCache>,
    extended_config_cache: Rc<ExtendedConfigCache>,
    content_mapper_host: Option<Arc<dyn tsc_contentmapper::Host>>,
    client: Option<Arc<dyn Client>>,
) -> ProjectCollectionBuilder {
    let open_files = open_file_paths(&overlays);
    let relative_pattern_support = tsc_lsproto::get_client_capabilities(ctx)
        .workspace
        .did_change_watched_files
        .relative_pattern_support;
    let overlays_is_open = {
        // PORT: `func(path) bool { _, ok := overlays[path] }` — the overlay
        // map is captured by reference in Go; the builder reads it only via
        // this predicate before `finalize`, and `overlays` is immutable
        // afterward, so capturing a copy is equivalent.
        let keys = tsc_collections::new_set_from_items(overlays.keys().cloned());
        move |path: &PathKey| keys.has(path)
    };
    ProjectCollectionBuilder {
        content_mapper_host,
        ctx: ctx.clone(),
        fs: fs.clone(),
        overlays,
        base: old_project_collection.clone(),
        compiler_options_for_inferred_projects,
        inferred_content_mappers,
        inferred_content_mapper_extensions,
        config_file_registry_builder: new_config_file_registry_builder(
            relative_pattern_support,
            fs as Arc<dyn FileSource>,
            Box::new(overlays_is_open),
            old_config_file_registry,
            extended_config_cache.clone(),
            new_snapshot_id,
            session_options.clone(),
            custom_config_file_name,
            &LogTree::none(),
        ),
        client,
        parse_cache,
        content_mapped_parse_cache,
        extended_config_cache,
        session_options,
        new_snapshot_id,
        program_structure_changed: Cell::new(false),
        default_projects_invalidated: Cell::new(false),
        open_files_changed: Cell::new(!tsc_collections::Set::equals(
            Some(&open_files),
            Some(&old_project_collection.open_files),
        )),
        file_default_projects: RefCell::new(FxHashMap::default()),
        configured_projects: DirtySyncMap::new(Some(
            old_project_collection.configured_projects.clone(),
        )),
        synthetic_projects: DirtySyncMap::new(Some(
            old_project_collection.synthetic_projects.clone(),
        )),
        inferred_project: DirtyBox::new(old_project_collection.inferred_project.clone()),
        created_programs: RefCell::new(Vec::new()),
        api_state: RefCell::new(old_api_state.clone_state()),
    }
}

impl ProjectCollectionBuilder {
    /// `b.isOpenFile`.
    pub fn is_open_file(&self, path: &PathKey) -> bool {
        self.overlays.contains_key(path)
    }

    /// `b.toPathKey`.
    pub fn to_path_key(&self, file_name: &RootedFilePath) -> PathKey {
        self.fs
            .fs
            .case_sensitivity()
            .path_key(&file_name.as_path())
    }

    /// The builder's inferred project as `*Project` (Go
    /// `b.inferredProject.Value()` — `None` is nil).
    fn inferred_project_value(&self) -> Option<Rc<Project>> {
        self.inferred_project.value().flatten()
    }

    /// `b.inferredProject` as a [`ProjectEntry`] handle.
    fn inferred_entry(&self) -> ProjectEntry<'_> {
        ProjectEntry::Inferred(&self.inferred_project)
    }

    /// `b.createdPrograms` — handle copy for snapshot adoption.
    pub fn created_programs(&self) -> Vec<Rc<Project>> {
        self.created_programs.borrow().clone()
    }

    /// `Finalize` creates a new `ProjectCollection` and `ConfigFileRegistry`
    /// based on the changes made in the builder.
    pub fn finalize(
        &self,
        _logger: &LogTree,
    ) -> (Rc<ProjectCollection>, ConfigFileRegistry) {
        let mut changed = false;
        let mut new_project_collection = self.base.clone();
        macro_rules! ensure_cloned {
            () => {
                if !changed {
                    new_project_collection = Rc::new(self.base.shallow_clone());
                    changed = true;
                }
            };
        }
        macro_rules! collection_mut {
            () => {
                Rc::get_mut(&mut new_project_collection)
                    .expect("freshly cloned project collection must be unique")
            };
        }

        if let (configured_projects, true) = self.configured_projects.finalize() {
            ensure_cloned!();
            collection_mut!().configured_projects = configured_projects.unwrap_or_default();
        }
        if let (synthetic_projects, true) = self.synthetic_projects.finalize() {
            ensure_cloned!();
            collection_mut!().synthetic_projects = synthetic_projects.unwrap_or_default();
        }

        if self.open_files_changed.get() {
            ensure_cloned!();
            collection_mut!().open_files = open_file_paths(&self.overlays);
        }

        if *self.file_default_projects.borrow() != self.base.file_default_projects {
            ensure_cloned!();
            collection_mut!().file_default_projects =
                self.file_default_projects.borrow().clone();
        }

        if let (inferred_project, true) = self.inferred_project.finalize() {
            ensure_cloned!();
            collection_mut!().inferred_project = inferred_project.flatten();
        }

        let (config_file_registry, registry_changed) =
            self.config_file_registry_builder.finalize();
        if registry_changed {
            ensure_cloned!();
            collection_mut!().config_file_registry = Some(config_file_registry.clone());
        }

        if !self.api_state.borrow().equals(&self.base.api_state) {
            ensure_cloned!();
            collection_mut!().api_state = self.api_state.borrow().clone_state();
        }

        let _ = changed;
        (new_project_collection, config_file_registry)
    }

    /// `forEachProject` — `fn` receives a [`ProjectEntry`] handle; return
    /// `false` to stop (Go `func(entry dirty.Value[*Project]) bool`).
    fn for_each_project(&self, mut f: impl FnMut(ProjectEntry<'_>) -> bool) {
        let keep_going = Cell::new(true);
        self.configured_projects.range(|entry| {
            keep_going.set(f(ProjectEntry::Configured(entry.clone())));
            keep_going.get()
        });
        if keep_going.get() {
            self.synthetic_projects.range(|entry| {
                keep_going.set(f(ProjectEntry::Synthetic(entry.clone())));
                keep_going.get()
            });
        }
        if !keep_going.get() {
            return;
        }
        if self.inferred_project_value().is_some() {
            f(self.inferred_entry());
        }
    }

    /// `HandleAPIRequest`.
    pub fn handle_api_request(
        &self,
        api_request: &ApiSnapshotRequest,
        logger: &LogTree,
    ) -> Result<(), String> {
        let previous_api_state = self.api_state.borrow().clone_state();
        *self.api_state.borrow_mut() = previous_api_state.clone_state();
        match self.handle_api_request_inner(api_request, logger) {
            Err(err) => {
                *self.api_state.borrow_mut() = previous_api_state;
                Err(err)
            }
            ok => ok,
        }
    }

    /// The `HandleAPIRequest` body — errors roll `apiState` back via the
    /// wrapper (Go's `defer`).
    fn handle_api_request_inner(
        &self,
        api_request: &ApiSnapshotRequest,
        logger: &LogTree,
    ) -> Result<(), String> {
        let mut projects_to_close: Set<PathKey> = Set::new();
        if let Some(close_projects) = &api_request.close_projects {
            for project_path in close_projects.keys() {
                let mut api_state = self.api_state.borrow_mut();
                match api_state.open_projects.get(project_path) {
                    Some(&count) if count > 1 => {
                        api_state.open_projects.insert(project_path.clone(), count - 1);
                    }
                    Some(1) => {
                        api_state.open_projects.remove(project_path);
                        projects_to_close.add(project_path.clone());
                    }
                    _ => {}
                }
            }
        }

        if let Some(open_projects) = &api_request.open_projects {
            for config_file_name in open_projects.keys() {
                let config_path = self.to_path_key(config_file_name);
                if self
                    .find_or_create_project(
                        config_file_name,
                        &config_path,
                        ProjectLoadKind::Create,
                        logger,
                    )
                    .is_some()
                {
                    self.api_state
                        .borrow_mut()
                        .open_projects
                        .entry(config_path.clone())
                        .and_modify(|count| *count += 1)
                        .or_insert(1);
                    // A project re-opened in the same request shouldn't be closed.
                    projects_to_close.delete(&config_path);
                } else {
                    return Err(format!(
                        "project not found for open: {}",
                        config_file_name.as_string()
                    ));
                }
            }
        }

        if let Some(close_files) = &api_request.close_files {
            for path in close_files.keys() {
                let mut api_state = self.api_state.borrow_mut();
                if let Some(entry) = api_state.open_files.get_mut(path) {
                    if entry.ref_count > 1 {
                        entry.ref_count -= 1;
                    } else {
                        api_state.open_files.remove(path);
                    }
                }
            }
        }

        for (path, file_name) in &api_request.open_files {
            let mut api_state = self.api_state.borrow_mut();
            let entry = api_state
                .open_files
                .entry(path.clone())
                .or_insert_with(|| crate::projectcollection::ApiOpenedFile {
                    file_name: RootedFilePath::default(),
                    ref_count: 0,
                });
            entry.file_name = file_name.clone();
            entry.ref_count += 1;
        }

        for (path, overlay) in &self.overlays {
            if let Some(entry) =
                self.find_default_configured_project(overlay.file_name(), path)
            {
                if let Some(project) = entry.value() {
                    projects_to_close.delete(project.config_file_path());
                }
            }
        }

        for project_path in projects_to_close.keys() {
            if let Some(entry) = self
                .configured_projects
                .load(&configured_project_id_from_path_key(project_path))
            {
                self.delete_project(&ProjectEntry::Configured(entry), logger);
            }
        }

        // Place newly API-opened files like LSP's textDocument/didOpen, ensuring only
        // their target projects. Existing API-opened files are retained by cleanup below
        // without implicitly updating their programs.
        if !api_request.open_files.is_empty() {
            let mut retain: Set<PathKey> = Set::new();
            let mut ensure_inferred_project = false;
            for (path, file_name) in &api_request.open_files {
                if self.is_open_file(path) {
                    if self.find_default_configured_project(file_name, path).is_none()
                        && !self.is_supported_in_inferred_project(file_name)
                    {
                        return Err(format!(
                            "no project found for opened file: {}",
                            file_name.as_string()
                        ));
                    }
                    continue;
                }
                let result = self.ensure_configured_project_and_ancestors_for_file(
                    file_name, path, logger,
                );
                retain.union(Some(&result.retain));
                if result.project.is_none() {
                    if !self.is_supported_in_inferred_project(file_name) {
                        return Err(format!(
                            "no project found for opened file: {}",
                            file_name.as_string()
                        ));
                    }
                    ensure_inferred_project = true;
                }
            }
            self.cleanup_configured_projects(&retain, logger);
            if ensure_inferred_project && self.inferred_project_value().is_some() {
                self.update_program(&self.inferred_entry(), logger);
            }
        } else if api_request.close_files.is_some() {
            self.cleanup_configured_projects(&Set::new(), logger);
        }
        let mut seen_reconfigured_programs: Set<SyntheticProjectId> = Set::new();
        for request in &api_request.reconfigure_programs {
            if seen_reconfigured_programs.has(&request.program_id) {
                return Err(format!(
                    "synthetic program reconfigured more than once: {}",
                    request.program_id
                ));
            }
            seen_reconfigured_programs.add(request.program_id.clone());
            if api_request
                .remove_programs
                .as_ref()
                .is_some_and(|remove| remove.has(&request.program_id))
            {
                return Err(format!(
                    "synthetic program cannot be reconfigured and removed: {}",
                    request.program_id
                ));
            }
            if self.synthetic_projects.load(&request.program_id).is_none() {
                return Err(format!(
                    "synthetic program not found for reconfiguration: {}",
                    request.program_id
                ));
            }
        }
        if let Some(remove_programs) = &api_request.remove_programs {
            for program_id in remove_programs.keys() {
                let Some(project) = self.synthetic_projects.load(program_id) else {
                    return Err(format!(
                        "synthetic program not found for removal: {}",
                        program_id
                    ));
                };
                self.delete_project(&ProjectEntry::Synthetic(project), logger);
            }
        }
        let mut created_programs: Vec<Option<Rc<Project>>> =
            vec![None; api_request.create_programs.len()];
        let mut created_entries = Vec::with_capacity(api_request.create_programs.len());
        for request in &api_request.create_programs {
            let entry = self.update_or_create_synthetic_project(
                &self.next_synthetic_project_id(),
                request.root_file_names.clone(),
                request.compiler_options.clone(),
                request
                    .project_references
                    .iter()
                    .map(|r| (**r).clone())
                    .collect(),
                request.config_file_parsing_diagnostics.clone(),
                request.module_resolver_factory.clone(),
                request.module_resolver_id,
                self.inferred_content_mappers.clone(),
                logger,
            );
            created_entries.push(entry);
        }
        let mut reconfigured_entries = Vec::with_capacity(api_request.reconfigure_programs.len());
        for request in &api_request.reconfigure_programs {
            reconfigured_entries.push(self.update_or_create_synthetic_project(
                &request.program_id,
                request.create_program_request.root_file_names.clone(),
                request.create_program_request.compiler_options.clone(),
                request
                    .create_program_request
                    .project_references
                    .iter()
                    .map(|r| (**r).clone())
                    .collect(),
                request
                    .create_program_request
                    .config_file_parsing_diagnostics
                    .clone(),
                request.create_program_request.module_resolver_factory.clone(),
                request.create_program_request.module_resolver_id,
                self.inferred_content_mappers.clone(),
                logger,
            ));
        }
        // Go runs these `updateProgram` calls on a `sync.WaitGroup`; the
        // single-threaded port runs them inline in the same order.
        for (i, entry) in created_entries.iter().enumerate() {
            if let Some(entry) = entry {
                if entry.value().is_some_and(|p| p.dirty) {
                    self.update_program(&ProjectEntry::Synthetic(entry.clone()), logger);
                }
                created_programs[i] = entry.value();
            }
        }
        for entry in &reconfigured_entries {
            if let Some(entry) = entry {
                if entry.value().is_some_and(|p| p.dirty) {
                    self.update_program(&ProjectEntry::Synthetic(entry.clone()), logger);
                }
            }
        }
        *self.created_programs.borrow_mut() =
            created_programs.into_iter().map(Option::unwrap).collect();
        for (path, file_name) in &api_request.ensure_files {
            self.did_request_file_impl(file_name.clone(), path.clone(), false, logger);
            if self.find_default_project(file_name, path).is_none() {
                return Err(format!(
                    "no project found for opened file: {}",
                    file_name.as_string()
                ));
            }
        }
        if let Some(ensure_programs) = &api_request.ensure_programs {
            for project_id in ensure_programs.keys() {
                self.did_request_project(project_id, logger);
            }
        }
        if api_request.ensure_all_programs {
            self.for_each_project(|entry| {
                self.update_program(&entry, logger);
                true
            });
        }
        let mut module_resolution_error = None;
        self.for_each_project(|entry| {
            if let Some(project) = entry.value() {
                if let Some(program) = &project.program {
                    module_resolution_error =
                        program.module_resolution_error().map(str::to_string);
                }
            }
            module_resolution_error.is_none()
        });
        match module_resolution_error {
            Some(err) => Err(err),
            None => Ok(()),
        }
    }

    /// `nextSyntheticProjectID`.
    fn next_synthetic_project_id(&self) -> SyntheticProjectId {
        for id in 1i64.. {
            let project_id = crate::project::new_synthetic_project_id(id);
            if self.synthetic_projects.load(&project_id).is_none() {
                return project_id;
            }
        }
        unreachable!()
    }

    /// `DidChangeFiles`.
    pub fn did_change_files(&self, summary: &FileChangeSummary, logger: &LogTree) {
        self.open_files_changed.set(
            self.open_files_changed.get()
                || !summary.opened.as_str().is_empty()
                || !summary.closed.is_empty(),
        );

        let to_paths = |uris: &Set<DocumentUri>| -> Vec<PathKey> {
            uris.keys()
                .iter()
                .map(|uri| uri.path_key(self.base.case_sensitivity))
                .collect()
        };
        let changed_files = to_paths(&summary.changed);
        let deleted_files = to_paths(&summary.deleted);
        let created_files = to_paths(&summary.created);
        if self.content_mapper_host.is_some() {
            let mut all_watch_changes = changed_files.clone();
            all_watch_changes.extend(deleted_files.iter().cloned());
            all_watch_changes.extend(created_files.iter().cloned());
            self.for_each_project(|entry| {
                self.refresh_content_mapper_project_for_changes(
                    &entry,
                    &all_watch_changes,
                    summary.has_excessive_non_create_watch_events(),
                    logger,
                );
                true
            });
        }

        let config_change_logger = logger.fork("Checking for changes affecting config files");
        let config_change_result = self
            .config_file_registry_builder
            .did_change_files(summary, &config_change_logger);
        log_change_file_result(&config_change_result, &config_change_logger);

        self.program_structure_changed.set(
            self.mark_projects_affected_by_config_changes(&config_change_result, logger),
        );

        self.for_each_project(|entry| {
            // Only consider change/delete; creates are handled by the config file registry
            if summary.has_excessive_non_create_watch_events() {
                entry.change(|rc| {
                    let p = Rc::get_mut(rc).expect("dirty clone must be unique");
                    p.dirty = true;
                    p.dirty_file_path = PathKey::default();
                    logger.logf(format_args!(
                        "Marking project as dirty due to excessive watch changes: {}",
                        p.id
                    ));
                });
                return true;
            }

            // Handle closed and changed files
            self.mark_files_changed(&entry, &changed_files, FileChangeType::Changed, logger);
            if entry.value().is_some_and(|v| v.kind == Kind::Inferred)
                && !summary.closed.is_empty()
            {
                let value = entry.value().unwrap();
                let root_file_paths = value
                    .command_line
                    .as_ref()
                    .map(|cl| cl.file_paths().clone())
                    .unwrap_or_default();
                let mut new_root_files = value
                    .command_line
                    .as_ref()
                    .map(|cl| cl.file_names().to_vec())
                    .unwrap_or_default();
                for uri in summary.closed.keys() {
                    let file_name = uri.file_name();
                    let path = self.to_path_key(&file_name);
                    if root_file_paths.has(&path) {
                        // `slices.DeleteFunc` — removes every match.
                        new_root_files.retain(|f| *f != file_name);
                    }
                }
                self.update_inferred_project_roots(new_root_files, logger);
            }

            // Handle deleted files
            if !summary.deleted.is_empty() {
                self.mark_files_changed(&entry, &deleted_files, FileChangeType::Deleted, logger);
            }

            // Handle created files
            if !summary.created.is_empty() {
                self.mark_files_changed(&entry, &created_files, FileChangeType::Created, logger);
            }

            true
        });

        // Handle opened file
        if !summary.opened.as_str().is_empty() || !summary.reopened.as_str().is_empty() {
            let file_name = if !summary.opened.as_str().is_empty() {
                summary.opened.file_name()
            } else {
                summary.reopened.file_name()
            };
            let path = self.to_path_key(&file_name);
            let open_file_result =
                self.ensure_configured_project_and_ancestors_for_file(&file_name, &path, logger);
            self.cleanup_configured_projects(&open_file_result.retain, logger);
        }
    }

    /// `refreshContentMapperProjectForChanges`.
    fn refresh_content_mapper_project_for_changes(
        &self,
        entry: &ProjectEntry,
        paths: &[PathKey],
        refresh_all: bool,
        logger: &LogTree,
    ) {
        let Some(project) = entry.value() else {
            return;
        };
        if project.program.is_none() || project.content_mapper_watched_files.is_none() {
            return;
        }
        let affected = refresh_all
            || paths.iter().any(|path| {
                project
                    .content_mapper_watched_files
                    .as_ref()
                    .unwrap()
                    .has(path)
            });
        if !affected {
            return;
        }
        if let Some(content_mapper_project) =
            project.program.as_ref().unwrap().content_mapper_project()
        {
            let _ = content_mapper_project.refresh();
        }
        entry.change(|rc| {
            let project = Rc::get_mut(rc).expect("dirty clone must be unique");
            project.dirty = true;
            project.dirty_file_path = PathKey::default();
            logger.logf(format_args!(
                "Marking project as dirty due to content mapper configuration changes: {}",
                project.id
            ));
        });
    }

    /// `cleanupConfiguredProjects` sweeps the loaded configured projects and
    /// unloads those that are no longer needed.
    fn cleanup_configured_projects(&self, retain: &Set<PathKey>, logger: &LogTree) {
        let to_remove_projects: RefCell<Set<PathKey>> = RefCell::new(Set::new());
        self.configured_projects.range(|entry| {
            to_remove_projects
                .borrow_mut()
                .add(entry.key().path_key().clone());
            true
        });

        let retain_configured_project_and_references =
            |project: &Rc<Project>, to_remove: &RefCell<Set<PathKey>>| {
                // Retain project
                to_remove
                    .borrow_mut()
                    .delete(project.config_file_path());
                if let Some(program) = &project.program {
                    program.range_resolved_project_reference(
                        &mut |reference_path, _config, _source, _index| {
                            if self
                                .configured_projects
                                .load(&configured_project_id_from_path_key(reference_path))
                                .is_some()
                            {
                                to_remove.borrow_mut().delete(reference_path);
                            }
                            true
                        },
                    );
                }
            };

        let retain_default_configured_project =
            |open_file_path: &PathKey,
             project: &Rc<Project>,
             to_remove: &RefCell<Set<PathKey>>| {
                // Retain project and its references
                retain_configured_project_and_references(project, to_remove);

                // Retain all the ancestor projects
                self.config_file_registry_builder.for_each_config_file_name_for(
                    open_file_path,
                    |config_file_name| {
                        if let Some(ancestor) = self.find_or_create_project(
                            config_file_name,
                            &self.to_path_key(config_file_name),
                            ProjectLoadKind::Find,
                            logger,
                        ) {
                            if let Some(project) = ancestor.value() {
                                retain_configured_project_and_references(&project, to_remove);
                            }
                        }
                    },
                );
            };

        let mut inferred_project_files: Vec<RootedFilePath> = Vec::new();
        for (open_file_path, overlay) in &self.overlays {
            let open_file = overlay.file_name();
            if let Some(p) = self.find_default_configured_project(open_file, open_file_path) {
                if let Some(project) = p.value() {
                    retain_default_configured_project(
                        open_file_path,
                        &project,
                        &to_remove_projects,
                    );
                }
            } else {
                inferred_project_files.push(open_file.clone());
            }
        }
        // Treat API-opened files like open files: retain their configured project (so
        // an LSP-driven open doesn't close it), or keep them as inferred project roots.
        for (path, file) in &self.api_state.borrow().open_files {
            if self.is_open_file(path) {
                continue;
            }
            if let Some(p) = self.find_default_configured_project(&file.file_name, path) {
                if let Some(project) = p.value() {
                    retain_default_configured_project(path, &project, &to_remove_projects);
                }
            } else {
                inferred_project_files.push(file.file_name.clone());
            }
        }

        for project_path in to_remove_projects.borrow().keys() {
            if retain.has(project_path) {
                continue;
            }
            if self
                .api_state
                .borrow()
                .open_projects
                .contains_key(project_path)
            {
                continue;
            }
            if let Some(p) = self
                .configured_projects
                .load(&configured_project_id_from_path_key(project_path))
            {
                self.delete_project(&ProjectEntry::Configured(p), logger);
            }
        }
        self.update_inferred_project_roots(inferred_project_files, logger);
        self.config_file_registry_builder.cleanup();
    }

    /// `cleanupAllConfiguredProjects` removes all configured projects
    /// unconditionally.
    #[allow(dead_code)]
    fn cleanup_all_configured_projects(&self, logger: &LogTree) {
        self.configured_projects.range(|entry| {
            if let Some(p) = self.configured_projects.load(&entry.key()) {
                self.delete_project(&ProjectEntry::Configured(p), logger);
            }
            true
        });
        self.config_file_registry_builder.cleanup();
    }

    /// `collectInferredProjectRoots`.
    fn collect_inferred_project_roots(&self) -> Vec<RootedFilePath> {
        let mut inferred_project_files: Vec<RootedFilePath> = Vec::new();
        for (path, overlay) in &self.overlays {
            if self
                .find_default_configured_project(overlay.file_name(), path)
                .is_none()
            {
                inferred_project_files.push(overlay.file_name().clone());
            }
        }
        self.append_api_opened_inferred_roots(inferred_project_files)
    }

    /// `appendAPIOpenedInferredRoots` appends API-opened files that aren't
    /// open in an overlay and have no configured project, so they're kept as
    /// inferred project roots and persist across snapshots.
    fn append_api_opened_inferred_roots(
        &self,
        mut inferred_project_files: Vec<RootedFilePath>,
    ) -> Vec<RootedFilePath> {
        for (path, file) in &self.api_state.borrow().open_files {
            if self.is_open_file(path) {
                continue;
            }
            if self
                .find_default_configured_project(&file.file_name, path)
                .is_none()
            {
                inferred_project_files.push(file.file_name.clone());
            }
        }
        inferred_project_files
    }

    /// `cleanupInferredProject`.
    fn cleanup_inferred_project(&self, logger: &LogTree) {
        let roots = self.collect_inferred_project_roots();
        self.update_inferred_project_roots(roots, logger);
    }

    /// `DidChangeContentMapperContributions`.
    pub fn did_change_content_mapper_contributions(&self, logger: &LogTree) {
        self.cleanup_inferred_project(logger);
        if self.inferred_project_value().is_some() {
            self.update_program(&self.inferred_entry(), logger);
        }
    }

    /// `ensureInferredProjectIncludesClosedFile`.
    fn ensure_inferred_project_includes_closed_file(
        &self,
        file_name: &RootedFilePath,
        logger: &LogTree,
    ) {
        // Collect existing inferred project roots (open files not in configured projects)
        // plus this closed file.
        let mut inferred_project_files = self.collect_inferred_project_roots();
        inferred_project_files.push(file_name.clone());
        self.update_inferred_project_roots(inferred_project_files, logger);
        if self.inferred_project_value().is_some() {
            self.update_program(&self.inferred_entry(), logger);
        }
    }

    /// `DidRequestFile` ensures projects are loaded for the given URI.
    /// If `configured_projects_only` is true, only configured projects are
    /// loaded; no inferred project is created and it is not guaranteed that
    /// there will be any project containing the file in the resulting
    /// snapshot.
    pub fn did_request_file(
        &self,
        uri: DocumentUri,
        configured_projects_only: bool,
        logger: &LogTree,
    ) {
        let file_name = uri.file_name();
        let path = self.to_path_key(&file_name);
        self.did_request_file_impl(file_name, path, configured_projects_only, logger);
    }

    /// `didRequestFile`.
    fn did_request_file_impl(
        &self,
        file_name: RootedFilePath,
        path: PathKey,
        configured_projects_only: bool,
        logger: &LogTree,
    ) {
        let start_time = Instant::now();
        if self.default_projects_invalidated.get() {
            self.ensure_configured_project_and_ancestors_for_file(&file_name, &path, logger);
            if !self.is_open_file(&path) {
                return;
            }
        }
        if self.is_open_file(&path) {
            let mut has_changes = self.program_structure_changed.get();

            // See if we can find a default project without updating a bunch of stuff.
            if let Some(result) = self.find_default_project(&file_name, &path) {
                has_changes = self.update_program(&result, logger) || has_changes;
                if let Some(value) = result.value() {
                    if value.contains_file(&path) {
                        if has_changes {
                            self.cleanup_inferred_project(logger);
                            if self.inferred_project_value().is_some() {
                                self.update_program(&self.inferred_entry(), logger);
                            }
                        }
                        return;
                    }
                }
            }

            // Make sure all projects we know about are up to date...
            self.configured_projects.range(|entry| {
                has_changes =
                    self.update_program(&ProjectEntry::Configured(entry.clone()), logger)
                        || has_changes;
                true
            });
            if has_changes {
                // If the structure of other projects changed, we might need to move files
                // in/out of the inferred project.
                self.cleanup_inferred_project(logger);
            }

            if self.inferred_project_value().is_some() {
                self.update_program(&self.inferred_entry(), logger);
            }

            // At this point we should be able to find the default project for the file without
            // creating anything else. Initially, I verified that and panicked if nothing was found,
            // but that panic was getting triggered by fourslash infrastructure when it told us to
            // open a package.json file. This is something the VS Code client would never do, but
            // it seems possible that another client would. There's no point in panicking; we don't
            // really even have an error condition until it tries to ask us language questions about
            // a non-TS-handleable file.
        } else {
            let result =
                self.ensure_configured_project_and_ancestors_for_file(&file_name, &path, logger);
            if result.project.is_none() && !configured_projects_only {
                // No configured project found for this closed file.
                // Add it to the inferred project so language service requests can be served.
                self.ensure_inferred_project_includes_closed_file(&file_name, logger);
            }
        }

        logger.log(format_args!(
            "Completed file request for {} in {:?}",
            file_name.as_string(),
            start_time.elapsed()
        ));
    }

    /// `DidRequestProject`.
    pub fn did_request_project(&self, project_id: &Id, logger: &LogTree) {
        let start_time = Instant::now();
        if project_id.inferred().is_some() {
            // Update inferred project
            if self.inferred_project_value().is_some() {
                self.update_program(&self.inferred_entry(), logger);
            }
        } else if let Some(synthetic_id) = project_id.synthetic() {
            if let Some(entry) = self.synthetic_projects.load(&synthetic_id) {
                self.update_program(&ProjectEntry::Synthetic(entry), logger);
            }
        } else if let Some(configured_id) = project_id.configured() {
            if let Some(entry) = self.configured_projects.load(&configured_id) {
                self.update_program(&ProjectEntry::Configured(entry), logger);
            }
        }

        logger.log(format_args!(
            "Completed project update request for {} in {:?}",
            project_id,
            start_time.elapsed()
        ));
    }

    /// `DidRequestProjectTrees`.
    pub fn did_request_project_trees(
        &self,
        project_tree_request: &ProjectTreeRequest,
        logger: &LogTree,
    ) {
        let start_time = Instant::now();

        let mut current_projects: Vec<ConfiguredProjectId> = Vec::new();
        self.configured_projects.range(|entry| {
            current_projects.push(entry.key());
            true
        });

        let mut seen_projects: Set<ConfiguredProjectId> = Set::new();
        // Go queues these on `core.NewWorkGroup(false)` — a parallel work
        // group; the single-threaded port runs them inline in the same
        // order (the `seenProjects` set makes the traversal deterministic).
        for project_id in current_projects {
            if let Some(entry) = self.configured_projects.load(&project_id) {
                // If this project has potential project reference for any of the project we are loading ancestor tree for
                // load this project first
                if entry.value().is_some_and(|project| {
                    project_tree_request.is_all_projects()
                        || project.has_potential_project_reference(project_tree_request)
                }) {
                    self.update_program(&ProjectEntry::Configured(entry.clone()), logger);
                }
                self.ensure_project_tree(&entry, project_tree_request, &mut seen_projects, logger);
            }
        }

        // Updated configured projects may have moved open files in or out of the inferred project.
        // Callers iterate over all language service projects, so the inferred one needs a program too.
        self.cleanup_inferred_project(logger);
        if self.inferred_project_value().is_some() {
            self.update_program(&self.inferred_entry(), logger);
        }

        logger.log(format_args!(
            "Completed project tree request for {:?} in {:?}",
            project_tree_request.projects(),
            start_time.elapsed()
        ));
    }

    /// `ensureProjectTree`.
    fn ensure_project_tree(
        &self,
        entry: &SyncMapEntry<ConfiguredProjectId, Rc<Project>>,
        project_tree_request: &ProjectTreeRequest,
        seen_projects: &mut Set<ConfiguredProjectId>,
        logger: &LogTree,
    ) {
        if !seen_projects.add_if_absent(entry.key()) {
            return;
        }

        let Some(project) = entry.value() else {
            return;
        };
        let Some(program) = &project.program else {
            return;
        };

        // If this project disables child load ignore it
        if program
            .command_line()
            .compiler_options()
            .is_some_and(|o| o.disable_referenced_project_load.is_true())
        {
            return;
        }

        let children = program.get_resolved_project_references();
        for child_config in children.iter().flatten() {
            if !project_tree_request.is_all_projects()
                && program.range_resolved_project_reference_in_child_config(
                    child_config,
                    &mut |reference_path, _config, _source, _index| {
                        !project_tree_request.is_project_referenced(reference_path)
                    },
                )
            {
                continue;
            }

            // Load this child project since this is referenced
            let config_path = child_config
                .config_file
                .as_ref()
                .map(|cfg| cfg.nodes[cfg.source_file].as_source_file().path_key().clone())
                .unwrap_or_default();
            let Some(child_project_entry) = self.find_or_create_project(
                child_config.config_name(),
                &config_path,
                ProjectLoadKind::Create,
                logger,
            ) else {
                continue;
            };
            self.update_program(
                &ProjectEntry::Configured(child_project_entry.clone()),
                logger,
            );

            // Ensure children for this project
            self.ensure_project_tree(
                &child_project_entry,
                project_tree_request,
                seen_projects,
                logger,
            );
        }
    }

    /// `DidUpdateATAState`.
    pub fn did_update_ata_state(
        &self,
        ata_changes: &FxHashMap<Id, AtaStateChange>,
        logger: &LogTree,
    ) {
        for (project_id, ata_change) in ata_changes {
            logger.embed(&ata_change.logs);
            let project: Option<ProjectEntry> = if project_id.inferred().is_some() {
                Some(self.inferred_entry())
            } else if let Some(synthetic_id) = project_id.synthetic() {
                self.synthetic_projects
                    .load(&synthetic_id)
                    .map(ProjectEntry::Synthetic)
            } else if let Some(configured_id) = project_id.configured() {
                self.configured_projects
                    .load(&configured_id)
                    .map(ProjectEntry::Configured)
            } else {
                None
            };

            if let Some(project) = project {
                // Go's `ChangeIf` — eager cond + `change` (single-threaded).
                let should_apply = entry_value_matches(&project, |p| {
                    // Consistency check: the ATA demands (project options, unresolved imports) of this project
                    // has not changed since the time the ATA request was dispatched; the change can still be
                    // applied to this project in its current state.
                    ata_change
                        .typings_info
                        .as_ref()
                        .is_some_and(|info| info.equals(&p.compute_typings_info()))
                });
                if should_apply {
                    let typings_watch_globs = get_typings_locations_globs(
                        &ata_change.typings_files_to_watch,
                        &self.session_options.typings_location,
                        &self.session_options.current_directory,
                        self.fs.fs.case_sensitivity(),
                    );
                    let typings_info = ata_change.typings_info.clone();
                    let typings_files = ata_change.typings_files.clone();
                    project.change(|rc| {
                        let p = Rc::get_mut(rc).expect("dirty clone must be unique");
                        // We checked before triggering this change (in Session.triggerATAForUpdatedProjects) that
                        // the set of typings files is actually different.
                        p.installed_typings_info = typings_info.clone().map(Arc::new);
                        p.typings_files = typings_files.clone();
                        p.typings_watch = p
                            .typings_watch
                            .as_ref()
                            .map(|w| w.clone_with(typings_watch_globs.clone()));
                        p.dirty = true;
                        p.dirty_file_path = PathKey::default();
                    });
                }
            }

            logger.log(format_args!("Updated ATA state for project {}", project_id));
        }
    }

    /// `DidChangeCustomConfigFileName` — if `customConfigFileName` changes,
    /// invalidate default projects.
    pub fn did_change_custom_config_file_name(&self, logger: &LogTree) {
        if !self
            .config_file_registry_builder
            .did_change_custom_config_file_name(logger)
        {
            return;
        }

        self.file_default_projects.borrow_mut().clear();
        self.default_projects_invalidated.set(true);
        self.program_structure_changed.set(true);
    }

    /// `DidChangeUserPreferences`.
    pub fn did_change_user_preferences(
        &self,
        old_preferences: &UserPreferences,
        new_preferences: &UserPreferences,
        logger: &LogTree,
    ) {
        if old_preferences.locale == new_preferences.locale {
            return;
        }
        self.for_each_project(|entry| {
            entry.change(|rc| {
                let project = Rc::get_mut(rc).expect("dirty clone must be unique");
                project.dirty = true;
                project.dirty_file_path = PathKey::default();
                logger.logf(format_args!(
                    "Marking project as dirty due to locale change: {}",
                    project.id
                ));
            });
            true
        });
    }

    /// `markProjectsAffectedByConfigChanges`.
    fn mark_projects_affected_by_config_changes(
        &self,
        config_change_result: &ChangeFileResult,
        logger: &LogTree,
    ) -> bool {
        for project_id in &config_change_result.affected_projects {
            let mut project: Option<ProjectEntry> = None;
            if project_id.inferred().is_some() {
                project = Some(self.inferred_entry());
            } else {
                if let Some(synthetic_id) = project_id.synthetic() {
                    if let Some(entry) = self.synthetic_projects.load(&synthetic_id) {
                        project = Some(ProjectEntry::Synthetic(entry));
                    }
                }
                if project.is_none() {
                    if let Some(configured_id) = project_id.configured() {
                        project = self
                            .configured_projects
                            .load(&configured_id)
                            .map(ProjectEntry::Configured);
                    }
                }
            }
            let Some(entry) = project else {
                panic!("project {project_id} affected by config change not found");
            };
            if entry.value().is_none() {
                panic!("project {project_id} affected by config change not found");
            }
            // Go's `ChangeIf(cond, apply)` — eager cond + `change`.
            let should_apply = entry_value_matches(&entry, |p| {
                !p.dirty || !p.dirty_file_path.as_string().is_empty()
            });
            if should_apply {
                entry.change(|rc| {
                    let p = Rc::get_mut(rc).expect("dirty clone must be unique");
                    p.dirty = true;
                    p.dirty_file_path = PathKey::default();
                    logger.logf(format_args!(
                        "Marking project {} as dirty due to change affecting config",
                        project_id
                    ));
                });
            }
        }

        // Recompute default projects for open files that now have different config file presence.
        let mut has_changes = false;
        for path in &config_change_result.affected_files {
            let Some(overlay) = self.overlays.get(path) else {
                continue;
            };
            let file_name = overlay.file_name();
            let _ = self.ensure_configured_project_and_ancestors_for_file(
                file_name,
                path,
                logger,
            );
            has_changes = true;
        }

        has_changes
    }

    /// `findDefaultProject` — returns a project entry (configured or the
    /// inferred-project box) or `None` (Go nil `dirty.Value`).
    fn find_default_project(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<ProjectEntry<'_>> {
        if let Some(configured_project) = self.find_default_configured_project(file_name, path)
        {
            return Some(ProjectEntry::Configured(configured_project));
        }
        if let Some(key) = self.file_default_projects.borrow().get(path) {
            if key.inferred().is_some() {
                return Some(self.inferred_entry());
            }
        }
        if let Some(inferred_project) = self.inferred_project_value() {
            if inferred_project.contains_file(path) {
                self.file_default_projects
                    .borrow_mut()
                    .insert(path.clone(), InferredProjectId.as_id());
                return Some(self.inferred_entry());
            }
        }
        None
    }

    /// `findDefaultConfiguredProject`.
    fn find_default_configured_project(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<SyncMapEntry<ConfiguredProjectId, Rc<Project>>> {
        if let Some(key) = self.file_default_projects.borrow().get(path) {
            if let Some(configured_id) = key.configured() {
                if let Some(entry) = self.configured_projects.load(&configured_id) {
                    return Some(entry);
                }
            }
        }
        // Sort configured projects so we can use a deterministic "first" as a last resort.
        let mut configured_project_paths: Vec<PathKey> = Vec::new();
        let mut configured_projects: FxHashMap<
            PathKey,
            SyncMapEntry<ConfiguredProjectId, Rc<Project>>,
        > = FxHashMap::default();
        self.configured_projects.range(|entry| {
            let configured_path = entry.key().path_key().clone();
            configured_project_paths.push(configured_path.clone());
            configured_projects.insert(configured_path, entry.clone());
            true
        });
        configured_project_paths.sort();

        let (project, multiple_candidates) = find_default_configured_project_from_program_inclusion(
            path,
            &configured_project_paths,
            |path| configured_projects.get(path).and_then(|entry| entry.value()),
        );

        if multiple_candidates {
            if let Some(p) = self
                .find_or_create_default_configured_project_for_file(
                    file_name,
                    path,
                    ProjectLoadKind::Find,
                    &LogTree::none(),
                )
                .project
            {
                return Some(p);
            }
        }

        configured_projects.get(&project).cloned()
    }

    /// `ensureConfiguredProjectAndAncestorsForFile`.
    fn ensure_configured_project_and_ancestors_for_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        logger: &LogTree,
    ) -> SearchResult {
        let mut result =
            self.find_or_create_default_configured_project_for_file(file_name, path, ProjectLoadKind::Create, logger);
        if result.project.is_some() && self.is_open_file(path) {
            self.create_ancestor_tree(file_name, path, &mut result, logger);
        }
        result
    }

    /// `createAncestorTree`.
    fn create_ancestor_tree(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        open_result: &mut SearchResult,
        logger: &LogTree,
    ) {
        let mut project = open_result
            .project
            .as_ref()
            .and_then(|entry| entry.value())
            .expect("createAncestorTree requires a project");
        loop {
            // Skip if project is not composite and we are only looking for solution
            if let Some(command_line) = &project.command_line {
                let options = command_line.compiler_options();
                if !options.is_some_and(|o| o.composite.is_true())
                    || options.is_some_and(|o| o.disable_solution_searching.is_true())
                {
                    return;
                }
            }

            // Get config file name
            let ancestor_config_name =
                self.config_file_registry_builder.get_ancestor_config_file_name(
                    file_name,
                    path,
                    project.config_file_name(),
                    logger,
                );
            if ancestor_config_name.as_string().is_empty() {
                return;
            }

            // find or delay load the project
            let ancestor_path = self.to_path_key(&ancestor_config_name);
            let Some(ancestor) = self.find_or_create_project(
                &ancestor_config_name,
                &ancestor_path,
                ProjectLoadKind::Create,
                logger,
            ) else {
                return;
            };

            open_result.retain.add(ancestor_path);

            // If this ancestor is new and was not updated because we are just creating it for future loading
            // eg when invoking find all references or rename that could span multiple projects
            // we would make the current project as its potential project reference
            let ancestor_value = ancestor.value().expect("created project has a value");
            if ancestor_value.command_line.is_none()
                && (project.command_line.is_none()
                    || project
                        .command_line
                        .as_ref()
                        .unwrap()
                        .compiler_options()
                        .is_some_and(|o| o.composite.is_true()))
            {
                let project_config_file_path = project.config_file_path.clone();
                ancestor.change(|rc| {
                    Rc::get_mut(rc)
                        .expect("dirty clone must be unique")
                        .set_potential_project_reference(
                            project_config_file_path.clone(),
                        );
                });
            }

            project = ancestor_value;
        }
    }

    /// `findOrCreateDefaultConfiguredProjectWorker`.
    #[allow(clippy::too_many_arguments)]
    fn find_or_create_default_configured_project_worker(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        config_file_name: &RootedFilePath,
        load_kind: ProjectLoadKind,
        visited: Option<&SyncSet<SearchNodeKey>>,
        fallback: Option<SearchResult>,
        logger: &LogTree,
    ) -> SearchResult {
        let configs: RefCell<FxHashMap<PathKey, Arc<ParsedCommandLine>>> =
            RefCell::new(FxHashMap::default());
        let owned_visited;
        let visited = match visited {
            Some(v) => v,
            None => {
                owned_visited = SyncSet::new();
                &owned_visited
            }
        };

        let neighbors = |node: SearchNode| -> Vec<SearchNode> {
            let config_path = self.to_path_key(&node.config_file_name);
            let configs_ref = configs.borrow();
            let Some(config) = configs_ref.get(&config_path) else {
                return Vec::new();
            };
            if config.project_references().is_empty() {
                return Vec::new();
            }
            let reference_load_kind = if config
                .compiler_options()
                .is_some_and(|o| o.disable_referenced_project_load.is_true())
            {
                ProjectLoadKind::Find
            } else {
                node.load_kind
            };

            let references = config.resolved_project_reference_paths();
            let ref_logger = if !references.is_empty() {
                node.logger.fork(&format!(
                    "Searching {} project references of {}",
                    references.len(),
                    node.config_file_name.as_string()
                ))
            } else {
                LogTree::none()
            };
            references
                .iter()
                .map(|config_file_name| SearchNode {
                    config_file_name: config_file_name.clone(),
                    load_kind: reference_load_kind,
                    logger: ref_logger.fork(&format!(
                        "Searching project reference {}",
                        config_file_name.as_string()
                    )),
                })
                .collect()
        };

        let visit = |node: SearchNode| -> (bool, bool) {
            let config_file_path = self.to_path_key(&node.config_file_name);
            let Some(config) = self.config_file_registry_builder.find_or_acquire_config_for_file(
                &node.config_file_name,
                &config_file_path,
                path,
                node.load_kind,
                &node.logger.fork("Acquiring config for open file"),
            ) else {
                node.logger.log(format_args!("Config file for project does not already exist"));
                return (false, false);
            };
            configs
                .borrow_mut()
                .insert(config_file_path.clone(), config.clone());
            if config.file_names().is_empty() {
                // Likely a solution tsconfig.json - the search will fan out to its references.
                node.logger
                    .log(format_args!("Project does not contain file (no root files)"));
                return (false, false);
            }

            if config
                .compiler_options()
                .is_some_and(|o| o.composite.is_true())
            {
                // For composite projects, we can get an early negative result.
                // !!! what about declaration files in node_modules? wouldn't it be better to
                //     check project inclusion if the project is already loaded?
                if !config.file_paths().has(path) {
                    node.logger.log(format_args!(
                        "Project does not contain file (by composite config inclusion)"
                    ));
                    return (false, false);
                }
            }

            let Some(project) = self.find_or_create_project(
                &node.config_file_name,
                &config_file_path,
                node.load_kind,
                &node.logger,
            ) else {
                node.logger
                    .log(format_args!("Project does not already exist"));
                return (false, false);
            };

            if node.load_kind == ProjectLoadKind::Create {
                // Ensure project is up to date before checking for file inclusion
                self.update_program(&ProjectEntry::Configured(project.clone()), &node.logger);
            }

            let project_value = project.value().expect("created project has a value");
            if project_value.contains_file(path) {
                let is_direct_inclusion = !project_value.is_source_from_project_reference(path);
                node.logger.logf(format_args!(
                    "Project contains file {}",
                    if is_direct_inclusion {
                        "directly"
                    } else {
                        "as a source of a referenced project"
                    }
                ));
                return (true, is_direct_inclusion);
            }

            node.logger.log(format_args!("Project does not contain file"));
            (false, false)
        };

        let preprocess_level = |level: &mut BreadthFirstSearchLevel<SearchNodeKey, SearchNode>| {
            let mut to_delete = Vec::new();
            {
                let level_ref = &*level;
                level.range(|node| {
                    if node.load_kind == ProjectLoadKind::Find
                        && level_ref.has(&SearchNodeKey {
                            config_file_name: node.config_file_name.clone(),
                            load_kind: ProjectLoadKind::Create,
                        })
                    {
                        // Remove find requests when a create request for the same project is already present.
                        to_delete.push(SearchNodeKey {
                            config_file_name: node.config_file_name.clone(),
                            load_kind: node.load_kind,
                        });
                    }
                    true
                });
            }
            for key in to_delete {
                level.delete(&key);
            }
        };

        let search = breadth_first_search_ex(
            SearchNode {
                config_file_name: config_file_name.clone(),
                load_kind,
                logger: logger.clone(),
            },
            &neighbors,
            &visit,
            BreadthFirstSearchOptions {
                visited: Some(visited),
                preprocess_level: Some(&preprocess_level),
            },
            &|node: &SearchNode| SearchNodeKey {
                config_file_name: node.config_file_name.clone(),
                load_kind: node.load_kind,
            },
        );

        let mut retain: Set<PathKey> = Set::new();
        let mut project: Option<SyncMapEntry<ConfiguredProjectId, Rc<Project>>> = None;
        if let Some(path_nodes) = &search.path {
            if let Some(first) = path_nodes.first() {
                project = self.configured_projects.load(
                    &configured_project_id_from_path_key(
                        &self.to_path_key(&first.config_file_name),
                    ),
                );
            }
            // If we found a project, we retain each project along the BFS path.
            // We don't want to retain everything we visited since BFS can terminate
            // early, and we don't want to retain nondeterministically.
            for node in path_nodes {
                retain.add(self.to_path_key(&node.config_file_name));
            }
        }

        if search.stopped {
            // Found a project that directly contains the file.
            return SearchResult { project, retain };
        }

        let mut fallback = fallback;
        if project.is_some() {
            // If we found a project that contains the file, but it is a source from
            // a project reference, record it as a fallback.
            // PORT: `retain` is cloned for the fallback — Go shares the one
            // set, but every `fallback` use returns before `retain` could be
            // extended, so a clone is observably identical.
            fallback = Some(SearchResult {
                project,
                retain: retain.clone(),
            });
        }

        // Look for tsconfig.json files higher up the directory tree and do the same. This handles
        // the common case where a higher-level "solution" tsconfig.json contains all projects in a
        // workspace.
        {
            let configs_ref = configs.borrow();
            if let Some(config) = configs_ref.get(&self.to_path_key(config_file_name)) {
                if config
                    .compiler_options()
                    .is_some_and(|o| o.disable_solution_searching.is_true())
                {
                    if let Some(fallback) = fallback {
                        return fallback;
                    }
                }
            }
        }
        let ancestor_config_name = self
            .config_file_registry_builder
            .get_ancestor_config_file_name(file_name, path, config_file_name, logger);
        if !ancestor_config_name.as_string().is_empty() {
            return self.find_or_create_default_configured_project_worker(
                file_name,
                path,
                &ancestor_config_name,
                load_kind,
                Some(visited),
                fallback,
                &logger.fork(&format!(
                    "Searching ancestor config file at {}",
                    ancestor_config_name.as_string()
                )),
            );
        }
        if let Some(fallback) = fallback {
            return fallback;
        }
        // If we didn't find anything, we can retain everything we visited,
        // since the whole graph must have been traversed (i.e., the set of
        // retained projects is guaranteed to be deterministic).
        visited.range(|node| {
            retain.add(self.to_path_key(&node.config_file_name));
            true
        });
        SearchResult {
            project: None,
            retain,
        }
    }

    /// `findOrCreateDefaultConfiguredProjectForFile`.
    fn find_or_create_default_configured_project_for_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        load_kind: ProjectLoadKind,
        logger: &LogTree,
    ) -> SearchResult {
        if let Some(key) = self.file_default_projects.borrow().get(path).cloned() {
            if key.inferred().is_some() {
                // The file belongs to the inferred project
                return SearchResult {
                    project: None,
                    retain: Set::new(),
                };
            }
            if let Some(configured_id) = key.configured() {
                return SearchResult {
                    project: self.configured_projects.load(&configured_id),
                    retain: Set::new(),
                };
            }
        }
        let config_file_name = self
            .config_file_registry_builder
            .get_config_file_name_for_file(file_name, path, logger);
        if config_file_name.as_string().is_empty() {
            return SearchResult {
                project: None,
                retain: Set::new(),
            };
        }
        let start_time = Instant::now();
        let result = self.find_or_create_default_configured_project_worker(
            file_name,
            path,
            &config_file_name,
            load_kind,
            None,
            None,
            &logger.fork(&format!(
                "Searching for default configured project for {}",
                file_name.as_string()
            )),
        );
        if let Some(project) = &result.project {
            if let Some(value) = project.value() {
                self.file_default_projects
                    .borrow_mut()
                    .insert(path.clone(), value.id.clone());
            }
        }
        let elapsed = start_time.elapsed();
        if let Some(project) = &result.project {
            logger.log(format_args!(
                "Found default configured project for {}: {} (in {:?})",
                file_name.as_string(),
                project
                    .value()
                    .map(|v| v.config_file_name().as_string().to_string())
                    .unwrap_or_default(),
                elapsed
            ));
        } else {
            logger.log(format_args!(
                "No default configured project found for {} (searched in {:?})",
                file_name.as_string(),
                elapsed
            ));
        }
        result
    }

    /// `findOrCreateProject`.
    fn find_or_create_project(
        &self,
        config_file_name: &RootedFilePath,
        config_file_path: &PathKey,
        load_kind: ProjectLoadKind,
        logger: &LogTree,
    ) -> Option<SyncMapEntry<ConfiguredProjectId, Rc<Project>>> {
        let id = configured_project_id_from_path_key(config_file_path);
        match load_kind {
            ProjectLoadKind::Find => self.configured_projects.load(&id),
            ProjectLoadKind::Create => self
                .configured_projects
                .load_or_store(
                    id,
                    Rc::new(new_configured_project(
                        config_file_name.clone(),
                        config_file_path.clone(),
                        self,
                        logger,
                    )),
                )
                .map(|(entry, _loaded)| entry),
        }
    }

    /// `updateInferredProjectRoots`.
    fn update_inferred_project_roots(
        &self,
        root_file_names: Vec<RootedFilePath>,
        logger: &LogTree,
    ) -> bool {
        let root_file_names: Vec<RootedFilePath> = root_file_names
            .into_iter()
            .filter(|file_name| self.is_supported_in_inferred_project(file_name))
            .collect();
        let mut project_references: Vec<ProjectReference> = Vec::new();
        let mut config_file_parsing_diagnostics: Vec<DiagnosticRef> = Vec::new();
        if let Some(project) = self.inferred_project_value() {
            if let Some(command_line) = &project.command_line {
                project_references = command_line.project_references().to_vec();
                config_file_parsing_diagnostics =
                    command_line.errors.lock().unwrap().clone();
            }
        }
        self.update_inferred_project(
            root_file_names,
            self.compiler_options_for_inferred_projects.clone(),
            project_references,
            config_file_parsing_diagnostics,
            self.inferred_content_mappers.clone(),
            logger,
        )
    }

    /// `updateOrCreateSyntheticProject`.
    #[allow(clippy::too_many_arguments)]
    fn update_or_create_synthetic_project(
        &self,
        project_id: &SyntheticProjectId,
        root_file_names: Vec<RootedFilePath>,
        compiler_options: Option<Arc<CompilerOptions>>,
        project_references: Vec<ProjectReference>,
        config_file_parsing_diagnostics: Vec<DiagnosticRef>,
        module_resolver_factory: Option<Arc<dyn ModuleResolverFactory>>,
        module_resolver_id: u64,
        content_mappers: Vec<Arc<Mapper>>,
        logger: &LogTree,
    ) -> Option<SyncMapEntry<SyntheticProjectId, Rc<Project>>> {
        let project = match self.synthetic_projects.load(project_id) {
            Some(entry) => entry,
            None => {
                let mut synthetic_project = new_synthetic_project(
                    project_id,
                    self.session_options.current_directory.clone(),
                    compiler_options,
                    root_file_names,
                    project_references,
                    content_mappers,
                    self,
                    logger,
                );
                if let Some(command_line) = &synthetic_project.command_line {
                    *command_line.errors.lock().unwrap() = config_file_parsing_diagnostics;
                }
                synthetic_project.module_resolver_factory = module_resolver_factory;
                synthetic_project.module_resolver_id = module_resolver_id;
                return self
                    .synthetic_projects
                    .load_or_store(project_id.clone(), Rc::new(synthetic_project))
                    .map(|(entry, _loaded)| entry);
            }
        };
        let current_project = project.value().expect("loaded project has a value");
        let compiler_options = compiler_options.or_else(|| {
            current_project
                .command_line
                .as_ref()
                .and_then(|cl| cl.compiler_options().cloned().map(Arc::new))
        });
        let new_command_line = new_inferred_project_command_line(
            compiler_options.as_deref(),
            root_file_names.clone(),
            project_references.clone(),
            content_mappers,
            &current_project.project_directory,
            self.fs.fs.case_sensitivity(),
        );
        *new_command_line.errors.lock().unwrap() = config_file_parsing_diagnostics.clone();
        // Go's `ChangeIf(cond, apply)` — eager cond + `change`.
        let should_apply = project.value().is_some_and(|p| {
            let Some(command_line) = &p.command_line else {
                return true;
            };
            command_line.file_names() != new_command_line.file_names()
                || !CompilerOptions::equals(
                    command_line.compiler_options(),
                    compiler_options.as_deref(),
                )
                || !project_references_equal(
                    command_line.project_references(),
                    &project_references,
                )
                || !diagnostics_equal(
                    &command_line.errors.lock().unwrap(),
                    &config_file_parsing_diagnostics,
                )
                || !mappers_equal(
                    command_line.content_mappers(),
                    new_command_line.content_mappers(),
                )
                || p.module_resolver_id != module_resolver_id
        });
        if should_apply {
            logger.log(format_args!(
                "Updating synthetic project config with {} root files",
                root_file_names.len()
            ));
            project.change(|rc| {
                let p = Rc::get_mut(rc).expect("dirty clone must be unique");
                p.set_command_line(Arc::new(new_command_line));
                p.module_resolver_factory = module_resolver_factory;
                p.module_resolver_id = module_resolver_id;
            });
        }
        Some(project)
    }

    /// `updateInferredProject` preserves the current command line when
    /// roots/options are unchanged.
    pub fn update_inferred_project(
        &self,
        root_file_names: Vec<RootedFilePath>,
        compiler_options: Option<Arc<CompilerOptions>>,
        project_references: Vec<ProjectReference>,
        config_file_parsing_diagnostics: Vec<DiagnosticRef>,
        content_mappers: Vec<Arc<Mapper>>,
        logger: &LogTree,
    ) -> bool {
        if root_file_names.is_empty() {
            return self.delete_inferred_project(logger);
        }
        let mut root_file_names = root_file_names;
        root_file_names.sort();
        self.update_or_create_inferred_project(
            root_file_names,
            compiler_options,
            project_references,
            config_file_parsing_diagnostics,
            content_mappers,
            logger,
        )
    }

    /// `deleteInferredProject`.
    fn delete_inferred_project(&self, logger: &LogTree) -> bool {
        let Some(project) = self.inferred_project_value() else {
            return false;
        };
        logger.log(format_args!("Deleting inferred project"));
        if let Some(program) = &project.program {
            program.range_resolved_project_reference(
                &mut |reference_path, _config, _source, _index| {
                    self.config_file_registry_builder
                        .release_config_for_project(reference_path, &project.id);
                    true
                },
            );
        }
        self.inferred_project.delete();
        true
    }

    /// `updateOrCreateInferredProject` always retains an inferred project,
    /// including when `rootFileNames` is empty.
    /// The caller transfers ownership of `rootFileNames`.
    fn update_or_create_inferred_project(
        &self,
        root_file_names: Vec<RootedFilePath>,
        compiler_options: Option<Arc<CompilerOptions>>,
        project_references: Vec<ProjectReference>,
        config_file_parsing_diagnostics: Vec<DiagnosticRef>,
        content_mappers: Vec<Arc<Mapper>>,
        logger: &LogTree,
    ) -> bool {
        if self.inferred_project_value().is_none() {
            let project = new_inferred_project(
                self.session_options.current_directory.clone(),
                compiler_options,
                root_file_names,
                project_references,
                content_mappers,
                self,
                logger,
            );
            if let Some(command_line) = &project.command_line {
                *command_line.errors.lock().unwrap() = config_file_parsing_diagnostics;
            }
            self.inferred_project.set(Some(Rc::new(project)));
            return true;
        }

        let compiler_options = compiler_options.or_else(|| {
            self.inferred_project_value().and_then(|p| {
                p.command_line
                    .as_ref()
                    .and_then(|cl| cl.compiler_options().cloned().map(Arc::new))
            })
        });
        let project_directory = self
            .inferred_project_value()
            .map(|p| p.project_directory.clone())
            .expect("inferred project checked above");
        let new_command_line = new_inferred_project_command_line(
            compiler_options.as_deref(),
            root_file_names.clone(),
            project_references.clone(),
            content_mappers,
            &project_directory,
            self.fs.fs.case_sensitivity(),
        );
        *new_command_line.errors.lock().unwrap() = config_file_parsing_diagnostics.clone();
        // Go's `b.inferredProject.ChangeIf(cond, apply)` — eager cond +
        // `change`.
        let changed = self.inferred_project.value().flatten().is_some_and(|p| {
            let Some(command_line) = &p.command_line else {
                return true;
            };
            command_line.file_names() != new_command_line.file_names()
                || !CompilerOptions::equals(
                    command_line.compiler_options(),
                    compiler_options.as_deref(),
                )
                || !project_references_equal(
                    command_line.project_references(),
                    &project_references,
                )
                || !diagnostics_equal(
                    &command_line.errors.lock().unwrap(),
                    &config_file_parsing_diagnostics,
                )
                || !mappers_equal(
                    command_line.content_mappers(),
                    new_command_line.content_mappers(),
                )
        });
        if !changed {
            return false;
        }
        logger.log(format_args!(
            "Updating inferred project config with {} root files",
            root_file_names.len()
        ));
        self.inferred_project.change(|value| {
            let p = value
                .as_mut()
                .and_then(Rc::get_mut)
                .expect("dirty clone must be unique");
            p.set_command_line(Arc::new(new_command_line));
        });
        true
    }

    /// `isSupportedInInferredProject`.
    fn is_supported_in_inferred_project(&self, file_name: &RootedFilePath) -> bool {
        if file_name.is_dynamic()
            || get_script_kind_from_file_name(file_name) != ScriptKind::Unknown
        {
            return true;
        }
        if let Some(file) = self.fs.get_file(file_name) {
            if file.is_overlay()
                && file_name
                    .any_extension(&[], tsc_tspath::CaseSensitivity::CaseSensitive)
                    .is_empty()
            {
                return true;
            }
        }
        let extensions: Vec<&str> = self
            .inferred_content_mapper_extensions
            .iter()
            .map(String::as_str)
            .collect();
        file_name.extension_is_one_of(&extensions)
    }

    /// `updateProgram` updates the program for the given project entry if
    /// necessary. It returns a boolean indicating whether the update could
    /// have caused any structure-affecting changes.
    ///
    /// PORT: Go wraps the read/mutate phases in `entry.Locked(fn)` to
    /// serialize against other goroutines; single-threaded here.
    fn update_program(&self, entry: &ProjectEntry, logger: &LogTree) -> bool {
        let mut update_program = false;
        let mut delete_project = false;
        let mut files_changed = false;
        let project_id = entry
            .value()
            .expect("updateProgram on a projectless entry")
            .id
            .clone();
        let start_time = Instant::now();
        let mut notified_loading = false;
        let mut display_name = String::new();
        {
            let value = entry.value().expect("updateProgram on a projectless entry");
            let mut early_return = false;
            if value.kind == Kind::Configured {
                let command_line = self.config_file_registry_builder.acquire_config_for_project(
                    value.config_file_name(),
                    value.config_file_path(),
                    &value.id,
                    &logger.fork("Acquiring config for project"),
                );
                match command_line {
                    None => {
                        delete_project = true;
                        files_changed = true;
                        early_return = true;
                    }
                    Some(command_line) => {
                        if !value
                            .command_line
                            .as_ref()
                            .is_some_and(|cl| Arc::ptr_eq(cl, &command_line))
                        {
                            update_program = true;
                            entry.change(|rc| {
                                Rc::get_mut(rc)
                                    .expect("dirty clone must be unique")
                                    .set_command_line(command_line.clone());
                            });
                        }
                    }
                }
            }
            if !early_return {
                if !update_program {
                    update_program = entry.value().is_some_and(|v| v.dirty);
                }
                if update_program && self.client.is_some() {
                    display_name = entry
                        .value()
                        .expect("updateProgram on a projectless entry")
                        .display_name(&self.session_options.current_directory);
                    notified_loading = true;
                }
            }
        }
        if notified_loading {
            if let Some(client) = &self.client {
                client.progress_start(&tsc_diagnostics::Project_0, &[display_name.clone()]);
            }
        }
        if delete_project {
            self.delete_project(entry, logger);
        }
        if update_program {
            let builder_handle = Arc::new(BuilderHandle::new(self));
            let files_changed_cell = Cell::new(files_changed);
            entry.change(|rc| {
                let project = Rc::get_mut(rc).expect("dirty clone must be unique");
                let old_host = project.host.take();
                let old_program = project.program.take();
                let old_checker_pool = project.checker_pool.take();
                project.host = Some(Arc::new(ProjectHostHandle::new(Arc::new(
                    new_compiler_host(
                        Arc::new(ProjectHandleData::new(project)),
                        builder_handle.clone(),
                        logger.fork("CompilerHost"),
                    ),
                ))));
                let result = project.create_program();
                let mut watched_files: Vec<RootedFilePath> = Vec::new();
                for mapper in project
                    .command_line
                    .as_ref()
                    .map(|cl| cl.content_mappers())
                    .unwrap_or(&[])
                {
                    if !mapper.package.is_empty()
                        && mapper.contribution_id.is_empty()
                        && !mapper.package_directory.as_string().is_empty()
                    {
                        watched_files.push(mapper.package_directory.resolve_file("package.json"));
                    }
                }
                if result.program.source_files_slice().iter().any(|&file| {
                    let nodes = result.program.arena_of(file);
                    !nodes[file].as_source_file().content_mapper().is_empty()
                }) {
                    if let Some(content_mapper_project) =
                        project.host.as_ref().unwrap().content_mapper_project()
                    {
                        if let Ok(dynamic_watched_files) =
                            content_mapper_project.watched_files()
                        {
                            watched_files.extend(dynamic_watched_files);
                        }
                    }
                }
                watched_files.sort();
                watched_files.dedup();
                project.content_mapper_watch = project
                    .content_mapper_watch
                    .as_ref()
                    .map(|w| w.clone_with(watched_files.clone()));
                let mut watched = Set::with_size_hint(watched_files.len());
                for file_name in &watched_files {
                    watched.add(
                        self.base
                            .case_sensitivity
                            .path_key(&file_name.as_path()),
                    );
                }
                project.content_mapper_watched_files = Some(watched);
                project.program = Some(result.program.clone());
                project.checker_pool = Some(result.checker_pool);
                project.program_update_kind = result.update_kind;
                project.program_last_update = self.new_snapshot_id;
                if result.update_kind == ProgramUpdateKind::Cloned {
                    project
                        .host
                        .as_ref()
                        .unwrap()
                        .source_fs()
                        .set_seen_files(
                            old_host.as_ref().unwrap().source_fs().seen_files(),
                        );
                }
                if result.update_kind == ProgramUpdateKind::NewFiles {
                    files_changed_cell.set(true);
                    project.program_files_watch = Some(project.clone_watchers());
                }
                project.dirty = false;
                project.dirty_file_path = PathKey::default();
                self.release_dropped_project_references(
                    old_program.as_ref(),
                    Some(&result.program),
                    &project.id,
                );
                if let Some(pool) = old_checker_pool {
                    pool.discard();
                }
            });
            files_changed = files_changed_cell.get();
        }
        if notified_loading {
            if let Some(client) = &self.client {
                client.progress_finish(&tsc_diagnostics::Project_0, &[display_name]);
            }
        }
        if update_program {
            logger.log(format_args!(
                "Program update for {} completed in {:?}",
                project_id,
                start_time.elapsed()
            ));
        }
        files_changed
    }

    /// `markFilesChanged`.
    fn mark_files_changed(
        &self,
        entry: &ProjectEntry,
        paths: &[PathKey],
        change_type: FileChangeType,
        logger: &LogTree,
    ) {
        // Go's `ChangeIf(cond, apply)` — eager cond + `change`.
        let Some((should_apply, new_dirty_file_path)) = ({
            let Some(p) = entry.value() else {
                return;
            };
            if p.program.is_none() || (p.dirty && p.dirty_file_path.as_string().is_empty()) {
                return;
            }

            let mut dirty = false;
            let mut dirty_file_path = p.dirty_file_path.clone();
            for path in paths {
                if p.contains_file(path) {
                    dirty = true;
                    if change_type == FileChangeType::Deleted {
                        dirty_file_path = PathKey::default();
                        break;
                    }
                    // package.json changes can affect module resolution and package
                    // identity (e.g. dedup decisions), so they must always trigger
                    // a full rebuild rather than a single-file clone.
                    if path.base_name() == "package.json" {
                        dirty_file_path = PathKey::default();
                        break;
                    }
                    if dirty_file_path.as_string().is_empty() {
                        dirty_file_path = path.clone();
                    } else if dirty_file_path != *path {
                        dirty_file_path = PathKey::default();
                        break;
                    }
                } else if let Some(host) = &p.host {
                    let seen = if change_type == FileChangeType::Created {
                        host.source_fs().seen_file_or_missing_parent_directory(path)
                    } else {
                        host.source_fs().seen_file(path)
                    };
                    if seen {
                        dirty = true;
                        dirty_file_path = PathKey::default();
                        break;
                    }
                }
            }
            Some((dirty || p.dirty_file_path != dirty_file_path, dirty_file_path))
        }) else {
            return;
        };
        if should_apply {
            entry.change(|rc| {
                let p = Rc::get_mut(rc).expect("dirty clone must be unique");
                p.dirty = true;
                p.dirty_file_path = new_dirty_file_path.clone();
                if !new_dirty_file_path.as_string().is_empty() {
                    logger.logf(format_args!(
                        "Marking project {} as dirty due to changes in {}",
                        p.id,
                        new_dirty_file_path.as_string()
                    ));
                } else {
                    logger.logf(format_args!("Marking project {} as dirty", p.id));
                }
            });
        }
    }

    /// `deleteProject`.
    fn delete_project(&self, project: &ProjectEntry, logger: &LogTree) {
        let Some(value) = project.value() else {
            return;
        };
        let project_id = value.id.clone();
        logger.logf(format_args!(
            "Deleting {} project: {}",
            value.kind.as_str(),
            value.id
        ));
        if let Some(program) = &value.program {
            program.range_resolved_project_reference(
                &mut |reference_path, _config, _source, _index| {
                    self.config_file_registry_builder
                        .release_config_for_project(reference_path, &project_id);
                    true
                },
            );
        }
        if value.kind == Kind::Configured {
            self.config_file_registry_builder
                .release_config_for_project(value.config_file_path(), &project_id);
        }
        project.delete();
    }

    /// `releaseDroppedProjectReferences` releases the config entries for
    /// project references that were present in `oldProgram` but are no
    /// longer referenced by `newProgram`. Creating `newProgram` already
    /// re-acquires the config for every reference it still resolves, so
    /// only the dropped references need to be released here.
    fn release_dropped_project_references(
        &self,
        old_program: Option<&Rc<tsc_compiler::program::Program>>,
        new_program: Option<&Rc<tsc_compiler::program::Program>>,
        project_id: &Id,
    ) {
        let Some(old_program) = old_program else {
            return;
        };
        if let Some(new_program) = new_program {
            if Rc::ptr_eq(old_program, new_program) {
                return;
            }
        }
        let mut new_references: Set<PathKey> = Set::new();
        if let Some(new_program) = new_program {
            new_program.range_resolved_project_reference(
                &mut |reference_path, _config, _source, _index| {
                    new_references.add(reference_path.clone());
                    true
                },
            );
        }
        old_program.range_resolved_project_reference(
            &mut |reference_path, _config, _source, _index| {
                if !new_references.has(reference_path) {
                    self.config_file_registry_builder
                        .release_config_for_project(reference_path, project_id);
                }
                true
            },
        );
    }
}

/// `entry_value_matches` — Go's `Value()`-as-`cond` pattern: applies `f` to
/// the project if the entry holds one.
fn entry_value_matches(entry: &ProjectEntry, f: impl FnOnce(&Project) -> bool) -> bool {
    entry.value().is_some_and(|p| f(&p))
}

/// `logChangeFileResult`.
fn log_change_file_result(result: &ChangeFileResult, logger: &LogTree) {
    if !result.affected_projects.is_empty() {
        logger.logf(format_args!(
            "Config file change affected projects: [{}]",
            result
                .affected_projects
                .iter()
                .map(|id| id.as_str().to_string())
                .collect::<Vec<_>>()
                .join(" ")
        ));
    }
    if !result.affected_files.is_empty() {
        logger.logf(format_args!(
            "Config file change affected config file lookups for {} files",
            result.affected_files.len()
        ));
    }
}

/// `findDefaultConfiguredProjectFromProgramInclusion` (projectcollection.go)
/// — picks the deterministic "first" configured project containing `path`;
/// `multipleCandidates` reports the ambiguous direct-inclusion case.
fn find_default_configured_project_from_program_inclusion(
    path: &PathKey,
    project_paths: &[PathKey],
    get_project: impl Fn(&PathKey) -> Option<Rc<Project>>,
) -> (PathKey, bool) {
    let mut containing_projects: Vec<PathKey> = Vec::new();
    let mut first_configured_project = PathKey::default();
    let mut first_non_source_of_project_reference_redirect = PathKey::default();
    let mut multiple_direct_inclusions = false;

    for project_path in project_paths {
        let Some(p) = get_project(project_path) else {
            continue;
        };
        if p.contains_file(path) {
            containing_projects.push(project_path.clone());
            if !multiple_direct_inclusions && !p.is_source_from_project_reference(path) {
                if first_non_source_of_project_reference_redirect.as_string().is_empty() {
                    first_non_source_of_project_reference_redirect = project_path.clone();
                } else {
                    multiple_direct_inclusions = true;
                }
            }
            if first_configured_project.as_string().is_empty() {
                first_configured_project = project_path.clone();
            }
        }
    }

    if containing_projects.len() == 1 {
        return (containing_projects.into_iter().next().unwrap(), false);
    }
    if !multiple_direct_inclusions {
        if !first_non_source_of_project_reference_redirect.as_string().is_empty() {
            // Multiple projects include the file, but only one is a direct inclusion.
            return (first_non_source_of_project_reference_redirect, false);
        }
        // Multiple projects include the file, and none are direct inclusions.
        return (first_configured_project, false);
    }
    // Multiple projects include the file directly.
    (first_configured_project, true)
}

/// `projectReferencesEqual`.
fn project_references_equal(a: &[ProjectReference], b: &[ProjectReference]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|(a, b)| a.path == b.path && a.circular == b.circular)
}

/// `reflect.DeepEqual(p.CommandLine.Errors, configFileParsingDiagnostics)`
/// — deep-compares `Diagnostic` contents behind the `DiagnosticRef` handles.
/// PORT: `Diagnostic` has no `PartialEq` (Go's DeepEqual walks every field,
/// including the `*SourceFile`); `diagnostic_deep_equal` compares the
/// observable fields — `file` by name/text rather than by walking the whole
/// source file.
fn diagnostics_equal(a: &[DiagnosticRef], b: &[DiagnosticRef]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b.iter()).all(|(a, b)| {
            let a = a.lock().unwrap();
            let b = b.lock().unwrap();
            diagnostic_deep_equal(&a, &b)
        })
}

/// `reflect.DeepEqual` on a single `*ast.Diagnostic`.
fn diagnostic_deep_equal(a: &tsc_ast::diagnostic::Diagnostic, b: &tsc_ast::diagnostic::Diagnostic) -> bool {
    a.code() == b.code()
        && a.category() == b.category()
        && a.loc() == b.loc()
        && a.source() == b.source()
        && a.message_text() == b.message_text()
        && a.message_key() == b.message_key()
        && a.message_args() == b.message_args()
        && a.reports_unnecessary() == b.reports_unnecessary()
        && a.reports_deprecated() == b.reports_deprecated()
        && a.skipped_on_no_emit() == b.skipped_on_no_emit()
        && match (a.file(), b.file()) {
            (None, None) => true,
            (Some(file_a), Some(file_b)) => {
                file_a.file_name == file_b.file_name
                    && file_a.path_key == file_b.path_key
                    && file_a.text == file_b.text
            }
            _ => false,
        }
        && diagnostics_equal(a.message_chain(), b.message_chain())
        && diagnostics_equal(a.related_information(), b.related_information())
}

/// `slices.Equal` on `[]*contentmapper.Mapper` — pointer equality.
fn mappers_equal(a: &[Arc<Mapper>], b: &[Arc<Mapper>]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| Arc::ptr_eq(a, b))
}
