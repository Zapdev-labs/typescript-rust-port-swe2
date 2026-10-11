// Ported from tsc/internal/project/projectcollectionbuilder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// PORT(skeleton): pending full port.
//
// PORT(sibling): `ProjectCollectionBuilder` is owned by the sibling
// session/project worker. `projectLoadKind` and the builder field shell +
// API surface below exist because owned infrastructure
// (configfileregistrybuilder.rs, snapshot.rs) names them. Every mutating
// method is `unimplemented!` — real project loading is the sibling port.

use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_contentmapper::Mapper;
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::projectreference::ProjectReference;
use tsc_lsproto::DocumentUri;
use tsc_lsutil::UserPreferences;
use tsc_project_logging::LogTree;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::client::Client;
use crate::configfileregistry::ConfigFileRegistry;
use crate::configfileregistrybuilder::{
    ConfigFileRegistryBuilder, new_config_file_registry_builder,
};
use crate::extendedconfigcache::ExtendedConfigCache;
use crate::filechange::FileChangeSummary;
use crate::overlayfs::Overlay;
use crate::parsecache::{ContentMappedParseCache, ParseCache};
use crate::project::{ConfiguredProjectId, Id, Project, SyntheticProjectId};
use crate::projectcollection::{ApiState, ProjectCollection, open_file_paths};
use crate::session::SessionOptions;
use crate::snapshot::{ApiSnapshotRequest, AtaStateChange, ProjectTreeRequest};
use crate::snapshotfs::{FileSource, SnapshotFsBuilder};

/// `type projectLoadKind int` (projectcollectionbuilder.go).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProjectLoadKind {
    Find = 0,
    Create = 1,
}

/// `ProjectCollectionBuilder` tracks changes made on top of a previous
/// `ProjectCollection`, producing a new clone with `finalize()` after all
/// changes have been made.
///
/// PORT(sibling): field shell + API surface only. `finalize` returns the
// shallow-cloned base so the plumbing is exercisable, but every project-
// level mutation is `unimplemented!` pending the real port.
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
    /// `programStructureChanged`.
    pub program_structure_changed: bool,
    /// `defaultProjectsInvalidated`.
    pub default_projects_invalidated: bool,
    /// `openFilesChanged`.
    pub open_files_changed: bool,

    /// `fileDefaultProjects`.
    pub file_default_projects: FxHashMap<PathKey, Id>,
    /// `configuredProjects` — PORT(sibling): Go `dirty.SyncMap[...]`; plain
    /// maps here until the real port lands (the `dirty` wrappers need
    /// `Cloneable` values, and `Rc<Project>` deliberately has none).
    pub configured_projects: FxHashMap<ConfiguredProjectId, Rc<Project>>,
    /// `syntheticProjects`.
    pub synthetic_projects: FxHashMap<SyntheticProjectId, Rc<Project>>,
    /// `inferredProject` — Go `dirty.Box[*Project]`; see `configuredProjects`.
    pub inferred_project: Option<Rc<Project>>,
    /// `createdPrograms`.
    pub created_programs: Vec<Rc<Project>>,

    /// `apiState`.
    pub api_state: ApiState,
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
        program_structure_changed: false,
        default_projects_invalidated: false,
        open_files_changed: !tsc_collections::Set::equals(
            Some(&open_files),
            Some(&old_project_collection.open_files),
        ),
        file_default_projects: FxHashMap::default(),
        configured_projects: old_project_collection.configured_projects.clone(),
        synthetic_projects: old_project_collection.synthetic_projects.clone(),
        inferred_project: old_project_collection.inferred_project.clone(),
        created_programs: Vec::new(),
        api_state: old_api_state.clone_state(),
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

    /// `Finalize` creates a new `ProjectCollection` and `ConfigFileRegistry`
    /// based on the changes made in the builder.
    ///
    /// PORT(sibling): returns the shallow-cloned base with finalized maps —
    /// the real `Finalize` applies pending config/project diffs and is the
    /// sibling's to port.
    pub fn finalize(
        &self,
        _logger: &LogTree,
    ) -> (Rc<ProjectCollection>, ConfigFileRegistry) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go Finalize")
    }

    /// `HandleAPIRequest`.
    ///
    /// PORT(sibling): `error` → `Result<(), String>` for now; the sibling
    /// should pick the real error channel used by `api.rs`.
    pub fn handle_api_request(
        &mut self,
        _api_request: &ApiSnapshotRequest,
        _logger: &LogTree,
    ) -> Result<(), String> {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go HandleAPIRequest")
    }

    /// `DidChangeFiles`.
    pub fn did_change_files(&mut self, _summary: &FileChangeSummary, _logger: &LogTree) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go DidChangeFiles")
    }

    /// `DidChangeContentMapperContributions`.
    pub fn did_change_content_mapper_contributions(&mut self, _logger: &LogTree) {
        unimplemented!(
            "PORT(sibling): projectcollectionbuilder.go DidChangeContentMapperContributions"
        )
    }

    /// `DidRequestFile`.
    pub fn did_request_file(
        &mut self,
        _uri: DocumentUri,
        _configured_projects_only: bool,
        _logger: &LogTree,
    ) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go DidRequestFile")
    }

    /// `DidRequestProject`.
    pub fn did_request_project(&mut self, _project_id: &Id, _logger: &LogTree) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go DidRequestProject")
    }

    /// `DidRequestProjectTrees`.
    pub fn did_request_project_trees(
        &mut self,
        _project_tree_request: &ProjectTreeRequest,
        _logger: &LogTree,
    ) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go DidRequestProjectTrees")
    }

    /// `DidUpdateATAState`.
    pub fn did_update_ata_state(
        &mut self,
        _ata_changes: &FxHashMap<Id, AtaStateChange>,
        _logger: &LogTree,
    ) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go DidUpdateATAState")
    }

    /// `DidChangeCustomConfigFileName`.
    pub fn did_change_custom_config_file_name(&mut self, _logger: &LogTree) {
        unimplemented!(
            "PORT(sibling): projectcollectionbuilder.go DidChangeCustomConfigFileName"
        )
    }

    /// `DidChangeUserPreferences`.
    pub fn did_change_user_preferences(
        &mut self,
        _old_preferences: &UserPreferences,
        _new_preferences: &UserPreferences,
        _logger: &LogTree,
    ) {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go DidChangeUserPreferences")
    }

    /// `updateInferredProject`.
    pub fn update_inferred_project(
        &mut self,
        _root_file_names: Vec<RootedFilePath>,
        _compiler_options: Option<Arc<CompilerOptions>>,
        _project_references: Vec<ProjectReference>,
        _config_file_parsing_diagnostics: Vec<DiagnosticRef>,
        _content_mappers: Vec<Arc<Mapper>>,
        _logger: &LogTree,
    ) -> bool {
        unimplemented!("PORT(sibling): projectcollectionbuilder.go updateInferredProject")
    }
}
