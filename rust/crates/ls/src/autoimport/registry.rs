// Ported from tsc/internal/ls/autoimport/registry.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(concurrency): Go builds buckets with a `sync.WaitGroup`/`wg.Go`
// pipeline; `Checker`/`Node`/`Symbol` arenas and the `dirty` maps are
// `Rc`/`RefCell`-based and cannot cross threads, so the three-phase
// discovery/extraction/bucket-building pipeline runs sequentially in the same
// order.
//
// PORT(ownership): `*RegistryBucket`/`*directory` map values are plain values
// here; shared/immutable inner state (`paths`, `package_files`, `index`, ...)
// is `Rc`'d so `Clone` shares like Go pointer copies. `dirty.Map` `Change`
// then yields a fresh bucket to mutate.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use rustc_hash::FxHashMap;
use tsc_ast::{ArenaCell, NodeId, ast};
use tsc_checker::checker_types::Program as _;
use tsc_collections::{Set, SyncMap, SyncSet};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::Tristate;
use tsc_dirty as dirty;
use tsc_lsproto::DocumentUri;
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_module::ResolverOptions;
use tsc_module::resolver::{DefaultResolver, ResolvedEntrypoint};
use tsc_packagejson::InfoCacheEntry;
use tsc_project_logging::{LogTree, Logger};
use tsc_symlinks::KnownSymlinks;
use tsc_tspath::{
    CaseSensitivity, ModuleSpecifier, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath,
};

use crate::api::Error;
use crate::autoimport::aliasresolver::new_alias_resolver;
use crate::autoimport::export::Export;
use crate::autoimport::index::Index;
use crate::autoimport::util::{
    CheckerPool, PathAndFileName, add_package_json_dependencies,
    add_project_reference_output_mappings, get_module_resolver, get_package_names_in_node_modules,
    get_package_realpath_funcs, get_resolved_package_names,
};

/// `type ProjectID interface { fmt.Stringer }` — an opaque, displayable
/// project identifier used as a registry bucket key.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ProjectId(pub Rc<str>);

impl fmt::Display for ProjectId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// `knownRecursiveSearchPackages`.
fn known_recursive_search_packages() -> Set<String> {
    tsc_collections::new_set_from_items(
        [
            "@material-ui/core",
            "@material-ui/icons",
            "@sap/cds",
            "@testing-library/react-native",
            "ajv",
            "asap",
            "async",
            "aws-sdk",
            "braintree-web",
            "core-js",
            "core-js-pure",
            "crypto-js",
            "cypress-mochawesome-reporter",
            "dd-trace",
            "dumi",
            "dva",
            "egg-mock",
            "electron-log",
            "es-abstract",
            "es6-promise",
            "eslint-config-taro",
            "expo",
            "expo-router",
            "flow-remove-types",
            "gatsby",
            "glamor",
            "gluegun",
            "graphology-indices",
            "graphology-traversal",
            "graphology-utils",
            "jest-expo",
            "lodash",
            "lodash-es",
            "moment",
            "mz",
            "next",
            "pdfjs-dist",
            "protobufjs",
            "react-app-polyfill",
            "react-dev-utils",
            "react-devtools-inline",
            "recast",
            "semver",
            "stylelint-config-html",
            "umi",
            "web3-provider-engine",
            "webpack",
        ]
        .into_iter()
        .map(str::to_string),
    )
}

/// `type newProgramStructure int`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub enum NewProgramStructure {
    #[default]
    False = 0,
    SameFileNames = 1,
    DifferentFileNames = 2,
}

/// `type bucketBuildPreferences struct` — user preferences that affect how a
/// bucket is built. When any of these change between builds, the bucket must
/// be rebuilt.
#[derive(Clone, Debug, Default)]
pub struct BucketBuildPreferences {
    pub file_exclude_patterns: Vec<String>,
    pub auto_import_entrypoint_directory_search: Tristate,
}

/// `bucketBuildPreferencesFromUserPreferences`.
pub(crate) fn bucket_build_preferences_from_user_preferences(
    prefs: &UserPreferences,
) -> BucketBuildPreferences {
    BucketBuildPreferences {
        file_exclude_patterns: prefs.auto_import_file_exclude_patterns.clone(),
        auto_import_entrypoint_directory_search: prefs.auto_import_entrypoint_directory_search,
    }
}

impl BucketBuildPreferences {
    /// `bucketBuildPreferences.Equal`.
    pub fn equal(&self, other: &BucketBuildPreferences) -> bool {
        tsc_core::core::unordered_equal(&self.file_exclude_patterns, &other.file_exclude_patterns)
            && self.auto_import_entrypoint_directory_search
                == other.auto_import_entrypoint_directory_search
    }
}

/// `type BucketState struct` — the dirty state of a bucket.
#[derive(Clone, Debug, Default)]
pub struct BucketState {
    /// `dirtyFile` is the file that was edited last, if any. It does not
    /// necessarily indicate that no other files have been edited, so it
    /// should be ignored if `multiple_files_dirty` is set. It should not be
    /// used for node_modules buckets, which rely on `dirty_packages` instead.
    pub dirty_file: PathKey,
    /// `multipleFilesDirty`.
    pub multiple_files_dirty: bool,
    /// `newProgramStructure`.
    pub new_program_structure: NewProgramStructure,
    /// `buildPreferences` holds the user preferences that were in effect when
    /// the bucket was built. If changed, the bucket should be rebuilt.
    pub build_preferences: BucketBuildPreferences,
    /// `dirtyPackages` is the set of package names that need to be
    /// re-indexed. `None` = Go nil (no granular updates pending).
    pub dirty_packages: Option<Set<String>>,
    /// `recursiveSearchPackages` — `None` means all non-exports packages were
    /// searched.
    pub recursive_search_packages: Option<Set<String>>,
}

impl BucketState {
    /// `BucketState.Dirty`.
    pub fn dirty(&self) -> bool {
        self.multiple_files_dirty
            || !self.dirty_file.as_string().is_empty()
            || self.new_program_structure > NewProgramStructure::False
            || self.dirty_packages.as_ref().is_some_and(|s| !s.is_empty())
    }

    /// `BucketState.DirtyFile`.
    pub fn dirty_file(&self) -> PathKey {
        if self.multiple_files_dirty {
            return PathKey::default();
        }
        self.dirty_file.clone()
    }

    /// `BucketState.DirtyPackages`.
    pub fn dirty_packages(&self) -> Option<&Set<String>> {
        if self.multiple_files_dirty {
            return None;
        }
        self.dirty_packages.as_ref()
    }

    /// `BucketState.RecursiveSearchPackages`.
    pub fn recursive_search_packages(&self) -> Option<&Set<String>> {
        self.recursive_search_packages.as_ref()
    }

    /// `BucketState.possiblyNeedsRebuildForFile`.
    pub fn possibly_needs_rebuild_for_file(
        &self,
        file: &PathKey,
        preferences: &UserPreferences,
    ) -> bool {
        self.new_program_structure > NewProgramStructure::False
            || self.has_dirty_file_besides(file)
            || !self
                .build_preferences
                .equal(&bucket_build_preferences_from_user_preferences(preferences))
            || self.dirty_packages.as_ref().is_some_and(|s| !s.is_empty())
    }

    /// `BucketState.hasDirtyFileBesides`.
    pub fn has_dirty_file_besides(&self, file: &PathKey) -> bool {
        self.multiple_files_dirty
            || (!self.dirty_file.as_string().is_empty() && self.dirty_file != *file)
    }
}

/// `recursiveSearchSubset` reports whether `target` is a subset of `current`.
/// `None` represents "all packages" — a superset of every concrete set.
pub(crate) fn recursive_search_subset(
    target: Option<&Set<String>>,
    current: Option<&Set<String>>,
) -> bool {
    match (target, current) {
        // Target wants all packages searched — only satisfied if current is
        // also all.
        (None, current) => current.is_none(),
        // Current searched all packages, so any concrete target is satisfied.
        (Some(_), None) => true,
        (Some(target), Some(current)) => Set::is_subset_of(Some(target), Some(current)),
    }
}

/// `type RegistryBucket struct`.
///
/// Bucket contents are considered immutable after the bucket is finalized;
/// the `Rc` fields share backing storage across clones exactly like Go's
/// shared maps/index.
#[derive(Clone, Default)]
pub struct RegistryBucket {
    /// `state`.
    pub(crate) state: BucketState,
    /// `Paths` maps file paths to package names. For project buckets, the
    /// package name is always the empty string.
    pub(crate) paths: Rc<FxHashMap<PathKey, String>>,
    /// `PackageFiles` maps package names to their file paths and file names.
    /// All package directory names in node_modules are keys; indexed packages
    /// have `Some` maps, unindexed packages have `None` (Go nil map).
    pub(crate) package_files: Rc<FxHashMap<String, Option<FxHashMap<PathKey, RootedFilePath>>>>,
    /// `ResolvedPackageNames` is only defined for project buckets.
    pub(crate) resolved_package_names: Option<Rc<Set<String>>>,
    /// `DependencyNames` is only defined for node_modules buckets. `None`
    /// means all packages are included.
    pub(crate) dependency_names: Option<Rc<Set<String>>>,
    /// `AmbientModuleNames` is only defined for node_modules buckets.
    pub(crate) ambient_module_names: Rc<FxHashMap<String, Vec<RootedFilePath>>>,
    /// `Index`. `RefCell` because the ambient-module second pass inserts
    /// into an index that is already installed in a bucket (Go mutates the
    /// shared `*Index`).
    pub(crate) index: Option<Rc<RefCell<Index<Rc<Export>>>>>,
}

impl RegistryBucket {
    /// `newRegistryBucket`.
    pub(crate) fn new_dirty() -> RegistryBucket {
        RegistryBucket {
            state: BucketState {
                multiple_files_dirty: true,
                new_program_structure: NewProgramStructure::DifferentFileNames,
                ..Default::default()
            },
            ..Default::default()
        }
    }

    /// `markProjectFileDirty` — should only be called within a `change` call
    /// on the dirty map; project buckets only.
    pub(crate) fn mark_project_file_dirty(&mut self, file: PathKey) {
        if self.state.has_dirty_file_besides(&file) {
            self.state.multiple_files_dirty = true;
        } else {
            self.state.dirty_file = file;
        }
    }

    /// `markNodeModulesDirty` — should only be called within a `change` call
    /// on the dirty map. If `package_name` is non-empty, that package is
    /// marked for granular update; otherwise the entire bucket is dirty.
    pub(crate) fn mark_node_modules_dirty(&mut self, package_name: &str) {
        if self.state.multiple_files_dirty {
            return;
        }
        if package_name.is_empty() {
            self.state.multiple_files_dirty = true;
            return;
        }
        self.state
            .dirty_packages
            .get_or_insert_with(Set::new)
            .add(package_name.to_string());
    }
}

impl dirty::Cloneable for RegistryBucket {
    /// Go `RegistryBucket.Clone` — shares all backing maps/index.
    fn clone_value(&self) -> Self {
        self.clone()
    }
}

/// `type directory struct`.
#[derive(Clone, Default)]
pub(crate) struct Directory {
    pub(crate) name: RootedDirectoryPath,
    /// `packageJson` — `None` is Go's nil `*InfoCacheEntry`.
    pub(crate) package_json: Option<Arc<InfoCacheEntry>>,
    pub(crate) has_node_modules: bool,
}

impl dirty::Cloneable for Directory {
    /// Go `directory.Clone` — shares `packageJson` (`Arc` clone).
    fn clone_value(&self) -> Self {
        self.clone()
    }
}

/// `type Registry struct`.
///
/// Go `*Registry` is shared by pointer; the registry is immutable once built
/// by [`Registry::clone`], so `&Registry` borrows suffice here.
#[derive(Default)]
pub struct Registry {
    pub(crate) case_sensitivity: CaseSensitivity,
    pub(crate) user_preferences: UserPreferences,
    /// `directories`.
    pub(crate) directories: FxHashMap<PathKey, Directory>,
    /// `nodeModules`.
    pub(crate) node_modules: FxHashMap<PathKey, Rc<RegistryBucket>>,
    /// `projects`.
    pub(crate) projects: FxHashMap<ProjectId, Rc<RegistryBucket>>,
    /// `uniquePackageCount`.
    pub(crate) unique_package_count: usize,
    /// `entrypoints` maps from file path to the resolved entrypoints for that
    /// file, shared across all node_modules buckets.
    pub(crate) entrypoints: FxHashMap<PathKey, Vec<Rc<ResolvedEntrypoint>>>,
    /// `specifierCache` maps from importing file to target file to specifier.
    pub(crate) specifier_cache: FxHashMap<PathKey, Rc<SyncMap<PathKey, ModuleSpecifier>>>,
}

/// `NewRegistry`.
impl Registry {
    pub fn new(case_sensitivity: CaseSensitivity, preferences: UserPreferences) -> Registry {
        Registry {
            case_sensitivity,
            user_preferences: preferences,
            directories: FxHashMap::default(),
            node_modules: FxHashMap::default(),
            projects: FxHashMap::default(),
            unique_package_count: 0,
            entrypoints: FxHashMap::default(),
            specifier_cache: FxHashMap::default(),
        }
    }

    /// `IsPreparedForImportingFile`.
    pub fn is_prepared_for_importing_file(
        &self,
        file_name: &RootedFilePath,
        project_id: &ProjectId,
        preferences: &UserPreferences,
    ) -> bool {
        let Some(project_bucket) = self.projects.get(project_id) else {
            return false;
        };
        let path = self.case_sensitivity.path_key(&file_name.as_path());
        if project_bucket
            .state
            .possibly_needs_rebuild_for_file(&path, preferences)
        {
            return false;
        }

        let mut dir_path = path.parent();
        loop {
            if let Some(dir_bucket) = self.node_modules.get(&dir_path)
                && dir_bucket
                    .state
                    .possibly_needs_rebuild_for_file(&path, preferences)
            {
                return false;
            }
            let parent = dir_path.parent();
            if parent == dir_path {
                break;
            }
            dir_path = parent;
        }
        true
    }

    /// `NodeModulesDirectories`.
    pub fn node_modules_directories(&self) -> FxHashMap<PathKey, RootedDirectoryPath> {
        let mut dirs = FxHashMap::default();
        for (dir_path, dir) in &self.directories {
            if dir.has_node_modules {
                dirs.insert(
                    dir_path.append_canonical_component("node_modules"),
                    dir.name.resolve_directory("node_modules"),
                );
            }
        }
        dirs
    }

    /// `Registry.Clone` — rebuilds the registry for `change` on top of `self`.
    ///
    /// Named `clone_registry` rather than `clone` to keep `Clone`-trait
    /// shorthand free for callers; Go's method is `Clone`.
    pub fn clone_registry(
        &self,
        ctx: &Context,
        change: RegistryChange,
        host: Rc<dyn RegistryCloneHost>,
        current_directory: RootedDirectoryPath,
        logger: &LogTree,
    ) -> Result<Registry, Error> {
        let start = Instant::now();
        let logger = &logger.fork("Building autoimport registry");
        let mut builder = RegistryBuilder::new(self, host, current_directory);
        if let Some(prefs) = &change.user_preferences {
            builder.user_preferences = prefs.clone();
            if !tsc_core::core::unordered_equal(
                &builder
                    .user_preferences
                    .auto_import_specifier_exclude_regexes,
                &self.user_preferences.auto_import_specifier_exclude_regexes,
            ) {
                builder.specifier_cache.clear();
            }
        }
        builder.update_bucket_and_directory_existence(&change, logger);
        builder.mark_buckets_dirty(&change, logger);
        if !change.requested_file.as_string().is_empty() {
            builder.update_indexes(ctx, &change, logger);
        }
        logger.logf(format_args!(
            "Built autoimport registry in {:?}",
            start.elapsed()
        ));
        Ok(builder.build())
    }

    /// `GetCacheStats`.
    pub fn get_cache_stats(&self) -> CacheStats {
        let mut stats = CacheStats {
            unique_package_count: self.unique_package_count,
            ..Default::default()
        };

        for (project_id, bucket) in &self.projects {
            let export_count = bucket
                .index
                .as_ref()
                .map_or(0, |i| i.borrow().entry_count());
            stats.project_buckets.push(BucketStats {
                name: project_id.to_string(),
                export_count,
                file_count: bucket.paths.len(),
                state: bucket.state.clone(),
                dependency_names: bucket.dependency_names.as_deref().cloned(),
                package_names: None,
            });
        }

        for (path, bucket) in &self.node_modules {
            let export_count = bucket
                .index
                .as_ref()
                .map_or(0, |i| i.borrow().entry_count());
            // Derive package names from `PackageFiles` keys.
            let mut package_names = None;
            let mut file_count = 0;
            package_names = Some(Set::with_size_hint(bucket.package_files.len()));
            for (name, paths) in bucket.package_files.iter() {
                package_names.as_mut().unwrap().add(name.clone());
                file_count += paths.as_ref().map_or(0, |p| p.len());
            }
            stats.node_modules_buckets.push(BucketStats {
                name: path.as_string().to_string(),
                export_count,
                file_count,
                state: bucket.state.clone(),
                dependency_names: bucket.dependency_names.as_deref().cloned(),
                package_names,
            });
        }

        stats.project_buckets.sort_by(|a, b| a.name.cmp(&b.name));
        stats
            .node_modules_buckets
            .sort_by(|a, b| a.name.cmp(&b.name));
        stats
    }
}

/// `type BucketStats struct`.
#[derive(Clone, Default)]
pub struct BucketStats {
    pub name: String,
    pub export_count: usize,
    pub file_count: usize,
    pub state: BucketState,
    pub dependency_names: Option<Set<String>>,
    pub package_names: Option<Set<String>>,
}

/// `type CacheStats struct`.
#[derive(Clone, Default)]
pub struct CacheStats {
    pub project_buckets: Vec<BucketStats>,
    pub node_modules_buckets: Vec<BucketStats>,
    pub unique_package_count: usize,
}

/// `type RegistryChange struct`.
#[derive(Default)]
pub struct RegistryChange {
    /// `RequestedFile`.
    pub requested_file: PathKey,
    /// `RequestedFileName`.
    pub requested_file_name: RootedFilePath,
    /// `OpenFiles`.
    pub open_files: HashMap<PathKey, RootedFilePath>,
    /// `Changed`.
    pub changed: Set<DocumentUri>,
    /// `Created`.
    pub created: Set<DocumentUri>,
    /// `Deleted`.
    pub deleted: Set<DocumentUri>,
    /// `RebuiltPrograms` maps from project ID to:
    ///   - `true`: the program was rebuilt with a different set of file names
    ///   - `false`: the program was rebuilt but the file names are unchanged
    pub rebuilt_programs: HashMap<ProjectId, bool>,
    /// `UserPreferences`.
    pub user_preferences: Option<UserPreferences>,
}

/// `type RegistryCloneHost interface`.
pub trait RegistryCloneHost {
    /// `FS()`.
    fn fs(&self) -> Arc<dyn tsc_vfs::Vfs>;
    /// `GetDefaultProject(path)` — `None` is Go's `(nil, nil)`.
    fn get_default_project(&self, path: &PathKey) -> Option<(ProjectId, Rc<Program>)>;
    /// `GetProgramForProject(projectID)`.
    fn get_program_for_project(&self, project_id: &ProjectId) -> Option<Rc<Program>>;
    /// `GetPackageJson(fileName)` — never nil in Go's implementation.
    fn get_package_json(&self, file_name: &RootedFilePath) -> Arc<InfoCacheEntry>;
    /// `GetSourceFile(fileName, path)` — returns the file's root `NodeId` and
    /// its node arena; `None` is Go's nil `*ast.SourceFile` (e.g.
    /// symlink/realpath mismatch).
    fn get_source_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<(NodeId, Rc<ArenaCell>)>;
    /// `Dispose()`.
    fn dispose(&self);
}

/// `type registryBuilder struct`.
struct RegistryBuilder {
    host: Rc<dyn RegistryCloneHost>,
    base_case_sensitivity: CaseSensitivity,
    /// `b.base.nodeModules` — only read for the `hadNodeModules` check and
    /// old-bucket lookups.
    base_node_modules: FxHashMap<PathKey, Rc<RegistryBucket>>,
    /// `b.base.specifierCache`.
    base_specifier_cache: FxHashMap<PathKey, Rc<SyncMap<PathKey, ModuleSpecifier>>>,
    /// `b.base.entrypoints` — read by `updateNodeModulesBucket`.
    base_entrypoints: FxHashMap<PathKey, Vec<Rc<ResolvedEntrypoint>>>,
    /// `b.base.directories` — read by `DiffMapsFunc`.
    base_directories: FxHashMap<PathKey, Directory>,
    /// `b.base.projects`.
    base_projects: FxHashMap<ProjectId, Rc<RegistryBucket>>,
    current_directory: RootedDirectoryPath,

    user_preferences: UserPreferences,
    directories: dirty::Map<PathKey, Directory>,
    node_modules: dirty::Map<PathKey, Rc<RegistryBucket>>,
    projects: dirty::Map<ProjectId, Rc<RegistryBucket>>,
    specifier_cache: dirty::MapBuilder<
        PathKey,
        Rc<SyncMap<PathKey, ModuleSpecifier>>,
        Rc<SyncMap<PathKey, ModuleSpecifier>>,
        fn(Rc<SyncMap<PathKey, ModuleSpecifier>>) -> Rc<SyncMap<PathKey, ModuleSpecifier>>,
        fn(Rc<SyncMap<PathKey, ModuleSpecifier>>) -> Rc<SyncMap<PathKey, ModuleSpecifier>>,
    >,
    resolver_options: ResolverOptions,

    unique_package_count: usize,
    entrypoints: dirty::MapBuilder<
        PathKey,
        Vec<Rc<ResolvedEntrypoint>>,
        Vec<Rc<ResolvedEntrypoint>>,
        fn(Vec<Rc<ResolvedEntrypoint>>) -> Vec<Rc<ResolvedEntrypoint>>,
        fn(Vec<Rc<ResolvedEntrypoint>>) -> Vec<Rc<ResolvedEntrypoint>>,
    >,
}

/// `newRegistryBuilder`.
impl RegistryBuilder {
    fn new(
        registry: &Registry,
        host: Rc<dyn RegistryCloneHost>,
        current_directory: RootedDirectoryPath,
    ) -> RegistryBuilder {
        let host_fs = host.fs();
        let current_directory_clone = current_directory.clone();
        RegistryBuilder {
            host,
            base_case_sensitivity: registry.case_sensitivity,
            base_node_modules: registry.node_modules.clone(),
            base_specifier_cache: registry.specifier_cache.clone(),
            base_entrypoints: registry.entrypoints.clone(),
            base_directories: registry.directories.clone(),
            base_projects: registry.projects.clone(),
            current_directory,

            user_preferences: registry.user_preferences.clone(),
            directories: dirty::Map::new(Some(registry.directories.clone())),
            node_modules: dirty::Map::new(Some(registry.node_modules.clone())),
            projects: dirty::Map::new(Some(registry.projects.clone())),
            specifier_cache: dirty::MapBuilder::new(
                Some(registry.specifier_cache.clone()),
                tsc_core::core::identity,
                tsc_core::core::identity,
            ),
            // Always re-initialized (host + compiler_options) before use.
            resolver_options: ResolverOptions {
                host: Arc::new(crate::autoimport::util::ResolutionHostImpl {
                    fs: host_fs,
                    current_directory: current_directory_clone,
                }),
                compiler_options: Arc::new(
                    tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS.clone(),
                ),
                typings_location: RootedDirectoryPath::default(),
                project_name: String::new(),
                extra_extensions: Vec::new(),
                package_json_cache: None,
            },
            unique_package_count: registry.unique_package_count,
            entrypoints: dirty::MapBuilder::new(
                Some(registry.entrypoints.clone()),
                tsc_core::core::identity,
                tsc_core::core::identity,
            ),
        }
    }

    /// `registryBuilder.Build`.
    fn build(self) -> Registry {
        Registry {
            case_sensitivity: self.base_case_sensitivity,
            user_preferences: self.user_preferences,
            directories: self.directories.finalize().0.unwrap_or_default(),
            node_modules: self.node_modules.finalize().0.unwrap_or_default(),
            projects: self.projects.finalize().0.unwrap_or_default(),
            specifier_cache: self.specifier_cache.build().unwrap_or_default(),
            unique_package_count: self.unique_package_count,
            entrypoints: self.entrypoints.build().unwrap_or_default(),
        }
    }

    /// `registryBuilder.newExportExtractor`.
    fn new_export_extractor(
        &self,
        package_name: String,
        checker: Rc<RefCell<tsc_checker::checker_core::Checker>>,
        module_resolver: Rc<DefaultResolver>,
        realpath: Option<crate::autoimport::util::RealpathFn>,
    ) -> crate::autoimport::extract::SymbolExtractor {
        crate::autoimport::extract::SymbolExtractor::new_export(
            package_name,
            checker,
            self.base_case_sensitivity,
            module_resolver,
            realpath,
        )
    }

    /// `updateBucketAndDirectoryExistence`.
    fn update_bucket_and_directory_existence(&mut self, change: &RegistryChange, logger: &LogTree) {
        let start = Instant::now();
        let mut needed_projects: FxHashMap<ProjectId, ()> = FxHashMap::default();
        let mut needed_directories: FxHashMap<PathKey, RootedDirectoryPath> = FxHashMap::default();
        let mut add_needed_directories = |path: &PathKey, file_name: &RootedFilePath| {
            if file_name.is_dynamic() {
                return;
            }
            let mut dir = file_name.directory();
            let mut dir_path = path.parent();
            loop {
                if needed_directories.contains_key(&dir_path) {
                    break;
                }
                needed_directories.insert(dir_path.clone(), dir.clone());
                let parent_path = dir_path.parent();
                let parent_dir = dir.as_path().directory();
                if parent_path == dir_path || parent_dir == dir {
                    break;
                }
                dir_path = parent_path;
                dir = parent_dir;
            }
        };
        for (path, file_name) in &change.open_files {
            if let Some((project_id, _)) = self.host.get_default_project(path) {
                needed_projects.insert(project_id, ());
            }
            add_needed_directories(path, file_name);

            if !self.specifier_cache.has(path) {
                self.specifier_cache
                    .set(path.clone(), Rc::new(SyncMap::new()));
            }
        }

        if !change.requested_file.as_string().is_empty() {
            add_needed_directories(&change.requested_file, &change.requested_file_name);
            if let Some((project_id, _)) = self.host.get_default_project(&change.requested_file) {
                needed_projects.insert(project_id, ());
            }
            if !self.specifier_cache.has(&change.requested_file) {
                self.specifier_cache
                    .set(change.requested_file.clone(), Rc::new(SyncMap::new()));
            }
        }

        for path in self.base_specifier_cache.keys() {
            if !change.open_files.contains_key(path) && *path != change.requested_file {
                self.specifier_cache.delete(path);
            }
        }

        let mut added_projects: Vec<ProjectId> = Vec::new();
        let mut removed_projects: Vec<ProjectId> = Vec::new();
        tsc_core::core::diff_maps_func(
            &self.base_projects,
            &needed_projects,
            |_a: &Rc<RegistryBucket>, _b: &()| panic!("never called because onChanged is nil"),
            Some(&mut |project_id: &ProjectId, _: &()| {
                // Need and don't have
                self.projects
                    .add(project_id.clone(), Rc::new(RegistryBucket::new_dirty()));
                added_projects.push(project_id.clone());
            }),
            Some(&mut |project_id: &ProjectId, _: &Rc<RegistryBucket>| {
                // Have and don't need
                self.projects.delete(project_id);
                removed_projects.push(project_id.clone());
            }),
            None,
        );
        for project_id in &added_projects {
            logger.logf(format_args!("Added project: {}", project_id));
        }
        for project_id in &removed_projects {
            logger.logf(format_args!("Removed project: {}", project_id));
        }

        let fs = self.host.fs();
        let update_directory = |dir_path: &PathKey,
                                dir_name: &RootedDirectoryPath,
                                package_json_changed: bool| {
            let package_json_file_name = dir_name.resolve_file("package.json");
            let has_node_modules = fs.directory_exists(&dir_name.resolve_directory("node_modules"));
            if let Some(entry) = self.directories.get(dir_path) {
                entry.change_if(
                    |dir: Option<Directory>| {
                        package_json_changed
                            || dir.is_some_and(|d| d.has_node_modules != has_node_modules)
                    },
                    |dir: &mut Directory| {
                        dir.package_json =
                            Some(self.host.get_package_json(&package_json_file_name));
                        dir.has_node_modules = has_node_modules;
                    },
                );
            } else {
                self.directories.add(
                    dir_path.clone(),
                    Directory {
                        name: dir_name.clone(),
                        package_json: Some(self.host.get_package_json(&package_json_file_name)),
                        has_node_modules,
                    },
                );
            }

            if has_node_modules {
                if self.node_modules.get(dir_path).is_none() {
                    self.node_modules
                        .add(dir_path.clone(), Rc::new(RegistryBucket::new_dirty()));
                }
            } else {
                self.node_modules.try_delete(dir_path);
            }
        };
        let update_directory = &update_directory;

        let package_json_changed = |dir_name: &RootedDirectoryPath| -> bool {
            let uri = tsc_lsconv::converters::file_name_to_document_uri(
                &dir_name.resolve_file("package.json"),
            );
            change.changed.has(&uri) || change.deleted.has(&uri) || change.created.has(&uri)
        };

        let mut added_node_modules_dirs: Vec<PathKey> = Vec::new();
        let mut removed_node_modules_dirs: Vec<PathKey> = Vec::new();
        let fs = self.host.fs();
        tsc_core::core::diff_maps_func(
            &self.base_directories,
            &needed_directories,
            |dir: &Directory, dir_name: &RootedDirectoryPath| {
                !package_json_changed(dir_name)
                    && dir.has_node_modules
                        == fs.directory_exists(&dir_name.resolve_directory("node_modules"))
            },
            Some(&mut |dir_path: &PathKey, dir_name: &RootedDirectoryPath| {
                // Need and don't have
                let had_node_modules = self.base_node_modules.contains_key(dir_path);
                update_directory(dir_path, dir_name, false);
                logger.logf(format_args!("Added directory: {}", dir_path.as_string()));
                if self.node_modules.get(dir_path).is_some() && !had_node_modules {
                    added_node_modules_dirs.push(dir_path.clone());
                }
            }),
            Some(&mut |dir_path: &PathKey, _dir: &Directory| {
                // Have and don't need
                let had_node_modules = self.base_node_modules.contains_key(dir_path);
                self.directories.delete(dir_path);
                self.node_modules.try_delete(dir_path);
                logger.logf(format_args!("Removed directory: {}", dir_path.as_string()));
                if had_node_modules {
                    removed_node_modules_dirs.push(dir_path.clone());
                }
            }),
            Some(
                &mut |dir_path: &PathKey, _dir: &Directory, dir_name: &RootedDirectoryPath| {
                    update_directory(dir_path, dir_name, package_json_changed(dir_name));
                    logger.logf(format_args!("Changed directory: {}", dir_path.as_string()));
                },
            ),
        );

        for dir_path in &added_node_modules_dirs {
            logger.logf(format_args!(
                "Added node_modules bucket: {}",
                dir_path.as_string()
            ));
        }
        for dir_path in &removed_node_modules_dirs {
            logger.logf(format_args!(
                "Removed node_modules bucket: {}",
                dir_path.as_string()
            ));
        }
        logger.logf(format_args!(
            "Updated buckets and directories in {:?}",
            start.elapsed()
        ));
    }

    /// `markBucketsDirty`.
    fn mark_buckets_dirty(&self, change: &RegistryChange, _logger: &LogTree) {
        // Mark new program structures
        for (project_id, new_file_names) in &change.rebuilt_programs {
            if let Some(bucket) = self.projects.get(project_id) {
                bucket.change(|b: &mut Rc<RegistryBucket>| {
                    Rc::make_mut(b).state.new_program_structure = if *new_file_names {
                        NewProgramStructure::DifferentFileNames
                    } else {
                        NewProgramStructure::SameFileNames
                    };
                });
            }
        }

        // Mark files dirty, bailing out if all buckets already have multiple
        // files dirty
        let mut clean_node_modules_buckets: HashMap<PathKey, ()> = HashMap::new();
        let mut clean_project_buckets: HashMap<ProjectId, ()> = HashMap::new();
        self.node_modules.range(|entry| {
            if !entry.value().is_some_and(|v| v.state.multiple_files_dirty) {
                clean_node_modules_buckets.insert(entry.key(), ());
            }
            true
        });
        self.projects.range(|entry| {
            if !entry.value().is_some_and(|v| v.state.multiple_files_dirty) {
                clean_project_buckets.insert(entry.key(), ());
            }
            true
        });

        let mut clean_node_modules_buckets = clean_node_modules_buckets;
        let mut clean_project_buckets = clean_project_buckets;
        let mut mark_files_dirty = |uris: &rustc_hash::FxHashSet<DocumentUri>| {
            if clean_node_modules_buckets.is_empty() && clean_project_buckets.is_empty() {
                return;
            }
            for uri in uris {
                let path = self
                    .base_case_sensitivity
                    .path_key(&uri.file_name().as_path());
                if !clean_node_modules_buckets.is_empty() {
                    // For node_modules, mark the bucket dirty if anything
                    // changes in the directory. The path could be either a
                    // symlink path (containing /node_modules/) or a realpath
                    // (for symlinked project references). Both are recorded in
                    // Paths for granular updates.
                    if let Some((dir_path, _rest)) =
                        path.split_at_canonical_component("node_modules")
                    {
                        if clean_node_modules_buckets.contains_key(&dir_path) {
                            let entry = self
                                .node_modules
                                .get(&dir_path)
                                .expect("dirty map missing bucket");
                            // Look up the package name for granular updates
                            let package_name = entry
                                .value()
                                .and_then(|b| b.paths.get(&path).cloned())
                                .unwrap_or_default();
                            entry.change(|b: &mut Rc<RegistryBucket>| {
                                Rc::make_mut(b).mark_node_modules_dirty(&package_name)
                            });
                            if !entry.value().is_some_and(|b| b.state.multiple_files_dirty) {
                                clean_node_modules_buckets.remove(&dir_path);
                            }
                        }
                    } else {
                        // Check if this path (possibly a realpath of a
                        // workspace package) is in any bucket's Paths. This
                        // handles local workspace packages where the realpath
                        // doesn't contain /node_modules/.
                        let bucket_dir_paths: Vec<PathKey> =
                            clean_node_modules_buckets.keys().cloned().collect();
                        for bucket_dir_path in bucket_dir_paths {
                            let entry = self
                                .node_modules
                                .get(&bucket_dir_path)
                                .expect("dirty map missing bucket");
                            if let Some(package_name) =
                                entry.value().and_then(|b| b.paths.get(&path).cloned())
                            {
                                // Use the package name for granular updates
                                entry.change(|b: &mut Rc<RegistryBucket>| {
                                    Rc::make_mut(b).mark_node_modules_dirty(&package_name)
                                });
                                if !entry.value().is_some_and(|b| b.state.multiple_files_dirty) {
                                    clean_node_modules_buckets.remove(&bucket_dir_path);
                                }
                            }
                        }
                    }
                }

                // For projects, mark the bucket dirty if the bucket contains
                // the file directly. Any other significant change, like a
                // created failed lookup location, is handled by
                // newProgramStructure.
                let project_dir_paths: Vec<ProjectId> =
                    clean_project_buckets.keys().cloned().collect();
                for project_dir_path in project_dir_paths {
                    let Some(entry) = self.projects.get(&project_dir_path) else {
                        continue;
                    };
                    if entry.value().is_some_and(|b| b.paths.contains_key(&path)) {
                        // Project buckets don't use package-based granular
                        // updates
                        entry.change(|b: &mut Rc<RegistryBucket>| {
                            Rc::make_mut(b).mark_project_file_dirty(path.clone())
                        });
                        if !entry.value().is_some_and(|b| b.state.multiple_files_dirty) {
                            clean_project_buckets.remove(&project_dir_path);
                        }
                    }
                }
            }
        };

        mark_files_dirty(change.created.keys());
        mark_files_dirty(change.deleted.keys());
        mark_files_dirty(change.changed.keys());
    }

    /// `updateIndexes` — the three-phase discovery/extraction/bucket-building
    /// pipeline, run sequentially (see module header).
    fn update_indexes(&mut self, ctx: &Context, change: &RegistryChange, logger: &LogTree) {
        struct NodeModulesBucketTask {
            entry: dirty::MapEntry<PathKey, Rc<RegistryBucket>>,
            dependency_names: Option<Rc<Set<String>>>,
            dir_name: RootedDirectoryPath,
            dir_path: PathKey,
            is_update: bool,
            existing_bucket: Option<Rc<RegistryBucket>>,
            dirty_packages: Option<Set<String>>,

            // Filled by discovery.
            package_names: Option<Set<String>>,
            directory_package_names: Option<Set<String>>,
            discovered: Vec<Rc<DiscoveredPackage>>,
        }

        let Some((project_id, _program)) = self.host.get_default_project(&change.requested_file)
        else {
            return;
        };

        // Compute resolved package names and project reference output
        // mappings for all projects upfront. Resolved package names are needed
        // to compute node_modules dependencies so packages that are directly
        // imported by programs are included even if not listed in
        // package.json. Project reference output mappings are needed to
        // redirect extraction from output .d.ts files to source files for
        // packages that are project references. We need all projects because a
        // node_modules directory can be used by multiple projects.
        let mut all_resolved_package_names: HashMap<ProjectId, Rc<Set<String>>> = HashMap::new();
        let mut project_reference_outputs: FxHashMap<PathKey, RootedFilePath> =
            FxHashMap::default();
        // Compute which packages have implicit deep imports (subpath imports
        // in packages without exports). These packages need recursive
        // directory search to discover all auto-importable files, even when
        // the preference is disabled.
        let mut all_deep_import_packages = Set::new();
        self.projects.range(|entry| {
            if let Some(program) = self.host.get_program_for_project(&entry.key()) {
                all_resolved_package_names.insert(
                    entry.key(),
                    Rc::new(get_resolved_package_names(ctx, &program)),
                );
                add_project_reference_output_mappings(&program, &mut project_reference_outputs);
                for name in program.deep_import_package_names() {
                    all_deep_import_packages.add(name.clone());
                }
            }
            true
        });

        let file_exclude_patterns = self
            .user_preferences
            .parsed_auto_import_file_exclude_patterns(self.host.fs().case_sensitivity());

        // Determine which packages need recursive directory search for this
        // build. `None` means all packages (preference is enabled for all).
        let mut target_recursive_packages: Option<Set<String>> = None;
        if !self
            .user_preferences
            .auto_import_entrypoint_directory_search
            .is_true()
        {
            target_recursive_packages = Some(all_deep_import_packages);
        }

        // --- Collect node_modules tasks ---
        let known_recursive = known_recursive_search_packages();
        let mut node_modules_tasks: Vec<NodeModulesBucketTask> = Vec::new();
        change
            .requested_file
            .for_each_ancestor_directory(|dir_path| {
                if let Some(node_modules_bucket) = self.node_modules.get(dir_path) {
                    let dir_name = self
                        .directories
                        .get(dir_path)
                        .and_then(|e| e.value())
                        .map(|d| d.name)
                        .unwrap_or_default();
                    let dependencies = self.compute_dependencies_for_node_modules_directory(
                        change,
                        &all_resolved_package_names,
                        &dir_name,
                        dir_path,
                    );
                    let bucket_value = node_modules_bucket.value().unwrap_or_default();
                    let bucket_state = bucket_value.state.clone();
                    // !!! Optimization: handle different dependency set via
                    //     granular updates
                    let needs_full_rebuild = bucket_state.multiple_files_dirty
                        || !Set::equals(
                            bucket_value.dependency_names.as_deref(),
                            dependencies.as_deref(),
                        )
                        || !bucket_state.build_preferences.equal(
                            &bucket_build_preferences_from_user_preferences(&self.user_preferences),
                        )
                        || !recursive_search_subset(
                            target_recursive_packages.as_ref(),
                            bucket_state.recursive_search_packages(),
                        );
                    let dirty_packages = bucket_state.dirty_packages().cloned();
                    let can_do_granular_update = !needs_full_rebuild
                        && dirty_packages.as_ref().is_some_and(|s| !s.is_empty());

                    if needs_full_rebuild {
                        node_modules_tasks.push(NodeModulesBucketTask {
                            entry: node_modules_bucket,
                            dependency_names: dependencies,
                            dir_name,
                            dir_path: dir_path.clone(),
                            is_update: false,
                            existing_bucket: None,
                            dirty_packages: None,
                            package_names: None,
                            directory_package_names: None,
                            discovered: Vec::new(),
                        });
                    } else if can_do_granular_update {
                        node_modules_tasks.push(NodeModulesBucketTask {
                            entry: node_modules_bucket.clone(),
                            dependency_names: dependencies,
                            dir_name,
                            dir_path: dir_path.clone(),
                            is_update: true,
                            existing_bucket: Some(bucket_value),
                            dirty_packages,
                            package_names: None,
                            directory_package_names: None,
                            discovered: Vec::new(),
                        });
                    }
                }
                ((), false)
            });

        let node_modules_logger = if !node_modules_tasks.is_empty() {
            logger.fork("Building node_modules indexes")
        } else {
            LogTree::none()
        };

        // --- Phase 1: Discovery ---
        // Resolve package.json and realpath for each package in each bucket.
        let discovery_start = Instant::now();
        for task in &mut node_modules_tasks {
            if task.is_update {
                task.package_names = task.dirty_packages.clone();
            } else {
                task.directory_package_names = Some(get_package_names_in_node_modules(
                    &task.dir_name.resolve_directory("node_modules"),
                    &self.host.fs(),
                ));
                task.package_names = tsc_core::core::coalesce(
                    task.dependency_names.as_deref().cloned(),
                    task.directory_package_names.clone(),
                );
            }
            let package_names = task.package_names.take();
            if let Some(package_names) = package_names {
                task.discovered =
                    self.discover_bucket_packages(&package_names, &task.dir_name, &task.dir_path);
                task.package_names = Some(package_names);
            }
        }
        node_modules_logger.logf(format_args!(
            "Discovered packages: {:?}",
            discovery_start.elapsed()
        ));

        // --- Phase 2: Extraction ---
        // Extract from main packages first. If a main package has no
        // TypeScript entrypoints, we fall back to extracting from @types in a
        // second pass. Packages with no main package extract directly from
        // @types in the primary pass.
        let extraction_start = Instant::now();
        let mut seen: HashMap<RootedDirectoryPath, bool> = HashMap::new();
        let mut extraction_cache: HashMap<RootedDirectoryPath, Rc<PerPackageExtractionResult>> =
            HashMap::new();
        // Collect all packages that have an @types fallback. After the primary
        // pass, we filter to only those whose main extraction failed, then
        // deduplicate by typesRealpath.
        let mut types_fallback_candidates: Vec<Rc<DiscoveredPackage>> = Vec::new();
        for task in &node_modules_tasks {
            for pkg in &task.discovered {
                if !pkg.realpath.as_string().is_empty() {
                    if !seen.contains_key(&pkg.realpath) {
                        seen.insert(pkg.realpath.clone(), true);
                        let enable_dir_search = target_recursive_packages.is_none()
                            || target_recursive_packages
                                .as_ref()
                                .is_some_and(|s| s.has(&pkg.package_name))
                            || known_recursive.has(&pkg.package_name);
                        // Record actual directory-searched packages so the
                        // stored set reflects reality for rebuild detection
                        // and stats.
                        if enable_dir_search && let Some(target) = &mut target_recursive_packages {
                            target.add(pkg.package_name.clone());
                        }
                        if ctx.is_cancelled() {
                            continue;
                        }
                        if let Some(result) = self.extract_package(
                            ctx,
                            &pkg.package_json,
                            &pkg.package_name,
                            &project_reference_outputs,
                            file_exclude_patterns.as_ref(),
                            enable_dir_search,
                        ) {
                            extraction_cache.insert(pkg.realpath.clone(), result);
                        }
                    }
                    if !pkg.types_realpath.as_string().is_empty() {
                        types_fallback_candidates.push(pkg.clone());
                    }
                } else if !pkg.types_realpath.as_string().is_empty() {
                    if !seen.contains_key(&pkg.types_realpath) {
                        seen.insert(pkg.types_realpath.clone(), true);
                        // @types packages always get directory search
                        if let Some(target) = &mut target_recursive_packages {
                            target.add(pkg.package_name.clone());
                        }
                        if ctx.is_cancelled() {
                            continue;
                        }
                        if let Some(result) = self.extract_package(
                            ctx,
                            pkg.types_package_json.as_ref().unwrap(),
                            &pkg.package_name,
                            &project_reference_outputs,
                            file_exclude_patterns.as_ref(),
                            true, /*enableDirectorySearch*/
                        ) {
                            extraction_cache.insert(pkg.types_realpath.clone(), result);
                        }
                    }
                }
            }
        }

        // For packages whose main extraction yielded nothing, fall back to
        // @types.
        for pkg in &types_fallback_candidates {
            let main_extracted = extraction_cache.contains_key(&pkg.realpath);
            if main_extracted || seen.contains_key(&pkg.types_realpath) {
                continue;
            }
            seen.insert(pkg.types_realpath.clone(), true);
            // @types fallback packages always get directory search
            if let Some(target) = &mut target_recursive_packages {
                target.add(pkg.package_name.clone());
            }
            if ctx.is_cancelled() {
                continue;
            }
            if let Some(result) = self.extract_package(
                ctx,
                pkg.types_package_json.as_ref().unwrap(),
                &pkg.package_name,
                &project_reference_outputs,
                file_exclude_patterns.as_ref(),
                true, /*enableDirectorySearch*/
            ) {
                extraction_cache.insert(pkg.types_realpath.clone(), result);
            }
        }
        node_modules_logger.logf(format_args!(
            "Extracted exports: {:?} ({} packages)",
            extraction_start.elapsed(),
            seen.len()
        ));
        self.unique_package_count = seen.len();

        // --- Phase 3: Bucket building ---
        // Each bucket installs the shared extraction results and builds its
        // index.
        let mut all_results: Vec<BucketBuildResult> = Vec::new();

        for task in node_modules_tasks {
            let task_entry = task.entry.clone();
            let mut br = BucketBuildResult {
                replace_bucket: Some(Box::new(move |bucket: RegistryBucket| {
                    task_entry.replace(Rc::new(bucket))
                })),
                resolution_path: task.entry.key(),
                ..Default::default()
            };
            if task.is_update {
                self.update_node_modules_bucket(
                    ctx,
                    &mut br,
                    task.existing_bucket.as_ref().unwrap(),
                    task.dirty_packages.as_ref(),
                    &task.discovered,
                    &extraction_cache,
                    target_recursive_packages.as_ref(),
                    &node_modules_logger.fork(task.dir_name.as_string()),
                );
            } else {
                self.build_node_modules_bucket(
                    ctx,
                    &mut br,
                    task.dependency_names.as_ref(),
                    &task.dir_path,
                    &task.discovered,
                    task.directory_package_names.as_ref(),
                    &extraction_cache,
                    target_recursive_packages.as_ref(),
                    &node_modules_logger.fork(task.dir_name.as_string()),
                );
            }
            all_results.push(br);
        }

        // Project bucket (not part of the three-phase pipeline — no
        // cross-bucket dedup needed).
        if let Some(project) = self.projects.get(&project_id) {
            let program = self.host.get_program_for_project(&project_id);
            let resolved_package_names = all_resolved_package_names.get(&project_id).cloned();
            let project_value = project.value().unwrap_or_default();
            let mut should_rebuild = project_value
                .state
                .has_dirty_file_besides(&change.requested_file)
                || !project_value.state.build_preferences.equal(
                    &bucket_build_preferences_from_user_preferences(&self.user_preferences),
                );
            if !should_rebuild
                && project_value.state.new_program_structure > NewProgramStructure::False
            {
                if let Some(program) = &program {
                    if !Set::equals(
                        project_value.resolved_package_names.as_deref(),
                        resolved_package_names.as_deref(),
                    ) || has_new_non_node_modules_files(program, &project_value)
                    {
                        should_rebuild = true;
                    } else {
                        project.change(|b: &mut Rc<RegistryBucket>| {
                            Rc::make_mut(b).state.new_program_structure = NewProgramStructure::False
                        });
                    }
                } else {
                    should_rebuild = true;
                }
            }
            if should_rebuild {
                let project_entry = project.clone();
                let mut br = BucketBuildResult {
                    replace_bucket: Some(Box::new(move |bucket: RegistryBucket| {
                        project_entry.replace(Rc::new(bucket))
                    })),
                    resolution_path: program.as_ref().map_or_else(PathKey::default, |p| {
                        self.base_case_sensitivity
                            .path_key(&p.base_directory().as_path())
                    }),
                    ..Default::default()
                };
                if let Some(program) = &program {
                    self.build_project_bucket(
                        ctx,
                        &mut br,
                        &project_id,
                        program,
                        resolved_package_names,
                        &logger.fork(&format!("Building project bucket {}", project_id)),
                    );
                }
                all_results.push(br);
            }
        }

        for br in &all_results {
            if br.err.is_some() {
                continue;
            }
            for path in &br.removed_entrypoint_paths {
                self.entrypoints.delete(path);
            }
            for (path, entries) in &br.entrypoints {
                self.entrypoints.set(path.clone(), entries.clone());
            }
            if let Some(replace) = &br.replace_bucket {
                replace(br.bucket.clone());
            }
        }

        // If we failed to resolve any alias exports by ending up at a
        // non-relative module specifier that didn't resolve to another
        // package, it's probably an ambient module declared in another
        // package. We recorded these failures, along with the name of every
        // ambient module declared elsewhere, so we can do a second pass on the
        // failed files, this time including the ambient modules declarations
        // that were missing the first time. Example:
        // node_modules/fs-extra/index.d.ts is simply `export * from "fs"`, but
        // when trying to resolve the `export *`, we don't know where "fs" is
        // declared. The aliasResolver tries to find packages named "fs" on the
        // file system, but after failing, records "fs" as a failure for
        // fs-extra/index.d.ts. Meanwhile, if we also processed
        // node_modules/@types/node/fs.d.ts, we recorded that file as declaring
        // the ambient module "fs". In the second pass, we combine those two
        // files and reprocess fs-extra/index.d.ts, this time finding "fs"
        // declared in @types/node.
        let second_pass_start = Instant::now();
        let mut second_pass_file_count = 0;
        for br in &all_results {
            if br.err.is_some() {
                continue;
            }
            let Some(targets) = &br.possible_failed_ambient_module_lookup_targets else {
                continue;
            };
            let mut root_files: FxHashMap<RootedFilePath, (NodeId, Rc<ArenaCell>)> =
                FxHashMap::default();
            for target in targets.keys() {
                for file_name in self.resolve_ambient_module_name(&target, &br.resolution_path) {
                    if root_files.contains_key(&file_name) {
                        continue;
                    }
                    let path = self.base_case_sensitivity.path_key(&file_name.as_path());
                    if let Some((file, arena)) = self.host.get_source_file(&file_name, &path) {
                        root_files.insert(file_name, (file, arena));
                        second_pass_file_count += 1;
                    }
                }
            }
            if !root_files.is_empty() {
                let mut resolver_options = self.resolver_options.clone();
                resolver_options.host = Arc::new(crate::autoimport::util::ResolutionHostImpl {
                    fs: self.host.fs(),
                    current_directory: self.current_directory.clone(),
                });
                resolver_options.compiler_options =
                    Arc::new(tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS.clone());
                let module_resolver = Rc::new(DefaultResolver::new(resolver_options));
                let alias_resolver = new_alias_resolver(
                    root_files.values().cloned().collect(),
                    HashMap::new(),
                    self.host.clone(),
                    module_resolver.clone(),
                    None,
                );
                let ch = Rc::new(RefCell::new(
                    tsc_checker::checker_core::Checker::new_checker(alias_resolver.clone(), None),
                ));
                let sources = br
                    .possible_failed_ambient_module_lookup_sources
                    .as_ref()
                    .map(|s| s.to_map())
                    .unwrap_or_default();
                for (path, source) in sources {
                    let Some(source_file) =
                        alias_resolver.get_source_file_by_file_name(&source.file_name, &path)
                    else {
                        continue;
                    };
                    let fs = self.host.fs();
                    let realpath: crate::autoimport::util::RealpathFn =
                        Arc::new(move |file_name: &RootedFilePath| {
                            tsc_tspath::rooted_file_path_from_path(
                                fs.realpath(&file_name.as_path()),
                            )
                        });
                    let extractor = self.new_export_extractor(
                        source.package_name.clone(),
                        ch.clone(),
                        module_resolver.clone(),
                        Some(realpath),
                    );
                    let file_exports = extractor.extract_from_file(source_file);
                    if let Some(index) = &br.bucket.index {
                        let mut index = index.borrow_mut();
                        for exp in file_exports {
                            index.insert_as_words(exp);
                        }
                    }
                }
            }
        }

        if second_pass_file_count > 0 {
            node_modules_logger.logf(format_args!(
                "{} files required second pass, took {:?}",
                second_pass_file_count,
                second_pass_start.elapsed()
            ));
        }
        node_modules_logger.logf(format_args!("Total: {:?}", discovery_start.elapsed()));
    }

    /// `buildProjectBucket`.
    fn build_project_bucket(
        &self,
        ctx: &Context,
        result: &mut BucketBuildResult,
        project_id: &ProjectId,
        program: &Rc<Program>,
        resolved_package_names: Option<Rc<Set<String>>>,
        logger: &LogTree,
    ) {
        if ctx.is_cancelled() {
            result.err = Some(Error::Message("context canceled".to_string()));
            return;
        }

        let start = Instant::now();
        let file_exclude_patterns = self
            .user_preferences
            .parsed_auto_import_file_exclude_patterns(self.host.fs().case_sensitivity());
        result.bucket = RegistryBucket::default();
        let mut resolver_options = self.resolver_options.clone();
        resolver_options.host = Arc::new(crate::autoimport::util::ResolutionHostImpl {
            fs: self.host.fs(),
            current_directory: self.current_directory.clone(),
        });
        resolver_options.compiler_options =
            Arc::new(tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS.clone());
        let module_resolver = Rc::new(DefaultResolver::new(resolver_options));
        let project_root_path = self
            .base_case_sensitivity
            .path_key(&program.base_directory().as_path());
        let symlink_cache = program.get_symlink_cache_opt();
        let checker_pool = CheckerPool::new(program.clone());
        let checker_count = checker_pool.created_count();
        let mut exports: FxHashMap<PathKey, Vec<Rc<Export>>> = FxHashMap::default();
        let mut skipped_file_count = 0;
        let mut combined_stats = crate::autoimport::extract::ExtractorStats::default();

        for file in program.source_files() {
            let (is_supplemental, is_ignored, is_excluded, skip_node_modules) = {
                let nodes = program.nodes(file.file_index());
                let sf = nodes[file].as_source_file();
                (
                    sf.is_content_mapper_supplemental(),
                    is_ignored_file(program, &nodes[file]),
                    file_exclude_patterns
                        .as_ref()
                        .is_some_and(|p| p.match_file_name(sf.file_name())),
                    sf.content_mapper().is_empty()
                        && (sf
                            .file_name()
                            .contains_lowercase_directory_sequence("/node_modules/")
                            || has_symlink_to_node_modules(
                                sf.path_key(),
                                &project_root_path,
                                symlink_cache,
                            )),
                )
            };
            if is_supplemental || is_ignored {
                continue;
            }
            if is_excluded {
                skipped_file_count += 1;
                continue;
            }
            // Ordinary node_modules files are owned by node_modules buckets.
            // Content-mapped files are not discovered by those buckets, but
            // files already transformed in the Program can be indexed here.
            if skip_node_modules {
                continue;
            }
            if ctx.is_cancelled() {
                continue;
            }
            let (checker, _done) = checker_pool.get_checker();
            let extractor =
                self.new_export_extractor(String::new(), checker, module_resolver.clone(), None);
            let file_exports = extractor.extract_from_file(file);
            exports.insert(
                {
                    let nodes = program.nodes(file.file_index());
                    nodes[file].as_source_file().path_key().clone()
                },
                file_exports,
            );
            combined_stats.add_from(extractor.stats());
        }

        let index_start = Instant::now();
        let mut idx = Index::default();
        let mut paths = FxHashMap::default();
        for (path, file_exports) in exports {
            paths.insert(path, String::new()); // Empty string for project buckets
            for exp in file_exports {
                idx.insert_as_words(exp);
            }
        }

        result.bucket.paths = Rc::new(paths);
        result.bucket.index = Some(Rc::new(RefCell::new(idx)));
        result.bucket.resolved_package_names = resolved_package_names;
        result.bucket.state.build_preferences =
            bucket_build_preferences_from_user_preferences(&self.user_preferences);

        logger.logf(format_args!(
            "Extracted exports: {:?} ({} exports, {} used checker, {} created checkers)",
            index_start - start,
            combined_stats.exports(),
            combined_stats.used_checker(),
            checker_count,
        ));
        if skipped_file_count > 0 {
            logger.logf(format_args!(
                "Skipped {} files due to exclude patterns",
                skipped_file_count
            ));
        }
        logger.logf(format_args!("Built index: {:?}", index_start.elapsed()));
        logger.logf(format_args!("Bucket total: {:?}", start.elapsed()));
    }

    /// `computeDependenciesForNodeModulesDirectory`.
    fn compute_dependencies_for_node_modules_directory(
        &self,
        change: &RegistryChange,
        all_resolved_package_names: &HashMap<ProjectId, Rc<Set<String>>>,
        _dir_name: &RootedDirectoryPath,
        dir_path: &PathKey,
    ) -> Option<Rc<Set<String>>> {
        // If any open files are in scope of this directory but not in scope of
        // any package.json, we need to add all packages in this node_modules
        // directory.
        for path in change.open_files.keys() {
            if dir_path.contains_path(path)
                && self
                    .get_nearest_ancestor_directory_with_package_json(path)
                    .is_none()
            {
                return None;
            }
        }

        // Get all package.jsons that have this node_modules directory in
        // their spine
        let mut dependencies = Set::new();
        self.directories.range(|entry| {
            if entry
                .value()
                .is_some_and(|d| d.package_json.as_ref().is_some_and(|pj| pj.exists()))
                && dir_path.contains_path(&entry.key())
            {
                if let Some(dir) = entry.value() {
                    if let Some(pj) = &dir.package_json {
                        if let Some(contents) = pj.get_contents() {
                            add_package_json_dependencies(&contents, &mut dependencies);
                        }
                    }
                }
            }
            true
        });

        // Add packages that are directly imported by programs but not listed
        // in package.json. This ensures node_modules files are always in
        // node_modules buckets. Include packages from all projects that have
        // this node_modules directory in their spine.
        for resolved_package_names in all_resolved_package_names.values() {
            for name in resolved_package_names.keys() {
                dependencies.add(name.clone());
            }
        }

        Some(Rc::new(dependencies))
    }

    /// `discoverBucketPackages` — resolves the package.json and realpath for
    /// each package name in a node_modules directory.
    fn discover_bucket_packages(
        &self,
        package_names: &Set<String>,
        dir_name: &RootedDirectoryPath,
        dir_path: &PathKey,
    ) -> Vec<Rc<DiscoveredPackage>> {
        let mut result = Vec::with_capacity(package_names.len());
        for package_name in package_names.keys() {
            let types_package_name = tsc_module::get_types_package_name(package_name);
            let package_json =
                self.host
                    .get_package_json(&dir_name.resolve_file(&tsc_tspath::combine_paths(
                        "node_modules",
                        &[package_name, "package.json"],
                    )));
            let mut types_package_json: Option<Arc<InfoCacheEntry>> = None;
            if *package_name != types_package_name {
                let types_json =
                    self.host
                        .get_package_json(&dir_name.resolve_file(&tsc_tspath::combine_paths(
                            "node_modules",
                            &[&types_package_name, "package.json"],
                        )));
                if types_json.directory_exists {
                    types_package_json = Some(types_json);
                }
            }
            let mut realpath = RootedDirectoryPath::default();
            if package_json.directory_exists {
                realpath = tsc_tspath::rooted_directory_path_from_path(
                    self.host
                        .fs()
                        .realpath(&package_json.package_directory.as_directory_path().as_path()),
                );
            }
            let mut types_realpath = RootedDirectoryPath::default();
            if let Some(types_package_json) = &types_package_json {
                types_realpath = tsc_tspath::rooted_directory_path_from_path(
                    self.host.fs().realpath(
                        &types_package_json
                            .package_directory
                            .as_directory_path()
                            .as_path(),
                    ),
                );
            }
            let case_sensitivity = self.host.fs().case_sensitivity();
            let is_local = !realpath.as_string().is_empty()
                && !realpath.contains_lowercase_directory_sequence("/node_modules/")
                && case_sensitivity
                    .path_key(&self.current_directory.as_path())
                    .contains_path(&case_sensitivity.path_key(&realpath.as_path()));
            result.push(Rc::new(DiscoveredPackage {
                package_name: package_name.clone(),
                package_json,
                realpath,
                types_package_json,
                types_realpath,
                dir_path: dir_path.clone(),
                is_local,
            }));
        }
        result
    }

    /// `extractPackage` — extracts exports from a single package.json. Runs
    /// once per unique realpath during the extraction phase. Returns `None`
    /// if the package has no extractable entrypoints.
    fn extract_package(
        &self,
        ctx: &Context,
        package_json: &Arc<InfoCacheEntry>,
        package_name: &str,
        project_reference_outputs: &FxHashMap<PathKey, RootedFilePath>,
        file_exclude_patterns: Option<&tsc_vfs::vfsmatch::SpecMatcher>,
        enable_directory_search: bool,
    ) -> Option<Rc<PerPackageExtractionResult>> {
        if !package_json.directory_exists {
            return None;
        }
        let (to_realpath, to_symlink) = get_package_realpath_funcs(
            &self.host.fs(),
            &package_json.package_directory.as_directory_path(),
        );
        let resolver = Rc::new(get_module_resolver(
            &self.host.fs(),
            &self.current_directory,
            to_realpath.clone(),
            self.resolver_options.clone(),
        ));
        let package_entrypoints = resolver.get_entrypoints_from_package_json_info(
            package_json,
            package_name,
            enable_directory_search,
        );
        if package_entrypoints.is_empty() {
            return None;
        }

        let mut package_entrypoints = package_entrypoints;
        let mut skipped_entrypoints = 0;
        if let Some(patterns) = file_exclude_patterns {
            let count = package_entrypoints.len();
            package_entrypoints.retain(|ep| !patterns.match_file_name(&ep.resolved_file_name));
            skipped_entrypoints = count - package_entrypoints.len();
        }
        if package_entrypoints.is_empty() {
            return None;
        }

        let result = Rc::new(PerPackageExtractionResult {
            package_files: RefCell::new(FxHashMap::default()),
            entrypoints: RefCell::new(package_entrypoints.iter().cloned().map(Rc::new).collect()),
            exports: RefCell::new(FxHashMap::default()),
            ambient_modules: RefCell::new(FxHashMap::default()),
            skipped_entrypoints,
            failed_ambient_module_lookup_sources: RefCell::new(HashMap::new()),
            failed_ambient_module_lookup_targets: RefCell::new(Set::new()),
            ..Default::default()
        });

        // Resolve entrypoint source files and build the alias resolver.
        let mut seen_files = Set::with_size_hint(package_entrypoints.len());
        let mut root_files: Vec<Option<(NodeId, Rc<ArenaCell>)>> =
            vec![None; package_entrypoints.len()];
        let mut symlinks: HashMap<PathKey, PathAndFileName> = HashMap::new();
        for (i, entrypoint) in package_entrypoints.iter().enumerate() {
            let mut file_name = entrypoint.symlink_or_realpath();
            let mut realpath_file_name = entrypoint.resolved_file_name.clone();
            let mut realpath_path = self
                .base_case_sensitivity
                .path_key(&realpath_file_name.as_path());

            if let Some(input_file_name) = project_reference_outputs.get(&realpath_path) {
                file_name = to_symlink(input_file_name);
                realpath_file_name = input_file_name.clone();
                realpath_path = self
                    .base_case_sensitivity
                    .path_key(&realpath_file_name.as_path());
            }

            if !seen_files.add_if_absent(realpath_path.clone()) {
                continue;
            }
            if file_name != realpath_file_name {
                let symlink_path = self.base_case_sensitivity.path_key(&file_name.as_path());
                symlinks.insert(
                    realpath_path.clone(),
                    PathAndFileName {
                        path: symlink_path,
                        file_name: file_name.clone(),
                    },
                );
                result.is_symlinked.set(true);
            }
            root_files[i] = self
                .host
                .get_source_file(&realpath_file_name, &realpath_path);
        }
        // Files that failed to resolve are skipped.
        let root_files: Vec<(NodeId, Rc<ArenaCell>)> =
            root_files.into_iter().flatten().collect();

        let result_ref = result.clone();
        let on_failed_ambient_module_lookup = Rc::new(
            move |source: &dyn tsc_ast::utilities::HasFileName, module_name: &str| {
                result_ref
                    .failed_ambient_module_lookup_targets
                    .borrow_mut()
                    .add(module_name.to_string());
                let mut sources = result_ref.failed_ambient_module_lookup_sources.borrow_mut();
                sources.entry(source.path_key().clone()).or_insert_with(|| {
                    FailedAmbientModuleLookupSource {
                        file_name: source.file_name().clone(),
                        package_name: String::new(),
                    }
                });
            },
        );

        let alias_resolver = new_alias_resolver(
            root_files,
            symlinks,
            self.host.clone(),
            resolver.clone(),
            Some(on_failed_ambient_module_lookup),
        );

        let ch = Rc::new(RefCell::new(
            tsc_checker::checker_core::Checker::new_checker(alias_resolver.clone(), None),
        ));
        let extractor = self.new_export_extractor(
            package_name.to_string(),
            ch,
            resolver.clone(),
            Some(to_realpath),
        );

        let mut non_module_files: Set<PathKey> = Set::new();
        for entrypoint in &alias_resolver.root_files {
            if ctx.is_cancelled() {
                return None;
            }
            let file_exports = extractor.extract_from_file(*entrypoint);
            let (ambient_names, entrypoint_file_name, entrypoint_path, external_indicator) = {
                let nodes = alias_resolver.nodes(entrypoint.file_index());
                let sf = nodes[*entrypoint].as_source_file();
                (
                    sf.ambient_module_names.to_vec(),
                    sf.file_name().clone(),
                    sf.path_key().clone(),
                    sf.external_module_indicator.is_some(),
                )
            };
            for name in ambient_names {
                result
                    .ambient_modules
                    .borrow_mut()
                    .entry(name)
                    .or_insert_with(Vec::new)
                    .push(entrypoint_file_name.clone());
            }
            result
                .package_files
                .borrow_mut()
                .insert(entrypoint_path.clone(), entrypoint_file_name);
            let symlink = alias_resolver.symlinks.get(&entrypoint_path);
            if let Some(symlink) = symlink {
                result
                    .package_files
                    .borrow_mut()
                    .insert(symlink.path.clone(), symlink.file_name.clone());
            }

            let mut has_exports = !file_exports.is_empty() && external_indicator;
            let mut sources = result.failed_ambient_module_lookup_sources.borrow_mut();
            if let Some(source) = sources.get_mut(&entrypoint_path) {
                source.package_name = package_name.to_string();
                has_exports = external_indicator;
            } else {
                drop(sources);
                result
                    .exports
                    .borrow_mut()
                    .insert(entrypoint_path.clone(), file_exports);
            }

            if !has_exports {
                non_module_files.add(entrypoint_path.clone());
                if let Some(symlink) = alias_resolver.symlinks.get(&entrypoint_path) {
                    non_module_files.add(symlink.path.clone());
                }
            }
        }

        // Discard entrypoints for non-module files and empty modules.
        result
            .entrypoints
            .borrow_mut()
            .retain(|ep| !non_module_files.has(&ep.resolved_path));

        result.stats_exports.set(extractor.stats().exports());
        result
            .stats_used_checker
            .set(extractor.stats().used_checker());
        Some(result)
    }

    /// `buildNodeModulesBucket`.
    fn build_node_modules_bucket(
        &self,
        ctx: &Context,
        result: &mut BucketBuildResult,
        dependencies: Option<&Rc<Set<String>>>,
        dir_path: &PathKey,
        discovered: &[Rc<DiscoveredPackage>],
        directory_package_names: Option<&Set<String>>,
        extraction_cache: &HashMap<RootedDirectoryPath, Rc<PerPackageExtractionResult>>,
        recursive_search_packages: Option<&Set<String>>,
        logger: &LogTree,
    ) {
        if ctx.is_cancelled() {
            result.err = Some(Error::Message("context canceled".to_string()));
            return;
        }

        let extraction = install_extractions(discovered, extraction_cache);

        let index_start = Instant::now();
        // Build PackageFiles with all directory package names; indexed
        // packages have non-nil maps, unindexed packages have nil maps.
        let mut all_package_files: FxHashMap<String, Option<FxHashMap<PathKey, RootedFilePath>>> =
            FxHashMap::default();
        if let Some(directory_package_names) = directory_package_names {
            for pkg_name in directory_package_names.keys() {
                all_package_files.insert(
                    pkg_name.clone(),
                    extraction.package_files.get(pkg_name).cloned().flatten(),
                );
            }
        }

        // Build Paths as reverse mapping from path to package name. Only
        // include paths for local workspace packages (eligible for granular
        // updates).
        let mut paths: FxHashMap<PathKey, String> = FxHashMap::default();
        for pkg_name in extraction.workspace_packages.keys() {
            if let Some(Some(files)) = extraction.package_files.get(pkg_name) {
                for path in files.keys() {
                    paths.insert(path.clone(), pkg_name.clone());
                }
            }
        }

        result.bucket = RegistryBucket {
            index: Some(Rc::new(RefCell::new(Index::default()))),
            dependency_names: dependencies.cloned(),
            package_files: Rc::new(all_package_files),
            ambient_module_names: Rc::new(extraction.ambient_module_names.clone()),
            paths: Rc::new(paths),
            state: BucketState {
                build_preferences: bucket_build_preferences_from_user_preferences(
                    &self.user_preferences,
                ),
                recursive_search_packages: recursive_search_packages.cloned(),
                ..Default::default()
            },
            ..Default::default()
        };
        result.entrypoints = FxHashMap::default();
        result.possible_failed_ambient_module_lookup_sources = extraction
            .possible_failed_ambient_module_lookup_sources
            .clone();
        result.possible_failed_ambient_module_lookup_targets = extraction
            .possible_failed_ambient_module_lookup_targets
            .clone();
        for file_exports in extraction.exports.values() {
            for exp in file_exports {
                if let Some(index) = &result.bucket.index {
                    index.borrow_mut().insert_as_words(exp.clone());
                }
            }
        }
        for entrypoint_set in &extraction.entrypoints {
            for entrypoint in entrypoint_set {
                result
                    .entrypoints
                    .entry(entrypoint.resolved_path.clone())
                    .or_insert_with(Vec::new)
                    .push(entrypoint.clone());
            }
        }

        // Compute old entrypoint paths to remove from the registry-level map.
        // For a full rebuild, all entrypoints belonging to the old bucket's
        // packages must be removed.
        if let Some(old_entry) = self.node_modules.get(dir_path) {
            if let Some(old_bucket) = old_entry.value() {
                for files in old_bucket.package_files.values() {
                    if let Some(files) = files {
                        for path in files.keys() {
                            if self.base_entrypoints.contains_key(path) {
                                result.removed_entrypoint_paths.push(path.clone());
                            }
                        }
                    }
                }
            }
        }

        logger.logf(format_args!(
            "Installed {} exports ({} used checker)",
            extraction.stats.exports(),
            extraction.stats.used_checker()
        ));
        if extraction.skipped_entrypoints_count > 0 {
            logger.logf(format_args!(
                "Skipped {} entrypoints due to exclude patterns",
                extraction.skipped_entrypoints_count
            ));
        }
        logger.logf(format_args!("Built index: {:?}", index_start.elapsed()));

        if ctx.is_cancelled() {
            result.err = Some(Error::Message("context canceled".to_string()));
        }
    }

    /// `updateNodeModulesBucket` performs a granular update of the
    /// node_modules bucket, re-extracting only the dirty packages and merging
    /// with the existing bucket.
    fn update_node_modules_bucket(
        &self,
        ctx: &Context,
        result: &mut BucketBuildResult,
        existing_bucket: &Rc<RegistryBucket>,
        dirty_packages: Option<&Set<String>>,
        discovered: &[Rc<DiscoveredPackage>],
        extraction_cache: &HashMap<RootedDirectoryPath, Rc<PerPackageExtractionResult>>,
        recursive_search_packages: Option<&Set<String>>,
        logger: &LogTree,
    ) {
        if ctx.is_cancelled() {
            result.err = Some(Error::Message("context canceled".to_string()));
            return;
        }

        let start = Instant::now();
        let extraction = install_extractions(discovered, extraction_cache);

        let index_start = Instant::now();
        let dirty_packages_set = dirty_packages.cloned().unwrap_or_default();

        // Clone the existing index, excluding exports from dirty packages
        let mut new_index = existing_bucket
            .index
            .as_ref()
            .and_then(|i| {
                i.borrow()
                    .clone_filtered(|exp| !dirty_packages_set.has(&exp.package_name))
            })
            .unwrap_or_default();

        // Clone PackageFiles, removing dirty packages
        let mut new_package_files = (*existing_bucket.package_files).clone();
        for pkg_name in dirty_packages_set.keys() {
            new_package_files.remove(pkg_name);
        }
        // Add newly extracted package files
        for (k, v) in &extraction.package_files {
            new_package_files.insert(k.clone(), v.clone());
        }

        // Clone Paths, removing dirty package paths
        let mut new_paths: FxHashMap<PathKey, String> = FxHashMap::default();
        for (path, pkg_name) in existing_bucket.paths.iter() {
            if dirty_packages_set.has(pkg_name) {
                continue;
            }
            new_paths.insert(path.clone(), pkg_name.clone());
        }
        // Add paths for newly extracted workspace packages
        for pkg_name in extraction.workspace_packages.keys() {
            if let Some(Some(files)) = extraction.package_files.get(pkg_name) {
                for path in files.keys() {
                    new_paths.insert(path.clone(), pkg_name.clone());
                }
            }
        }

        // Clone AmbientModuleNames, removing dirty package entries
        let mut new_ambient_module_names: FxHashMap<String, Vec<RootedFilePath>> =
            FxHashMap::default();
        for (module_name, file_names) in existing_bucket.ambient_module_names.iter() {
            // Filter out files from dirty packages
            let mut filtered: Vec<RootedFilePath> = Vec::new();
            for file_name in file_names {
                let path = self.base_case_sensitivity.path_key(&file_name.as_path());
                if let Some(pkg_name) = existing_bucket.paths.get(&path) {
                    if dirty_packages_set.has(pkg_name) {
                        continue;
                    }
                }
                filtered.push(file_name.clone());
            }
            if !filtered.is_empty() {
                new_ambient_module_names.insert(module_name.clone(), filtered);
            }
        }
        // Add newly extracted ambient module names
        for (module_name, file_names) in &extraction.ambient_module_names {
            new_ambient_module_names
                .entry(module_name.clone())
                .or_insert_with(Vec::new)
                .extend(file_names.iter().cloned());
        }

        // Collect entrypoint paths that need to be removed from the
        // registry-level map (paths belonging to dirty packages)
        let mut removed_entrypoint_paths: Vec<PathKey> = Vec::new();
        for path in self.base_entrypoints.keys() {
            if let Some(pkg_name) = existing_bucket.paths.get(path) {
                if dirty_packages_set.has(pkg_name) {
                    removed_entrypoint_paths.push(path.clone());
                }
            }
        }
        // Build new entrypoints from extraction
        let mut new_entrypoints: FxHashMap<PathKey, Vec<Rc<ResolvedEntrypoint>>> =
            FxHashMap::default();
        for entrypoint_set in &extraction.entrypoints {
            for entrypoint in entrypoint_set {
                new_entrypoints
                    .entry(entrypoint.resolved_path.clone())
                    .or_insert_with(Vec::new)
                    .push(entrypoint.clone());
            }
        }

        // Insert newly extracted exports into the index
        for file_exports in extraction.exports.values() {
            for exp in file_exports {
                new_index.insert_as_words(exp.clone());
            }
        }

        result.bucket = RegistryBucket {
            index: Some(Rc::new(RefCell::new(new_index))),
            dependency_names: existing_bucket.dependency_names.clone(),
            package_files: Rc::new(new_package_files),
            ambient_module_names: Rc::new(new_ambient_module_names),
            paths: Rc::new(new_paths),
            state: BucketState {
                build_preferences: bucket_build_preferences_from_user_preferences(
                    &self.user_preferences,
                ),
                recursive_search_packages: recursive_search_packages.cloned(),
                ..Default::default()
            },
            ..Default::default()
        };
        result.entrypoints = new_entrypoints;
        result.removed_entrypoint_paths = removed_entrypoint_paths;
        result.possible_failed_ambient_module_lookup_sources = extraction
            .possible_failed_ambient_module_lookup_sources
            .clone();
        result.possible_failed_ambient_module_lookup_targets = extraction
            .possible_failed_ambient_module_lookup_targets
            .clone();

        logger.logf(format_args!(
            "Granular update of {} packages: {:?} ({} exports)",
            dirty_packages_set.len(),
            index_start - start,
            extraction.stats.exports()
        ));
        logger.logf(format_args!("Built index: {:?}", index_start.elapsed()));

        if ctx.is_cancelled() {
            result.err = Some(Error::Message("context canceled".to_string()));
        }
    }

    /// `getNearestAncestorDirectoryWithPackageJson`.
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        file_path: &PathKey,
    ) -> Option<Directory> {
        file_path.parent().for_each_ancestor_directory(|dir_path| {
            if let Some(dir_entry) = self.directories.get(dir_path) {
                let dir = dir_entry.value().unwrap_or_default();
                if dir.package_json.as_ref().is_some_and(|pj| pj.exists()) {
                    return (dir, true);
                }
            }
            (Directory::default(), false)
        })
    }

    /// `resolveAmbientModuleName`.
    fn resolve_ambient_module_name(
        &self,
        module_name: &str,
        from_path: &PathKey,
    ) -> Vec<RootedFilePath> {
        from_path
            .for_each_ancestor_directory(|dir_path| {
                if let Some(bucket) = self.node_modules.get(dir_path) {
                    if let Some(bucket) = bucket.value() {
                        if let Some(file_names) = bucket.ambient_module_names.get(module_name) {
                            return (file_names.clone(), true);
                        }
                    }
                }
                (Vec::new(), false)
            })
            .unwrap_or_default()
    }
}

/// `hasNewNonNodeModulesFiles`.
fn has_new_non_node_modules_files(program: &Program, bucket: &RegistryBucket) -> bool {
    if bucket.state.new_program_structure != NewProgramStructure::DifferentFileNames {
        return false;
    }
    for file in program.source_files() {
        let nodes = program.nodes(file.file_index());
        let sf = nodes[file].as_source_file();
        if sf.is_content_mapper_supplemental()
            || sf
                .file_name()
                .contains_lowercase_directory_sequence("/node_modules/")
            || is_ignored_file(program, &nodes[file])
        {
            continue;
        }
        if !bucket.paths.contains_key(sf.path_key()) {
            return true;
        }
    }
    false
}

/// `isIgnoredFile`.
fn is_ignored_file(program: &Program, file: &ast::Node) -> bool {
    let sf = file.as_source_file();
    program.is_source_file_default_library(sf.path_key())
        || program.is_global_typings_file(sf.file_name())
}

/// `hasSymlinkToNodeModules` checks if a file's realpath has a symlink that
/// points to a node_modules directory. This is used to skip files in the
/// project bucket that would be duplicated by the node_modules bucket via
/// their symlink.
fn has_symlink_to_node_modules(
    file_path: &PathKey,
    project_root_path: &PathKey,
    symlink_cache: Option<&KnownSymlinks>,
) -> bool {
    let Some(symlink_cache) = symlink_cache else {
        return false;
    };
    // Keep files inside this project indexed in project buckets even if they
    // are reachable through a node_modules symlink from elsewhere.
    if project_root_path.contains_path(file_path) {
        return false;
    }

    // First check if the file itself has a symlink to node_modules
    let files_by_realpath = symlink_cache.files_by_realpath();
    if let Some(symlink_paths) = files_by_realpath.load(file_path) {
        let mut found = false;
        symlink_paths.range(|symlink_path| {
            if symlink_path.contains_lowercase_directory_sequence("/node_modules/") {
                found = true;
                return false; // stop ranging
            }
            true
        });
        if found {
            return true;
        }
    }

    // Fall back to checking ancestor directories
    let directories_by_realpath = symlink_cache.directories_by_realpath();
    let mut found = false;
    file_path.for_each_ancestor_directory(|dir_path| {
        let Some(symlink_paths) = directories_by_realpath.load(dir_path) else {
            return ((), false);
        };
        // Check if any of the symlinks point to a node_modules directory
        symlink_paths.range(|symlink_path| {
            if symlink_path.contains_lowercase_directory_sequence("/node_modules/") {
                found = true;
                return false; // stop ranging
            }
            true
        });
        ((), found) // stop if we found a match
    });
    found
}

/// `type failedAmbientModuleLookupSource struct`.
#[derive(Clone)]
pub(crate) struct FailedAmbientModuleLookupSource {
    pub file_name: RootedFilePath,
    pub package_name: String,
}

/// `type bucketBuildResult struct`.
#[derive(Default)]
struct BucketBuildResult {
    /// `replaceBucket` — installs the built bucket (a `dirty.MapEntry::
    /// replace` bound to its entry, matching Go's `replaceBucket func`).
    replace_bucket: Option<Box<dyn Fn(RegistryBucket)>>,
    resolution_path: PathKey,
    err: Option<Error>,

    bucket: RegistryBucket,
    /// `entrypoints` — the resolved entrypoints from this bucket's packages,
    /// to be merged into the registry-level entrypoints map.
    entrypoints: FxHashMap<PathKey, Vec<Rc<ResolvedEntrypoint>>>,
    /// `removedEntrypointPaths` lists paths whose entrypoints should be
    /// removed from the registry-level map before merging new entrypoints.
    /// Used for granular updates.
    removed_entrypoint_paths: Vec<PathKey>,
    /// `possibleFailedAmbientModuleLookupSources` — file path → filename and
    /// package name.
    possible_failed_ambient_module_lookup_sources:
        Option<Rc<SyncMap<PathKey, FailedAmbientModuleLookupSource>>>,
    /// `possibleFailedAmbientModuleLookupTargets` — likely ambient module
    /// names.
    possible_failed_ambient_module_lookup_targets: Option<Rc<SyncSet<String>>>,
}

/// `type discoveredPackage struct` — a package found during the discovery
/// phase, holding the resolved package.json and realpath for deduplication.
/// When both a real package and a corresponding @types package exist (e.g.
/// react + @types/react), both are stored so extraction can fall back to the
/// @types package if the real package has no TypeScript entrypoints.
pub(crate) struct DiscoveredPackage {
    pub package_name: String,
    pub package_json: Arc<InfoCacheEntry>,
    pub realpath: RootedDirectoryPath,
    pub types_package_json: Option<Arc<InfoCacheEntry>>,
    pub types_realpath: RootedDirectoryPath,
    /// `dirPath` — bucket directory path (used as extraction context).
    #[allow(dead_code)]
    pub dir_path: PathKey,
    /// `isLocal` — true if realpath is within the workspace root.
    pub is_local: bool,
}

/// `type perPackageExtractionResult struct` — the extraction output for one
/// physical package. Interior-mutable so the alias-resolver callback can
/// record failures through a shared `Rc`.
#[derive(Default)]
pub(crate) struct PerPackageExtractionResult {
    pub package_files: RefCell<FxHashMap<PathKey, RootedFilePath>>,
    pub entrypoints: RefCell<Vec<Rc<ResolvedEntrypoint>>>,
    pub exports: RefCell<FxHashMap<PathKey, Vec<Rc<Export>>>>,
    pub ambient_modules: RefCell<FxHashMap<String, Vec<RootedFilePath>>>,
    pub stats_exports: std::cell::Cell<i32>,
    pub stats_used_checker: std::cell::Cell<i32>,
    pub skipped_entrypoints: usize,
    pub is_symlinked: std::cell::Cell<bool>,
    pub failed_ambient_module_lookup_sources:
        RefCell<HashMap<PathKey, FailedAmbientModuleLookupSource>>,
    pub failed_ambient_module_lookup_targets: RefCell<Set<String>>,
}

/// `type packageExtractionResult struct` — aggregated extraction results for
/// one bucket.
#[derive(Default)]
pub(crate) struct PackageExtractionResult {
    pub exports: FxHashMap<PathKey, Vec<Rc<Export>>>,
    pub package_files: FxHashMap<String, Option<FxHashMap<PathKey, RootedFilePath>>>,
    pub ambient_module_names: FxHashMap<String, Vec<RootedFilePath>>,
    pub entrypoints: Vec<Vec<Rc<ResolvedEntrypoint>>>,
    pub workspace_packages: Set<String>,
    pub possible_failed_ambient_module_lookup_sources:
        Option<Rc<SyncMap<PathKey, FailedAmbientModuleLookupSource>>>,
    pub possible_failed_ambient_module_lookup_targets: Option<Rc<SyncSet<String>>>,
    pub stats: crate::autoimport::extract::ExtractorStats,
    pub skipped_entrypoints_count: usize,
}

/// `installExtractions` aggregates pre-extracted per-package results into a
/// single `PackageExtractionResult` for one bucket.
fn install_extractions(
    discovered: &[Rc<DiscoveredPackage>],
    extraction_cache: &HashMap<RootedDirectoryPath, Rc<PerPackageExtractionResult>>,
) -> PackageExtractionResult {
    let mut result = PackageExtractionResult {
        possible_failed_ambient_module_lookup_sources: Some(Rc::new(SyncMap::new())),
        possible_failed_ambient_module_lookup_targets: Some(Rc::new(SyncSet::new())),
        ..Default::default()
    };

    for pkg in discovered {
        let extraction = extraction_cache
            .get(&pkg.realpath)
            .or_else(|| extraction_cache.get(&pkg.types_realpath));
        let Some(extraction) = extraction else {
            continue;
        };
        for (k, v) in extraction.exports.borrow().iter() {
            result.exports.insert(k.clone(), v.clone());
        }
        let files_map = result
            .package_files
            .entry(pkg.package_name.clone())
            .or_insert_with(|| Some(FxHashMap::default()));
        let files_map = files_map.get_or_insert_with(FxHashMap::default);
        for (k, v) in extraction.package_files.borrow().iter() {
            files_map.insert(k.clone(), v.clone());
        }
        for (name, file_names) in extraction.ambient_modules.borrow().iter() {
            result
                .ambient_module_names
                .entry(name.clone())
                .or_insert_with(Vec::new)
                .extend(file_names.iter().cloned());
        }
        result
            .entrypoints
            .push(extraction.entrypoints.borrow().clone());
        for (path, source) in extraction
            .failed_ambient_module_lookup_sources
            .borrow()
            .iter()
        {
            result
                .possible_failed_ambient_module_lookup_sources
                .as_ref()
                .unwrap()
                .load_or_store(
                    path.clone(),
                    FailedAmbientModuleLookupSource {
                        file_name: source.file_name.clone(),
                        package_name: source.package_name.clone(),
                    },
                );
        }
        for target in extraction
            .failed_ambient_module_lookup_targets
            .borrow()
            .keys()
        {
            result
                .possible_failed_ambient_module_lookup_targets
                .as_ref()
                .unwrap()
                .add(target.clone());
        }
        if extraction.is_symlinked.get() && pkg.is_local {
            result.workspace_packages.add(pkg.package_name.clone());
        }
        result.stats.add_from_counts(
            extraction.stats_exports.get(),
            extraction.stats_used_checker.get(),
        );
        result.skipped_entrypoints_count += extraction.skipped_entrypoints;
    }

    result
}
