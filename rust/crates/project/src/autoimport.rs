// Ported from tsc/internal/project/autoimport.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(blocked): `ls/autoimport` (the `Registry`/`RegistryCloneHost`/
// `ProjectID` types this file plugs into) lives in the sibling `tsc-ls`
// crate, which does not yet compile — see the disabled dependency in
// Cargo.toml. `AutoImportRegistry`, `RegistryChange`, and
// `RegistryCloneHost` below are local stand-ins with the Go signatures;
// rewire them to `tsc_ls::autoimport` when it lands.
// The filesystem plumbing (`AutoImportBuilderFs`,
// `AutoImportRegistryCloneHost`) IS fully ported.

use std::rc::Rc;
use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;
use tsc_collections::{Set, SyncMap};
use tsc_lsproto::DocumentUri;
use tsc_lsutil::UserPreferences;
use tsc_packagejson::{InfoCacheEntry, PackageDirectory, PackageJson};
use tsc_project_logging::LogTree;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::overlayfs::{FileHandle, FileHandleSource};
use crate::parsecache::{ParseCache, ParseCacheKey, new_parse_cache_key};
use crate::project::Id;
use crate::projectcollection::ProjectCollection;
use crate::snapshotfs::{FileSource, SourceFs, SnapshotFsBuilder, new_source_fs};

/// `autoimport.ProjectID` — Go `interface{ ... }` implemented by `ID`.
pub type ProjectId = Id;

/// `autoimport.RegistryChange`.
#[derive(Default)]
pub struct RegistryChange {
    pub requested_file: PathKey,
    pub requested_file_name: RootedFilePath,
    pub open_files: FxHashMap<PathKey, RootedFilePath>,
    pub changed: Set<DocumentUri>,
    pub created: Set<DocumentUri>,
    pub deleted: Set<DocumentUri>,
    /// `RebuiltPrograms` maps from project ID to:
    ///   - `true`: the program was rebuilt with a different set of file names
    ///   - `false`: the program was rebuilt but the set of file names is
    ///     unchanged
    pub rebuilt_programs: FxHashMap<ProjectId, bool>,
    pub user_preferences: Option<UserPreferences>,
}

/// `autoimport.Registry` — the auto-import completion index carried by
/// snapshots.
///
/// PORT(blocked): this is a field-shell stand-in — `clone` preserves the
/// registry's tracked inputs (case sensitivity, preferences, node_modules
/// watch roots) but does NOT run the real indexing pipeline from
// `ls/autoimport/registry.go` until `tsc-ls` compiles.
pub struct AutoImportRegistry {
    case_sensitivity: CaseSensitivity,
    user_preferences: UserPreferences,
    node_modules_directories: FxHashMap<PathKey, RootedDirectoryPath>,
}

/// `autoimport.NewRegistry`.
pub fn new_registry(
    case_sensitivity: CaseSensitivity,
    preferences: UserPreferences,
) -> Arc<AutoImportRegistry> {
    Arc::new(AutoImportRegistry {
        case_sensitivity,
        user_preferences: preferences,
        node_modules_directories: FxHashMap::default(),
    })
}

/// `RegistryError` — Go `error` from `Registry.Clone`.
pub type RegistryError = Box<dyn std::error::Error + Send + Sync>;

impl AutoImportRegistry {
    /// `r.NodeModulesDirectories()`.
    pub fn node_modules_directories(&self) -> FxHashMap<PathKey, RootedDirectoryPath> {
        self.node_modules_directories.clone()
    }

    /// `r.Clone`.
    ///
    /// PORT(blocked): preserves tracked state verbatim; the real
    /// `registryBuilder` pipeline (watched packages, exports index,
    // per-project program diffs) is pending the `tsc-ls` autoimport port.
    pub fn clone_registry(
        &self,
        _ctx: &tsc_core::context::Context,
        change: RegistryChange,
        _host: &dyn RegistryCloneHost,
        _current_directory: &RootedDirectoryPath,
        _logger: &LogTree,
    ) -> Result<Arc<AutoImportRegistry>, RegistryError> {
        Ok(Arc::new(AutoImportRegistry {
            case_sensitivity: self.case_sensitivity,
            user_preferences: change
                .user_preferences
                .unwrap_or_else(|| self.user_preferences.clone()),
            node_modules_directories: self.node_modules_directories.clone(),
        }))
    }
}

/// `autoimport.RegistryCloneHost` — the snapshot-side view the registry
/// reads through while cloning.
///
/// PORT(blocked): local stand-in for the `tsc-ls` trait — `get_source_file`
/// returns the parse-cache lease value (`Arc<Mutex<ParsedSourceFile>>`)
// standing in for Go's `*ast.SourceFile`.
pub trait RegistryCloneHost {
    /// `FS()`.
    fn fs(&self) -> Arc<dyn Vfs>;
    /// `GetDefaultProject` — `None` is Go's `(nil, nil)`.
    fn get_default_project(
        &self,
        path: &PathKey,
    ) -> Option<(ProjectId, Rc<tsc_compiler::program::Program>)>;
    /// `GetProgramForProject`.
    fn get_program_for_project(
        &self,
        project_id: &ProjectId,
    ) -> Option<Rc<tsc_compiler::program::Program>>;
    /// `GetPackageJson`.
    fn get_package_json(&self, file_name: &RootedFilePath) -> InfoCacheEntry;
    /// `GetSourceFile`.
    fn get_source_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<Mutex<tsc_contentmapper::ParsedSourceFile>>>;
    /// `Dispose`.
    fn dispose(&self);
}

/// `autoImportBuilderFS` — a `FileSource` over the snapshot-FS builder that
/// avoids long-term caching of files referenced only by auto-imports.
///
/// (Note the reason we can't just use the finalized `SnapshotFS` is that
/// changed files not read during other parts of the snapshot clone will be
/// marked as dirty, but not yet refreshed from the source filesystem.)
pub struct AutoImportBuilderFs {
    snapshot_fs_builder: Arc<SnapshotFsBuilder>,
    /// `untrackedFiles` — files read only by the auto-import indexer, kept
    /// out of the builder's `cacheFiles`.
    untracked_files: SyncMap<PathKey, Option<Arc<dyn FileHandle>>>,
}

impl AutoImportBuilderFs {
    /// `&autoImportBuilderFS{snapshotFSBuilder}`.
    pub fn new(snapshot_fs_builder: Arc<SnapshotFsBuilder>) -> Self {
        AutoImportBuilderFs {
            snapshot_fs_builder,
            untracked_files: SyncMap::new(),
        }
    }
}

/// `var _ FileSource = (*autoImportBuilderFS)(nil)`
impl FileSource for AutoImportBuilderFs {
    /// `FS`.
    fn fs(&self) -> Arc<dyn Vfs> {
        self.snapshot_fs_builder.fs_vfs()
    }

    /// `GetFile`.
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        let path = self
            .snapshot_fs_builder
            .case_sensitivity
            .path_key(&file_name.as_path());
        self.get_file_by_path(file_name, &path)
    }

    /// `GetFileByPath` — reuse files already tracked by the builder's cache,
    /// but keep auto-import-only reads in `untracked_files` so they aren't
    /// retained by the finalized snapshot.
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        if let Some(cached_file) = self.snapshot_fs_builder.cache_files.load(path) {
            return self.snapshot_fs_builder.reload_entry_if_needed(&cached_file);
        }
        if let Some(fh) = self.untracked_files.load(path) {
            return fh;
        }
        let fh = self.snapshot_fs_builder.fs.get_file_by_path(file_name, path);
        self.untracked_files.load_or_store(path.clone(), fh).0
    }

    /// `FileExists`.
    fn file_exists(&self, file_name: &RootedFilePath, path: &PathKey) -> bool {
        self.snapshot_fs_builder.file_exists(file_name, path)
    }

    /// `GetAccessibleEntries`.
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> tsc_vfs::Entries {
        self.snapshot_fs_builder.get_accessible_entries(path)
    }
}

/// `autoImportRegistryCloneHost`.
pub struct AutoImportRegistryCloneHost {
    project_collection: Rc<ProjectCollection>,
    parse_cache: Rc<ParseCache>,
    /// `fs` — `newSourceFS(false, &autoImportBuilderFS{...})`.
    fs: Arc<SourceFs>,

    /// `filesMu`/`files` — parse-cache keys acquired through
    /// `get_source_file`, released by `dispose`.
    files: Mutex<Vec<ParseCacheKey>>,
}

/// `newAutoImportRegistryCloneHost`.
pub fn new_auto_import_registry_clone_host(
    project_collection: Rc<ProjectCollection>,
    parse_cache: Rc<ParseCache>,
    snapshot_fs_builder: Arc<SnapshotFsBuilder>,
) -> AutoImportRegistryCloneHost {
    AutoImportRegistryCloneHost {
        project_collection,
        parse_cache,
        fs: Arc::new(new_source_fs(
            false,
            Arc::new(AutoImportBuilderFs::new(snapshot_fs_builder)),
        )),
        files: Mutex::new(Vec::new()),
    }
}

/// `var _ autoimport.RegistryCloneHost = (*autoImportRegistryCloneHost)(nil)`
impl RegistryCloneHost for AutoImportRegistryCloneHost {
    /// `FS`.
    fn fs(&self) -> Arc<dyn Vfs> {
        self.fs.clone()
    }

    /// `GetDefaultProject`.
    fn get_default_project(
        &self,
        path: &PathKey,
    ) -> Option<(ProjectId, Rc<tsc_compiler::program::Program>)> {
        let project = self.project_collection.get_default_project(path)?;
        let program = project.get_program()?.clone();
        Some((project.id.clone(), program))
    }

    /// `GetPackageJson`.
    ///
    /// !!! ref-counted shared cache — see the Go note; the package-json
    /// info cache is created per call here as in Go.
    fn get_package_json(&self, file_name: &RootedFilePath) -> InfoCacheEntry {
        let fh = self.fs.get_file(file_name);
        let package_directory = file_name.directory();
        let cache_package_directory =
            PackageDirectory::new(package_directory.clone(), self.fs.case_sensitivity());
        let Some(fh) = fh else {
            return InfoCacheEntry {
                directory_exists: self.fs.directory_exists(&package_directory),
                package_directory: cache_package_directory,
                contents: None,
            };
        };
        match tsc_packagejson::parse(fh.content().as_bytes()) {
            Err(_) => {
                // `version_state` is private, so `PackageJson` can't be
                // built with a literal — default then set the public fields.
                let mut contents = PackageJson::default();
                contents.parseable = false;
                InfoCacheEntry {
                    directory_exists: true,
                    package_directory: cache_package_directory,
                    contents: Some(Arc::new(contents)),
                }
            }
            Ok(fields) => {
                let mut contents = PackageJson::default();
                contents.fields = fields;
                contents.parseable = true;
                InfoCacheEntry {
                    directory_exists: true,
                    package_directory: cache_package_directory,
                    contents: Some(Arc::new(contents)),
                }
            }
        }
    }

    /// `GetProgramForProject` — Go panics on a non-`ID` ProjectID; our
    /// `ProjectId` IS `Id`, so the assertion is free.
    fn get_program_for_project(
        &self,
        project_id: &ProjectId,
    ) -> Option<Rc<tsc_compiler::program::Program>> {
        let project = self.project_collection.get_project(project_id)?;
        project.get_program().cloned()
    }

    /// `GetSourceFile`.
    fn get_source_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<Mutex<tsc_contentmapper::ParsedSourceFile>>> {
        let fh = self.fs.get_file(file_name)?;
        let opts = tsc_ast::parseoptions::SourceFileParseOptions {
            file_name: fh.file_name().clone(),
            path_key: path.clone(),
            ..Default::default()
        };
        let key = new_parse_cache_key(opts, fh.hash(), fh.kind());
        let result = self.parse_cache.acquire(key.clone(), &fh);
        self.files.lock().unwrap().push(key);
        Some(result)
    }

    /// `Dispose` — releases the parse-cache references acquired through
    /// `get_source_file`.
    fn dispose(&self) {
        let mut files = self.files.lock().unwrap();
        for key in files.drain(..) {
            self.parse_cache.deref(&key);
        }
    }
}
