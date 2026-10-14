// Ported from tsc/internal/project/autoimport.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The registry machinery itself lives in `tsc_ls::autoimport`; this module
// provides the snapshot-side clone host (`autoImportRegistryCloneHost`)
// and the builder filesystem (`autoImportBuilderFS`).

use std::rc::Rc;
use std::sync::{Arc, Mutex};

use tsc_ast::ArenaCell;
use tsc_collections::SyncMap;
use tsc_ls::autoimport::registry::{ProjectId, RegistryCloneHost};
use tsc_packagejson::{InfoCacheEntry, PackageDirectory, PackageJson};
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::overlayfs::{FileHandle, FileHandleSource};
use crate::parsecache::{ParseCache, ParseCacheKey, new_parse_cache_key};
use crate::project::Id;
use crate::projectcollection::ProjectCollection;
use crate::snapshotfs::{FileSource, SourceFs, SnapshotFsBuilder, new_source_fs};

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
    ///
    /// PORT: `autoimport.ProjectID` is `ls::autoimport::ProjectId` — an
    /// `Rc<str>` keyed by the project's `Id` string (Go's `fmt.Stringer`).
    fn get_default_project(
        &self,
        path: &PathKey,
    ) -> Option<(ProjectId, Rc<tsc_compiler::program::Program>)> {
        let project = self.project_collection.get_default_project(path)?;
        let program = project.get_program()?.clone();
        Some((ProjectId(Rc::from(project.id.as_str())), program))
    }

    /// `GetPackageJson` — never nil in Go's implementation.
    ///
    /// !!! ref-counted shared cache — see the Go note; the package-json
    /// info cache is created per call here as in Go.
    fn get_package_json(&self, file_name: &RootedFilePath) -> Arc<InfoCacheEntry> {
        let fh = self.fs.get_file(file_name);
        let package_directory = file_name.directory();
        let cache_package_directory =
            PackageDirectory::new(package_directory.clone(), self.fs.case_sensitivity());
        let Some(fh) = fh else {
            return Arc::new(InfoCacheEntry {
                directory_exists: self.fs.directory_exists(&package_directory),
                package_directory: cache_package_directory,
                contents: None,
            });
        };
        match tsc_packagejson::parse(fh.content().as_bytes()) {
            Err(_) => {
                // `version_state` is private, so `PackageJson` can't be
                // built with a literal — default then set the public fields.
                let mut contents = PackageJson::default();
                contents.parseable = false;
                Arc::new(InfoCacheEntry {
                    directory_exists: true,
                    package_directory: cache_package_directory,
                    contents: Some(Arc::new(contents)),
                })
            }
            Ok(fields) => {
                let mut contents = PackageJson::default();
                contents.fields = fields;
                contents.parseable = true;
                Arc::new(InfoCacheEntry {
                    directory_exists: true,
                    package_directory: cache_package_directory,
                    contents: Some(Arc::new(contents)),
                })
            }
        }
    }

    /// `GetProgramForProject` — `ProjectId` is keyed by `Id`'s string form.
    fn get_program_for_project(
        &self,
        project_id: &ProjectId,
    ) -> Option<Rc<tsc_compiler::program::Program>> {
        let project = self
            .project_collection
            .get_project(&Id::from(project_id.0.as_ref()))?;
        project.get_program().cloned()
    }

    /// `GetSourceFile` — returns the file's root `NodeId` plus an
    /// [`ArenaCell`] aliasing the parse-cache arena (Go shares the
    /// `*ast.SourceFile`); `None` mirrors Go's nil `*ast.SourceFile`.
    fn get_source_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<(tsc_ast::NodeId, Rc<ArenaCell>)> {
        let fh = self.fs.get_file(file_name)?;
        let opts = tsc_ast::parseoptions::SourceFileParseOptions {
            file_name: fh.file_name().clone(),
            path_key: path.clone(),
            ..Default::default()
        };
        let key = new_parse_cache_key(opts, fh.hash(), fh.kind());
        let result = self.parse_cache.acquire(key.clone(), &fh);
        self.files.lock().unwrap().push(key);
        let parsed = result.lock().unwrap();
        Some((
            parsed.file,
            Rc::new(ArenaCell::from_shared(parsed.nodes.clone())),
        ))
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
