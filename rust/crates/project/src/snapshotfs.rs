// Ported from tsc/internal/project/snapshotfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::any::Any;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock, RwLock};
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_collections::{Set, SyncMap, SyncSet};
use tsc_dirty::{self, Cloneable, FinalizationHooks, SyncMapEntry, Value};
use tsc_lsconv;
use tsc_lsproto::DocumentUri;
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath,
};
use tsc_vfs::fs::{FileInfo, FsError};
use tsc_vfs::{Entries, Vfs};

use crate::filechange::FileChangeSummary;
use crate::overlayfs::{
    CachedFile, FileContent, FileHandle, FileHandleSource, LayeredFileSystem, layered_as_vfs,
    new_cached_file,
};
use crate::parsecache::hash_string_128;

/// `FileSource`.
///
/// PORT: `Send + Sync` is required because `SourceFs` stores `Arc<dyn
/// FileSource>` behind `Vfs`'s `Send + Sync` bound. Go's
/// `snapshotFSBuilder` state is unsynchronized (`dirty.Map`), but the port
/// uses `dirty.SyncMap` + a `Mutex`-backed directory map so the builder can
/// satisfy the bound.
pub trait FileSource: Send + Sync {
    fn fs(&self) -> Arc<dyn Vfs>;
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>>;
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>>;
    fn file_exists(&self, file_name: &RootedFilePath, path: &PathKey) -> bool;
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries;
}

/// `cachedLayeredFileSystem` — a `cachedvfs` read-query cache layered over a
/// `LayeredFileSystem`.
pub struct CachedLayeredFileSystem {
    fs: Arc<tsc_vfs::cachedvfs::Fs>,
    layered: Arc<dyn LayeredFileSystem>,
}

/// `newCachedLayeredFileSystem`.
pub fn new_cached_layered_file_system(
    file_system: Arc<dyn LayeredFileSystem>,
) -> Arc<dyn LayeredFileSystem> {
    Arc::new(CachedLayeredFileSystem {
        fs: tsc_vfs::cachedvfs::from(layered_as_vfs(file_system.clone())),
        layered: file_system,
    })
}


/// `dirty.CloneableMap[tspath.PathKey, string]` — Send + Sync variant.
///
/// PORT: `CloneableMap` in `tsc_dirty` is `Rc`-backed and cannot be `Send`.
/// Go's cloneable map shares its backing table on assignment and
/// deep-copies on `Clone()`; `Arc<Mutex<…>>` preserves the
/// mutate-through-shared-handle pattern (`entry.change` mutates the shared
/// table) while satisfying `Vfs`'s `Send + Sync` bound.
#[derive(Debug, Default)]
pub struct DirMap(pub Arc<std::sync::Mutex<FxHashMap<PathKey, String>>>);

impl Clone for DirMap {
    /// Go map assignment — shares the backing table.
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl Cloneable for DirMap {
    /// `maps.Clone` — a fresh, independently mutable table.
    fn clone_value(&self) -> Self {
        Self(Arc::new(std::sync::Mutex::new(
            self.0.lock().unwrap().clone(),
        )))
    }
}

impl DirMap {
    /// `make(dirty.CloneableMap[…])`.
    pub fn from_map(map: FxHashMap<PathKey, String>) -> DirMap {
        DirMap(Arc::new(std::sync::Mutex::new(map)))
    }
}

impl FileHandleSource for CachedLayeredFileSystem {
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.layered.get_file(file_name)
    }
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        self.layered.get_file_by_path(file_name, path)
    }
}

impl LayeredFileSystem for CachedLayeredFileSystem {
    fn overlays(&self) -> FxHashMap<PathKey, Arc<crate::overlayfs::Overlay>> {
        self.layered.overlays()
    }

    /// `ExpandFileChanges` — delegates to the layered FS when it implements
    /// `FileChangeExpander` (the trait method default returns `change`).
    fn expand_file_changes(&self, change: FileChangeSummary) -> FileChangeSummary {
        self.layered.expand_file_changes(change)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Vfs for CachedLayeredFileSystem {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.fs.case_sensitivity()
    }
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.fs.file_exists(path)
    }
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.fs.read_file(path)
    }
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.fs.write_file(path, data)
    }
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.fs.append_file(path, data)
    }
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.fs.remove(path)
    }
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.fs.chtimes(path, a_time, m_time)
    }
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.fs.directory_exists(path)
    }
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.fs.get_accessible_entries(path)
    }
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.fs.stat(path)
    }
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.fs.realpath(path)
    }
}

/// `realpathAliasSet` is a thread-safe set of symlink paths that alias a
/// single realpath. It implements `dirty.Cloneable` so it can be used as a
/// value in `dirty.SyncMap`.
///
/// PORT: the mutex is unnecessary — mutation happens inside
/// `dirty.SyncMapEntry` change callbacks, which are already synchronized.
#[derive(Clone, Default)]
pub struct RealpathAliasSet {
    pub paths: FxHashMap<PathKey, RootedFilePath>,
}

impl RealpathAliasSet {
    /// `(s *realpathAliasSet) Add`.
    pub fn add(&mut self, path: PathKey, file_name: RootedFilePath) {
        self.paths.insert(path, file_name);
    }

    /// `(p aliasPaths) Has`.
    pub fn has(&self, path: &PathKey) -> bool {
        self.paths.contains_key(path)
    }

    /// `(p aliasPaths) Len`.
    pub fn len(&self) -> usize {
        self.paths.len()
    }

    pub fn is_empty(&self) -> bool {
        self.paths.is_empty()
    }
}

impl tsc_dirty::Cloneable for RealpathAliasSet {
    fn clone_value(&self) -> Self {
        self.clone()
    }
}

/// `SnapshotFS`.
pub struct SnapshotFs {
    pub case_sensitivity: CaseSensitivity,
    pub fs: Arc<dyn LayeredFileSystem>,
    pub cache_files: FxHashMap<PathKey, CachedFile>,
    pub cache_directories: FxHashMap<PathKey, DirMap>,
    pub read_files: SyncMap<PathKey, Arc<MemoizedCachedFile>>,
    /// `nodeModulesRealpathAliases` maps realpath-based keys to sets of
    /// symlink-based keys, for files inside node_modules that are accessed
    /// through directory symlinks. This allows watch events (which use
    /// realpaths) to invalidate files cached under symlink paths.
    pub node_modules_realpath_aliases: FxHashMap<PathKey, RealpathAliasSet>,
}

/// `memoizedCachedFile` — `sync.OnceValue(func() FileHandle)`; `None` is the
/// nil `FileHandle`.
pub struct MemoizedCachedFile {
    once: OnceLock<Option<Arc<dyn FileHandle>>>,
    f: Box<dyn Fn() -> Option<Arc<dyn FileHandle>> + Send + Sync>,
}

impl MemoizedCachedFile {
    pub fn new(f: impl Fn() -> Option<Arc<dyn FileHandle>> + Send + Sync + 'static) -> Self {
        MemoizedCachedFile {
            once: OnceLock::new(),
            f: Box::new(f),
        }
    }

    /// `entry()` — the memoized load.
    pub fn call(&self) -> Option<Arc<dyn FileHandle>> {
        self.once.get_or_init(|| (self.f)()).clone()
    }
}

impl FileSource for SnapshotFs {
    /// `(s *SnapshotFS) FS`.
    fn fs(&self) -> Arc<dyn Vfs> {
        layered_as_vfs(self.fs.clone())
    }

    /// `(s *SnapshotFS) GetFile`.
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.get_file_by_path(
            file_name,
            &self.case_sensitivity.path_key(&file_name.as_path()),
        )
    }

    /// `(s *SnapshotFS) GetFileByPath`.
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        if let Some(file) = self.cache_files.get(path) {
            return Some(Arc::new(file.clone()));
        }
        let layered = self.fs.clone();
        let file_name = file_name.clone();
        let path_key = path.clone();
        let new_entry = Arc::new(MemoizedCachedFile::new(move || {
            layered.get_file_by_path(&file_name, &path_key)
        }));
        let (entry, _) = self.read_files.load_or_store(path.clone(), new_entry);
        entry.call()
    }

    /// `(s *SnapshotFS) FileExists`.
    fn file_exists(&self, file_name: &RootedFilePath, path: &PathKey) -> bool {
        if self.cache_files.contains_key(path) {
            return true;
        }
        self.fs.file_exists(file_name)
    }

    /// `(s *SnapshotFS) GetAccessibleEntries`.
    fn get_accessible_entries(&self, directory_name: &RootedDirectoryPath) -> Entries {
        let lower_entries = self.fs.get_accessible_entries(directory_name);
        let key = self.case_sensitivity.path_key(&directory_name.as_path());
        let Some(directory) = self.cache_directories.get(&key) else {
            return lower_entries;
        };
        let fs = self.fs.clone();
        let directory_name = directory_name.clone();
        merge_cached_directory_entries(
            &lower_entries,
            directory,
            |path, child_name| {
                self.cache_files.contains_key(path)
                    || fs.file_exists(&directory_name.resolve_file(child_name))
            },
            self.fs.case_sensitivity(),
        )
    }
}

/// `mergeCachedDirectoryEntries`.
fn merge_cached_directory_entries(
    directory_entries: &Entries,
    cached_entries: &DirMap,
    is_cached_file: impl Fn(&PathKey, &str) -> bool,
    case_sensitivity: CaseSensitivity,
) -> Entries {
    let mut entries = Entries {
        files: Vec::new(),
        directories: Vec::new(),
        symlinks: directory_entries.symlinks.clone(),
    };
    let equal_name =
        |left: &str, right: &str| (case_sensitivity.get_comparer())(left, right) == 0;
    let has_name = |names: &[String], name: &str| names.iter().any(|n| equal_name(n, name));
    for (child_path, child_name) in cached_entries.0.lock().unwrap().iter() {
        if let Some(symlinks) = &mut entries.symlinks {
            let child_name = child_name.clone();
            symlinks.retain(|name| !equal_name(name, &child_name));
        }
        if is_cached_file(child_path, child_name) {
            entries.files.push(child_name.clone());
        } else {
            entries.directories.push(child_name.clone());
        }
    }
    for file_name in &directory_entries.files {
        if !has_name(&entries.files, file_name) && !has_name(&entries.directories, file_name) {
            entries.files.push(file_name.clone());
        }
    }
    for directory_name in &directory_entries.directories {
        if !has_name(&entries.files, directory_name)
            && !has_name(&entries.directories, directory_name)
        {
            entries.directories.push(directory_name.clone());
        }
    }
    entries
}

/// `snapshotFSBuilder`.
pub struct SnapshotFsBuilder {
    pub fs: Arc<dyn LayeredFileSystem>,
    /// `pub(crate)` — `snapshot.rs`/`autoimport.rs` reach the raw map for
    /// `processFileChanges`/`autoImportBuilderFS` like Go's package access.
    pub(crate) cache_files: tsc_dirty::SyncMap<PathKey, CachedFile>,
    cache_directories: tsc_dirty::SyncMap<PathKey, DirMap>,
    source_backed_replacements: Arc<SyncSet<PathKey>>,
    node_modules_realpath_aliases: tsc_dirty::SyncMap<PathKey, RealpathAliasSet>,
    pub(crate) case_sensitivity: CaseSensitivity,
}

/// `newSnapshotFSBuilderFromSource`.
pub fn new_snapshot_fs_builder_from_source(
    fs: Arc<dyn LayeredFileSystem>,
    cache_files: FxHashMap<PathKey, CachedFile>,
    cache_directories: FxHashMap<PathKey, DirMap>,
    node_modules_realpath_aliases: FxHashMap<PathKey, RealpathAliasSet>,
) -> SnapshotFsBuilder {
    let fs = new_cached_layered_file_system(fs);
    SnapshotFsBuilder {
        case_sensitivity: fs.case_sensitivity(),
        fs,
        cache_files: tsc_dirty::SyncMap::new(Some(cache_files)),
        cache_directories: tsc_dirty::SyncMap::new(Some(cache_directories)),
        source_backed_replacements: Arc::new(SyncSet::new()),
        node_modules_realpath_aliases: tsc_dirty::SyncMap::new(Some(
            node_modules_realpath_aliases,
        )),
    }
}

impl FileSource for SnapshotFsBuilder {
    /// `(s *snapshotFSBuilder) FS`.
    fn fs(&self) -> Arc<dyn Vfs> {
        self.fs_vfs()
    }
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        SnapshotFsBuilder::get_file(self, file_name)
    }
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        SnapshotFsBuilder::get_file_by_path(self, file_name, path)
    }
    fn file_exists(&self, file_name: &RootedFilePath, path: &PathKey) -> bool {
        SnapshotFsBuilder::file_exists(self, file_name, path)
    }
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        SnapshotFsBuilder::get_accessible_entries(self, path)
    }
}

/// `newSnapshotFSBuilder` — used for fresh builders with no prior cache
/// state (Go passes nil maps; `dirty.NewSyncMap(nil)` → `None`).
pub fn new_snapshot_fs_builder(fs: Arc<dyn LayeredFileSystem>) -> SnapshotFsBuilder {
    let fs = new_cached_layered_file_system(fs);
    SnapshotFsBuilder {
        case_sensitivity: fs.case_sensitivity(),
        fs,
        cache_files: tsc_dirty::SyncMap::new(None),
        cache_directories: tsc_dirty::SyncMap::new(None),
        source_backed_replacements: Arc::new(SyncSet::new()),
        node_modules_realpath_aliases: tsc_dirty::SyncMap::new(None),
    }
}

impl SnapshotFsBuilder {
    /// `(s *snapshotFSBuilder) FS`.
    pub fn fs_vfs(&self) -> Arc<dyn Vfs> {
        layered_as_vfs(self.fs.clone())
    }

    /// `(s *snapshotFSBuilder) Finalize` — synchronizes the directory
    /// structure based on added and deleted cache entries and returns the
    /// finalized `SnapshotFS` plus whether anything changed.
    pub fn finalize(&self) -> (SnapshotFs, bool) {
        // PORT: hooks are `Box<dyn FnMut + 'static>`; captures that Go took by
        // pointer are shared through `Rc`/`Arc` handles cloned into each
        // closure.
        let deleted: Rc<RefCell<Option<FxHashMap<PathKey, Option<CachedFile>>>>> =
            Rc::new(RefCell::new(None));

        fn on_added_file(
            cache_directories: &tsc_dirty::SyncMap<PathKey, DirMap>,
            path: &PathKey,
            file_name: &RootedFilePath,
        ) {
            let mut child_path = path.clone();
            let mut child = file_name.as_path();
            loop {
                let parent_path = child_path.parent();
                let parent = child.directory();
                if child_path == parent_path {
                    break; // reached root
                }
                let base_name = child.base_name().to_string();
                if let Some(dir_entry) = cache_directories.load(&parent_path) {
                    let child_path = child_path.clone();
                    let base_name = base_name.clone();
                    dir_entry.change(move |dir: &mut DirMap| {
                        dir.0.lock().unwrap().insert(child_path, base_name);
                    });
                    break;
                } else {
                    let mut dir = FxHashMap::default();
                    dir.insert(child_path.clone(), base_name);
                    cache_directories
                        .load_or_store(parent_path.clone(), DirMap::from_map(dir));
                }
                child_path = parent_path;
                child = parent.as_path();
            }
        }

        fn on_deleted_file_or_directory(
            cache_directories: &tsc_dirty::SyncMap<PathKey, DirMap>,
            path: &PathKey,
        ) {
            let Some(dir_entry) = cache_directories.load(&path.parent()) else {
                return;
            };
            // PORT: Go deletes the entry from inside `Change`; `change` holds
            // the entry lock here, so the delete runs after it returns.
            let mut should_delete = false;
            dir_entry.change(|dir| {
                let mut dir = dir.0.lock().unwrap();
                dir.remove(path);
                should_delete = dir.is_empty();
            });
            if should_delete {
                dir_entry.delete();
                on_deleted_file_or_directory(cache_directories, &dir_entry.key());
            }
        }

        let source_backed_replacements = self.source_backed_replacements.clone();
        let deleted_hook = deleted.clone();
        let cache_directories = self.cache_directories.clone();
        let (cache_files, changed) = self.cache_files.finalize_with(FinalizationHooks {
            on_delete: Some(Box::new(move |key: PathKey, value: Option<CachedFile>| {
                if source_backed_replacements.has(&key) {
                    return;
                }
                deleted_hook
                    .borrow_mut()
                    .get_or_insert_with(FxHashMap::default)
                    .insert(key, value);
            })),
            on_change: None,
            on_add: Some(Box::new(move |key: PathKey, value: Option<CachedFile>| {
                if let Some(value) = value {
                    on_added_file(&cache_directories, &key, &value.base.file_name);
                }
            })),
        });

        if let Some(deleted) = deleted.borrow().as_ref() {
            for path in deleted.keys() {
                on_deleted_file_or_directory(&self.cache_directories, path);
            }
        }

        // Prune deleted symlink paths from realpath alias sets before
        // finalizing, so that empty sets are dropped during finalization.
        if let Some(deleted) = deleted.borrow().as_ref() {
            for (deleted_path, deleted_file) in deleted {
                let Some(deleted_file) = deleted_file else {
                    continue;
                };
                if deleted_file.realpath_path.as_string().is_empty() {
                    continue;
                }
                if let Some(entry) = self
                    .node_modules_realpath_aliases
                    .load(&deleted_file.realpath_path)
                {
                    let deleted_path = deleted_path.clone();
                    entry.locked(move |e: &mut dyn Value<RealpathAliasSet>| {
                        e.change(&mut |alias_set: &mut RealpathAliasSet| {
                            alias_set.paths.remove(&deleted_path);
                        });
                        if e.value().is_none_or(|v| v.paths.is_empty()) {
                            e.delete();
                        }
                    });
                }
            }
        }

        let (node_modules_realpath_aliases, aliases_changed) =
            self.node_modules_realpath_aliases.finalize();
        let (cache_directories, _) = self.cache_directories.finalize();

        (
            SnapshotFs {
                case_sensitivity: self.case_sensitivity,
                fs: self.fs.clone(),
                cache_files: cache_files.unwrap_or_default(),
                cache_directories: cache_directories.unwrap_or_default(),
                read_files: SyncMap::new(),
                node_modules_realpath_aliases: node_modules_realpath_aliases
                    .unwrap_or_default(),
            },
            changed || aliases_changed,
        )
    }

    /// `(s *snapshotFSBuilder) GetFile`.
    pub fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        let path = self.case_sensitivity.path_key(&file_name.as_path());
        self.get_file_by_path(file_name, &path)
    }

    /// `deleteCacheEntry`.
    pub(crate) fn delete_cache_entry(&self, entry: &SyncMapEntry<PathKey, CachedFile>) {
        if let Some(file) = entry.value() {
            if self.fs.file_exists(file.file_name()) {
                self.source_backed_replacements.add(entry.key());
            }
        }
        entry.delete();
    }

    /// `(s *snapshotFSBuilder) FileExists`.
    pub fn file_exists(&self, file_name: &RootedFilePath, path: &PathKey) -> bool {
        if let Some(entry) = self.cache_files.load(path) {
            if entry.value().is_none() {
                return false;
            }
            // Entry may be dirty - reload to check current state in the
            // source filesystem.
            return self.reload_entry_if_needed(&entry).is_some();
        }
        // Path never loaded into cacheFiles - use cached stat (no file read).
        self.fs.file_exists(file_name)
    }

    /// `(s *snapshotFSBuilder) GetFileByPath`.
    pub fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        if let Some(entry) = self.cache_files.load(path) {
            return self.reload_entry_if_needed(&entry);
        }
        let file = self.fs.get_file_by_path(file_name, path)?;
        if file.is_overlay() {
            return Some(file);
        }
        self.cache_source_file(file_name, path, &file)
    }

    /// `(s *snapshotFSBuilder) GetAccessibleEntries`.
    pub fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        let lower_entries = self.fs.get_accessible_entries(path);
        let key = self.case_sensitivity.path_key(&path.as_path());
        let Some(directory) = self.cache_directories.load(&key) else {
            return lower_entries;
        };
        let Some(directory_value) = directory.value() else {
            return lower_entries;
        };
        let fs = self.fs.clone();
        let path = path.clone();
        merge_cached_directory_entries(
            &lower_entries,
            &directory_value,
            |key, child_name| {
                self.cache_files
                    .load(key)
                    .is_some_and(|entry| entry.value().is_some())
                    || fs.file_exists(&path.resolve_file(child_name))
            },
            self.fs.case_sensitivity(),
        )
    }

    /// `cacheSourceFile`.
    fn cache_source_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        source: &Arc<dyn FileHandle>,
    ) -> Option<Arc<dyn FileHandle>> {
        let mut file = new_cached_file(file_name.clone(), source.content().to_string());
        file.base.hash = source.hash();
        let (entry, loaded) = self.cache_files.load_or_store(path.clone(), file)?;
        if !loaded && path.as_string().contains("/node_modules/") {
            self.record_realpath_alias(&entry, file_name, path);
        }
        self.reload_entry_if_needed(&entry)
    }

    /// `getCachedFile`.
    fn get_cached_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        force_reload: bool,
    ) -> Option<Arc<dyn FileHandle>> {
        let (entry, loaded) = self.cache_files.load_or_store(
            path.clone(),
            CachedFile {
                base: crate::overlayfs::FileBase::new(
                    file_name.clone(),
                    String::new(),
                    tsc_ast::Uint128::default(),
                ),
                needs_reload: true,
                realpath_path: PathKey::default(),
            },
        )?;
        if !loaded && path.as_string().contains("/node_modules/") {
            self.record_realpath_alias(&entry, file_name, path);
        }
        if force_reload {
            return self.reload_entry(&entry);
        }
        self.reload_entry_if_needed(&entry)
    }

    /// `recordRealpathAlias` checks if fileName is accessed through a symlink
    /// and, if so, records a mapping from the realpath-based key to the
    /// symlink-based key. This is only called for files inside node_modules
    /// where symlinks are common.
    fn record_realpath_alias(
        &self,
        cached_file_entry: &SyncMapEntry<PathKey, CachedFile>,
        symlink_file_name: &RootedFilePath,
        symlink_path: &PathKey,
    ) {
        let realpath = RootedFilePath::from(self.fs.realpath(&symlink_file_name.as_path()));
        let realpath_path = self.case_sensitivity.path_key(&realpath.as_path());
        if realpath_path != *symlink_path {
            let realpath_path_for_entry = realpath_path.clone();
            cached_file_entry.change(move |file: &mut CachedFile| {
                file.realpath_path = realpath_path_for_entry;
            });
            if let Some((entry, _)) = self
                .node_modules_realpath_aliases
                .load_or_store(realpath_path, RealpathAliasSet::default())
            {
                let symlink_path = symlink_path.clone();
                let symlink_file_name = symlink_file_name.clone();
                entry.change(move |alias_set: &mut RealpathAliasSet| {
                    alias_set.add(symlink_path, symlink_file_name);
                });
            }
        }
    }

    /// `reloadEntry`.
    fn reload_entry(&self, entry: &SyncMapEntry<PathKey, CachedFile>) -> Option<Arc<dyn FileHandle>> {
        let mut file_name = RootedFilePath::default();
        entry.locked(|e: &mut dyn Value<CachedFile>| {
            if let Some(file) = e.value() {
                file_name = file.base.file_name.clone();
            }
        });
        if file_name.as_string().is_empty() {
            return None;
        }
        // Read file outside the lock to avoid blocking other goroutines.
        let content = self.fs.read_file(&file_name);
        entry.locked(|e: &mut dyn Value<CachedFile>| {
            if e.value().is_none() {
                return;
            }
            if let Some(content) = &content {
                let hash = hash_string_128(content);
                let content = content.clone();
                e.change(&mut move |file: &mut CachedFile| {
                    file.base.content = content.clone();
                    file.base.hash = hash;
                    file.needs_reload = false;
                });
            } else {
                e.delete();
            }
        });
        entry.value().map(|f| Arc::new(f) as Arc<dyn FileHandle>)
    }

    /// `reloadEntryIfNeeded`.
    pub(crate) fn reload_entry_if_needed(
        &self,
        entry: &SyncMapEntry<PathKey, CachedFile>,
    ) -> Option<Arc<dyn FileHandle>> {
        let mut file_name = RootedFilePath::default();
        entry.locked(|e: &mut dyn Value<CachedFile>| {
            if let Some(file) = e.value() {
                if !file.matches_disk_text() {
                    file_name = file.base.file_name.clone();
                }
            }
        });
        if !file_name.as_string().is_empty() {
            // Read file outside the lock to avoid blocking other goroutines.
            let content = self.fs.read_file(&file_name);
            entry.locked(|e: &mut dyn Value<CachedFile>| {
                if e.value().is_none_or(|v| v.matches_disk_text()) {
                    return; // another goroutine already reloaded it
                }
                if let Some(content) = &content {
                    let hash = hash_string_128(content);
                    let content = content.clone();
                    e.change(&mut move |file: &mut CachedFile| {
                        file.base.content = content.clone();
                        file.base.hash = hash;
                        file.needs_reload = false;
                    });
                } else {
                    e.delete();
                }
            });
        }
        entry.value().map(|f| Arc::new(f) as Arc<dyn FileHandle>)
    }

    /// `watchChangesOverlapCache`.
    pub fn watch_changes_overlap_cache(
        &self,
        change: &FileChangeSummary,
        previous_open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
        open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
    ) -> bool {
        for uri in change.changed.keys() {
            let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
            if previous_open_files.contains_key(&path) || open_files.contains_key(&path) {
                return true;
            }
            if self.cache_files.load(&path).is_some() {
                return true;
            }
            if self.node_modules_realpath_aliases.load(&path).is_some() {
                return true;
            }
        }
        for uri in change.deleted.keys() {
            let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
            if previous_open_files.contains_key(&path) || open_files.contains_key(&path) {
                return true;
            }
            if self.cache_files.load(&path).is_some() {
                return true;
            }
            if self.node_modules_realpath_aliases.load(&path).is_some() {
                return true;
            }
        }
        false
    }

    /// `invalidateCache`.
    pub fn invalidate_cache(&self) {
        self.cache_files
            .range(|entry: &SyncMapEntry<PathKey, CachedFile>| {
                entry.change(|file: &mut CachedFile| {
                    file.needs_reload = true;
                });
                true
            });
    }

    /// `invalidateNodeModulesCache`.
    pub fn invalidate_node_modules_cache(&self) {
        self.cache_files
            .range(|entry: &SyncMapEntry<PathKey, CachedFile>| {
                if entry.key().as_string().contains("/node_modules/") {
                    entry.change(|file: &mut CachedFile| {
                        file.needs_reload = true;
                    });
                }
                true
            });
    }

    /// `markDirtyFiles`.
    ///
    /// PORT: sequential — Go fanned `reloadEntryIfContentChanged` out on a
    /// `WorkGroup`; the Rust port's `dirty` structures are single-threaded.
    pub fn mark_dirty_files(&self, mut change: FileChangeSummary) -> FileChangeSummary {
        if change.changed.len() > 0 {
            let mut filtered_changed = Set::<DocumentUri>::new();
            for uri in change.changed.keys() {
                let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
                if let Some(file) = self.fs.get_file_by_path(&uri.file_name(), &path) {
                    if file.is_overlay() {
                        filtered_changed.add(uri.clone());
                        continue;
                    }
                }
                let Some(entry) = self.cache_files.load(&path) else {
                    filtered_changed.add(uri.clone());
                    continue;
                };
                if self.reload_entry_if_content_changed(&entry) {
                    filtered_changed.add(uri.clone());
                }
            }
            change.changed = filtered_changed;
        }
        for uri in change.deleted.keys() {
            let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
            if let Some(entry) = self.cache_files.load(&path) {
                self.delete_cache_entry(&entry);
            }
        }
        change
    }

    /// `reloadEntryIfContentChanged`.
    fn reload_entry_if_content_changed(&self, entry: &SyncMapEntry<PathKey, CachedFile>) -> bool {
        let Some(file) = entry.value() else {
            return true;
        };
        let content = self.fs.read_file(&file.base.file_name);
        let changed = RefCell::new(true);
        entry.locked(|e: &mut dyn Value<CachedFile>| {
            if e.value().is_none() {
                return;
            }
            let cur = e.value().unwrap();
            let Some(content) = &content else {
                e.delete();
                return;
            };
            if *content == cur.base.content {
                *changed.borrow_mut() = false;
                if !cur.matches_disk_text() {
                    e.change(&mut |file: &mut CachedFile| {
                        file.needs_reload = false;
                    });
                }
                return;
            }
            let hash = hash_string_128(content);
            let content = content.clone();
            e.change(&mut move |file: &mut CachedFile| {
                file.base.content = content.clone();
                file.base.hash = hash;
                file.needs_reload = false;
            });
        });
        *changed.borrow()
    }

    /// `isRelevantFileName` — returns true if the given URI refers to a file
    /// that could affect the project: it has a TypeScript-relevant or
    /// configured content-mapper extension, is dynamic (e.g. untitled), or is
    /// present in the supplied open-file state.
    pub fn is_relevant_file_name(
        &self,
        uri: &DocumentUri,
        content_mapper_extensions: &[String],
        content_mapper_watched_files: Option<&Set<PathKey>>,
        open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
    ) -> bool {
        let file_name = uri.file_name();
        if content_mapper_watched_files
            .is_some_and(|watched| {
                watched.has(&self.case_sensitivity.path_key(&file_name.as_path()))
            })
        {
            return true;
        }
        if file_name.extension_is_one_of(
            &content_mapper_extensions
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        ) {
            return true;
        }
        if file_name.is_dynamic() {
            return true;
        }
        if open_files.contains_key(&self.case_sensitivity.path_key(&file_name.as_path())) {
            return true;
        }
        is_relevant_extension(&file_name.any_extension(&[], CaseSensitivity::CaseSensitive))
    }

    /// `expandAndFilterWatchEvents` expands directory deletion URIs into
    /// individual file deletion URIs using the cached directory structure,
    /// and filters out watch events for paths that are neither known
    /// directories nor have relevant file extensions.
    pub fn expand_and_filter_watch_events(
        &self,
        mut change: FileChangeSummary,
        content_mapper_extensions: &[String],
        content_mapper_watched_files: Option<&Set<PathKey>>,
        previous_open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
        open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
    ) -> FileChangeSummary {
        if change.deleted.len() > 0 {
            let mut filtered_deleted = Set::<DocumentUri>::new();
            for uri in change.deleted.keys() {
                let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
                if self.cache_directories.load(&path).is_some()
                    || has_open_file_within(&path, previous_open_files, open_files)
                {
                    self.collect_files_recursive(
                        &path,
                        &mut filtered_deleted,
                        previous_open_files,
                        open_files,
                    );
                } else if self.is_relevant_file_name(
                    &uri,
                    content_mapper_extensions,
                    content_mapper_watched_files,
                    open_files,
                ) || is_node_modules_path(&path)
                {
                    // node_modules deletions must always be preserved for
                    // auto-import registry change handlers. They won't be in
                    // cacheDirectories since the registry doesn't use the
                    // snapshotFSBuilder for its file system, since we don't
                    // want to retain files read there.
                    filtered_deleted.add(uri.clone());
                }
            }
            change.deleted = filtered_deleted;
        }

        if change.changed.len() > 0 {
            let mut filtered_changed = Set::<DocumentUri>::new();
            for uri in change.changed.keys() {
                if self.is_relevant_file_name(
                    &uri,
                    content_mapper_extensions,
                    content_mapper_watched_files,
                    open_files,
                ) {
                    filtered_changed.add(uri.clone());
                }
            }
            change.changed = filtered_changed;
        }

        // We can't filter created events because any created path could be a
        // directory symlink that includes relevant files.
        // configFileRegistryBuilder will check if these paths are directories
        // if they fall within a config's wildcard directories.

        change
    }

    /// `collectFilesRecursive` recursively collects all cached file URIs under
    /// the given directory path using the cacheDirectories and cacheFiles
    /// maps.
    fn collect_files_recursive(
        &self,
        dir_path: &PathKey,
        files: &mut Set<DocumentUri>,
        previous_open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
        open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
    ) {
        for (path, file) in open_files {
            if dir_path.contains_path(path) {
                files.add(tsc_lsconv::file_name_to_document_uri(file.file_name()));
            }
        }
        for (path, file) in previous_open_files {
            if dir_path.contains_path(path) {
                files.add(tsc_lsconv::file_name_to_document_uri(file.file_name()));
            }
        }
        let Some(dir_entry) = self.cache_directories.load(dir_path) else {
            return;
        };
        let Some(dir) = dir_entry.value() else {
            return;
        };
        let children: Vec<PathKey> = dir.0.lock().unwrap().keys().cloned().collect();
        for child_path in children {
            if let Some(entry) = self.cache_files.load(&child_path) {
                if let Some(file) = entry.value() {
                    files.add(tsc_lsconv::file_name_to_document_uri(&file.base.file_name));
                }
            }
            self.collect_files_recursive(&child_path, files, previous_open_files, open_files);
        }
    }

    /// `convertOpenAndCloseToChanges`.
    pub fn convert_open_and_close_to_changes(
        &self,
        mut change: FileChangeSummary,
        previous_open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
        open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
    ) -> FileChangeSummary {
        if !change.opened.as_str().is_empty() && !change.opened.file_name().is_dynamic() {
            let path = self
                .case_sensitivity
                .path_key(&change.opened.file_name().as_path());
            match self.cache_files.load(&path) {
                None => {
                    change.created.add(change.opened.clone());
                }
                Some(entry) if entry.original().is_none() => {
                    change.created.add(change.opened.clone());
                }
                Some(entry) => {
                    if let Some(open_file) = open_files.get(&path) {
                        // The file already exists in the program, but the
                        // open-file content from didOpen may differ from what
                        // was originally read from the source (e.g. the
                        // editor normalizes line endings, or the source file
                        // changed since the project was loaded). Mark it as
                        // Changed so the project rebuilds.
                        if let Some(cached_file) = entry.original() {
                            if open_file.hash() != cached_file.hash() {
                                change.changed.add(change.opened.clone());
                            }
                        }
                        self.delete_cache_entry(&entry);
                    }
                }
            }
        }
        for uri in change.closed.keys() {
            let file_name = uri.file_name();
            if file_name.is_dynamic() {
                continue;
            }
            let path = self.case_sensitivity.path_key(&file_name.as_path());
            // We may have ignored watcher events while the file was open, so
            // force a reload.
            if let Some(fh) = self.get_cached_file(&file_name, &path, true) {
                if let Some(previous_open_file) = previous_open_files.get(&path) {
                    if fh.hash() != previous_open_file.hash() {
                        change.changed.add(uri.clone());
                    }
                }
                continue;
            }
            change.deleted.add(uri.clone());
        }
        change
    }
}

impl SnapshotFs {
    /// `(s *SnapshotFS) expandRealpathAliases` adds synthetic URIs to the
    /// Changed and Deleted sets for files that were accessed through
    /// node_modules symlinks. When a watch event arrives using a realpath,
    /// this expands it to include the symlink-based path so that downstream
    /// consumers (markDirtyFiles, markFilesChanged) can find cached entries.
    pub fn expand_realpath_aliases(&self, mut change: FileChangeSummary) -> FileChangeSummary {
        if self.node_modules_realpath_aliases.is_empty() {
            return change;
        }

        let mut additional_changed = Set::<DocumentUri>::new();
        for uri in change.changed.keys() {
            let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
            if let Some(aliases) = self.node_modules_realpath_aliases.get(&path) {
                for alias_file_name in aliases.paths.values() {
                    additional_changed
                        .add(tsc_lsconv::file_name_to_document_uri(alias_file_name));
                }
            }
        }
        for uri in additional_changed.keys() {
            change.changed.add(uri.clone());
        }

        let mut additional_deleted = Set::<DocumentUri>::new();
        for uri in change.deleted.keys() {
            let path = self.case_sensitivity.path_key(&uri.file_name().as_path());
            if let Some(aliases) = self.node_modules_realpath_aliases.get(&path) {
                for alias_file_name in aliases.paths.values() {
                    additional_deleted
                        .add(tsc_lsconv::file_name_to_document_uri(alias_file_name));
                }
            }
        }
        for uri in additional_deleted.keys() {
            change.deleted.add(uri.clone());
        }

        change
    }
}

/// `isRelevantExtension` returns true if the given extension is a known
/// TypeScript or JavaScript extension that can affect the project.
fn is_relevant_extension(ext: &str) -> bool {
    matches!(
        ext,
        ".js" | ".jsx" | ".mjs" | ".cjs" | ".ts" | ".tsx" | ".mts" | ".cts" | ".json"
    )
}

/// `isNodeModulesPath` reports whether path is a node_modules directory
/// itself or lives inside one. Used to preserve node_modules watch
/// deletions, whose package files are read transiently and therefore never
/// tracked in cacheDirectories.
pub fn is_node_modules_path(path: &PathKey) -> bool {
    let s = path.as_string();
    s.ends_with("/node_modules") || s.contains("/node_modules/")
}

/// `hasOpenFileWithin`.
fn has_open_file_within(
    path: &PathKey,
    previous_open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
    open_files: &FxHashMap<PathKey, Arc<dyn FileHandle>>,
) -> bool {
    for open_file_path in open_files.keys() {
        if path.contains_path(open_file_path) {
            return true;
        }
    }
    for open_file_path in previous_open_files.keys() {
        if path.contains_path(open_file_path) {
            return true;
        }
    }
    false
}

/// `sourceFS` is a vfs.FS that sources files from a FileSource and tracks
/// seen files.
pub struct SourceFs {
    tracking: AtomicBool,
    missing_directories: SyncSet<PathKey>,
    seen_files: SyncMap<PathKey, RootedFilePath>,
    source: RwLock<Arc<dyn FileSource>>,
    case_sensitivity: CaseSensitivity,
}

/// `newSourceFS`.
pub fn new_source_fs(tracking: bool, source: Arc<dyn FileSource>) -> SourceFs {
    SourceFs {
        tracking: AtomicBool::new(tracking),
        missing_directories: SyncSet::default(),
        seen_files: SyncMap::new(),
        case_sensitivity: source.fs().case_sensitivity(),
        source: RwLock::new(source),
    }
}

impl SourceFs {
    /// `DisableTracking`.
    pub fn disable_tracking(&self) {
        self.tracking.store(false, Ordering::SeqCst);
    }

    /// `set_source` — used by `compilerHost.freeze` to swap the builder
    /// source for the finalized `SnapshotFS`.
    pub fn set_source(&self, source: Arc<dyn FileSource>) {
        *self.source.write().unwrap() = source;
    }

    /// `fs.source` — the wrapped `FileSource` (read handle).
    pub fn source(&self) -> Arc<dyn FileSource> {
        self.source.read().unwrap().clone()
    }

    /// `Track`.
    pub fn track(&self, file_name: &RootedFilePath) {
        if !self.tracking.load(Ordering::SeqCst) {
            return;
        }
        self.seen_files.store(
            self.case_sensitivity.path_key(&file_name.as_path()),
            file_name.clone(),
        );
    }

    /// `SeenFile`.
    pub fn seen_file(&self, path: &PathKey) -> bool {
        self.seen_files.load(path).is_some()
    }

    /// `SeenFileOrMissingParentDirectory`.
    pub fn seen_file_or_missing_parent_directory(&self, path: &PathKey) -> bool {
        if self.seen_files.load(path).is_some() {
            return true;
        }
        if !self.missing_directories.is_empty() {
            let mut path = path.clone();
            loop {
                if self.missing_directories.has(&path) {
                    return true;
                }
                let parent = path.parent();
                if parent == path {
                    break;
                }
                path = parent;
            }
        }
        false
    }
}

impl FileHandleSource for SourceFs {
    /// `(fs *sourceFS) GetFile`.
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.track(file_name);
        self.source.read().unwrap().get_file(file_name)
    }

    /// `(fs *sourceFS) GetFileByPath`.
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        self.track(file_name);
        self.source.read().unwrap().get_file_by_path(file_name, path)
    }
}

impl Vfs for SourceFs {
    /// `CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    /// `DirectoryExists`.
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        let exists = self.source.read().unwrap().fs().directory_exists(path);
        if !exists && self.tracking.load(Ordering::SeqCst) {
            self.missing_directories
                .add(self.case_sensitivity.path_key(&path.as_path()));
        }
        exists
    }

    /// `FileExists`.
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.track(path);
        let key = self.case_sensitivity.path_key(&path.as_path());
        self.source.read().unwrap().file_exists(path, &key)
    }

    /// `GetAccessibleEntries`.
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.source.read().unwrap().get_accessible_entries(path)
    }

    /// `ReadFile`.
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        let fh = self.get_file(path)?;
        Some(fh.content().to_string())
    }

    /// `Realpath`.
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.source.read().unwrap().fs().realpath(path)
    }

    /// `Stat`.
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.source.read().unwrap().fs().stat(path)
    }

    fn write_file(&self, _path: &RootedFilePath, _data: &str) -> Result<(), FsError> {
        panic!("unimplemented")
    }
    fn append_file(&self, _path: &RootedFilePath, _data: &str) -> Result<(), FsError> {
        panic!("unimplemented")
    }
    fn remove(&self, _path: &RootedPath) -> Result<(), FsError> {
        panic!("unimplemented")
    }
    fn chtimes(&self, _path: &RootedPath, _a: SystemTime, _m: SystemTime) -> Result<(), FsError> {
        panic!("unimplemented")
    }
}
