// Ported from tsc/internal/api/requestfilesystem/requestfilesystem.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `vfs.FS`/`project.LayeredFileSystem`/`project.RebasableFileSystem`
//   implementations dispatch through `Arc<dyn ...>` trait objects. The Go
//   `getRequestFileSystem` assertion becomes `as_any().downcast_ref` via the
//   `Vfs::as_any` hook added for this port.
// - `s.paths` (shared `*requestPathNode`) → `Arc<RequestPathNode>`; Go
//   shares the immutable tree across `applyTo`/`WithBaseFileSystem` clones,
//   which `Arc` reproduces. `fmt.Errorf` returns → `String` errors (the
//   session reports them to the client verbatim).

mod filechanges;
mod pathtree;

use std::sync::Arc;
use std::time::SystemTime;

use rustc_hash::{FxHashMap, FxHashSet};
use serde::Deserialize;
use tsc_project::filechange::FileChangeSummary;
use tsc_project::overlayfs::{
    FileHandle, FileHandleSource, LayeredFileSystem, LayeredFsInput, Overlay, OverlayFs,
    RebasableFileSystem, layered_as_vfs, new_cached_file_handle,
};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath, combine_paths,
    has_trailing_directory_separator, rooted_directory_path_from_path, rooted_file_path_from_path,
    rooted_path_from_absolute, to_rooted_path,
};
use tsc_vfs::fs::FsError;
use tsc_vfs::{Entries, Vfs, ERR_INVALID};

use pathtree::{
    RequestEntry, RequestFallback, RequestPathNode, RequestSymlink, clone_entries,
    compose_request_paths, merge_entries, request_path_contains,
};

pub use filechanges::add_file_changes;

/// `Kind` controls how a request filesystem is used. Go's `type Kind
/// string` accepts any value at unmarshal and rejects unknown kinds in
/// `newRequestFileSystemWorker`; `Other` preserves the raw string for the
/// same error message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `KindFull` makes the supplied filesystem canonical and total.
    Full,
    /// `KindLayer` checks the supplied filesystem before falling back to the
    /// host.
    Layer,
    Other(String),
}

impl Kind {
    /// The Go `string` value, for `unknown request filesystem kind %q`.
    fn as_str(&self) -> &str {
        match self {
            Kind::Full => "full",
            Kind::Layer => "layer",
            Kind::Other(s) => s,
        }
    }
}

impl Default for Kind {
    fn default() -> Self {
        Kind::Other(String::new())
    }
}

impl<'de> Deserialize<'de> for Kind {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Ok(match s.as_str() {
            "full" => Kind::Full,
            "layer" => Kind::Layer,
            _ => Kind::Other(s),
        })
    }
}

/// `RequestDirectoryEntries` is a cached directory listing. Entry names are
/// relative to the directory, matching `vfs.GetAccessibleEntries`.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct RequestDirectoryEntries {
    /// `json:"files" nonnil:"true"`
    #[serde(default)]
    pub files: Vec<String>,
    /// `json:"directories" nonnil:"true"`
    #[serde(default)]
    pub directories: Vec<String>,
}

/// `RequestSymlink` describes a symbolic link in a request filesystem.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct RequestSymlinkParams {
    /// Target is resolved relative to the directory containing the link,
    /// matching native symbolic-link semantics.
    pub target: String,
    /// Host routes the target through the host filesystem. This is the only
    /// way a full filesystem can access paths not supplied in the request
    /// filesystem.
    #[serde(default)]
    pub host: bool,
}

/// `RequestFileSystem` supplies file contents and, optionally, directory
/// listings for a request that creates a snapshot.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RequestFileSystemParams {
    pub kind: Kind,
    /// Files maps file names to their complete contents.
    /// `nonnil:"true"`
    #[serde(default)]
    pub files: FxHashMap<String, String>,
    /// Directories maps directory names to complete listing results.
    /// Directory structure implied by Files is derived when a listing is
    /// omitted.
    #[serde(default)]
    pub directories: FxHashMap<String, RequestDirectoryEntries>,
    /// Symlinks maps link paths to targets in this filesystem or the host
    /// filesystem.
    #[serde(default)]
    pub symlinks: FxHashMap<String, RequestSymlinkParams>,
    /// RemovedPaths lists files or directory trees that must be treated as
    /// missing even when present in an underlying snapshot or host
    /// filesystem.
    #[serde(default)]
    pub removed_paths: Vec<String>,
}

struct ResolvedRequestPath {
    path: RootedPath,
    followed_symlink: bool,
    host: bool,
    ok: bool,
}

#[derive(Default)]
struct RequestPathLookup {
    path: RootedPath,
    /// `lookup.info` — the local `requestFile`/`requestDirectory` entry
    /// (`node.entry.(vfs.FileInfo)` — never a symlink).
    info: Option<RequestEntry>,
    /// `lookup.fileSystem` — always `s.base` when set.
    file_system: Option<Arc<dyn Vfs>>,
    followed_symlink: bool,
    ok: bool,
}

impl RequestPathLookup {
    /// `lookup.info.IsDir()` — `nil` info is not a dir; files are not;
    /// directories are.
    fn info_is_dir(&self) -> Option<bool> {
        self.info.as_ref().map(|e| e.is_dir())
    }
}

/// `getRequestFileSystem` — the `fs.(*requestFileSystem)` assertion.
fn get_request_file_system(file_system: &Arc<dyn Vfs>) -> Option<&RequestFileSystem> {
    file_system.as_concrete()?.downcast_ref::<RequestFileSystem>()
}

/// `NewForUpdate` creates a request filesystem for a snapshot update.
/// Layers over request filesystems are compacted eagerly so the result does
/// not retain its base snapshot's filesystem.
pub fn new_for_update(
    params: Option<&RequestFileSystemParams>,
    base: Arc<dyn Vfs>,
    base_source: Option<Arc<dyn FileHandleSource>>,
    current_directory: &RootedDirectoryPath,
    file_changes: &mut FileChangeSummary,
) -> Result<Arc<dyn Vfs>, String> {
    let Some(params) = params else {
        return Ok(base);
    };
    // PORT: `base vfs.FS` + the `fs.(FileHandleSource)` assertion Go makes
    // inside `GetFileByPath` — `base_source` is the asserted twin, supplied
    // by callers that hold a source-capable FS (`None` for plain hosts).
    let mut base_file_system = base.clone();
    let mut base_source = base_source;
    if params.kind == Kind::Full {
        if let Some(request_base) = get_request_file_system(&base) {
            base_file_system = request_base.base.clone();
            base_source = request_base.base_source.clone();
        }
    }
    let mut file_system = new_request_file_system_worker(
        params,
        base_file_system.clone(),
        base_source,
        current_directory,
    )?;
    if let Some(base_request_file_system) = get_request_file_system(&base_file_system) {
        file_system = file_system.apply_to(base_request_file_system.clone());
    }
    if params.kind == Kind::Layer {
        add_file_changes(
            file_changes,
            params,
            &base_file_system,
            &file_system,
            current_directory,
        );
    }
    Ok(Arc::new(file_system))
}

/// `HasFullFileSystem` reports whether fileSystem contains a complete
/// request filesystem.
pub fn has_full_file_system(file_system: &Arc<dyn Vfs>) -> bool {
    get_request_file_system(file_system)
        .is_some_and(|fs| fs.kind == Kind::Full)
}

/// `requestFileSystem` is either a full filesystem or a layer over the
/// session host filesystem. Its base is always the host, which may be a
/// callback filesystem; inherited request entries are compacted into paths.
#[derive(Clone)]
pub struct RequestFileSystem {
    kind: Kind,
    base: Arc<dyn Vfs>,
    /// `s.base.(project.FileHandleSource)` — Go asserts lazily in
    /// `GetFileByPath`; the optional source is carried alongside `base`
    /// like `overlayFS.host_source`.
    base_source: Option<Arc<dyn FileHandleSource>>,
    current_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    paths: Arc<RequestPathNode>,
}

fn new_request_file_system_worker(
    params: &RequestFileSystemParams,
    base: Arc<dyn Vfs>,
    base_source: Option<Arc<dyn FileHandleSource>>,
    current_directory: &RootedDirectoryPath,
) -> Result<RequestFileSystem, String> {
    if params.kind != Kind::Full && params.kind != Kind::Layer {
        return Err(format!(
            "unknown request filesystem kind {:?}",
            params.kind.as_str()
        ));
    }

    let mut result = RequestFileSystem {
        kind: params.kind.clone(),
        case_sensitivity: base.case_sensitivity(),
        base,
        base_source,
        current_directory: current_directory.clone(),
        paths: Arc::new(RequestPathNode::default()),
    };
    let mut paths = RequestPathNode::default();
    result.register_directory(&mut paths, current_directory.clone());
    let mut file_names: Vec<&String> = params.files.keys().collect();
    file_names.sort();
    for file_name in file_names {
        let content = &params.files[file_name];
        let absolute_file_name =
            rooted_file_path_from_path(result.to_absolute_path(file_name));
        let path = result
            .case_sensitivity
            .path_key(&absolute_file_name.as_path());
        let node = paths.ensure(&path);
        if let Some(RequestEntry::File(existing)) = &node.entry {
            return Err(format!(
                "duplicate request filesystem file path {:?} and {:?}",
                existing.file_name, absolute_file_name
            ));
        }
        node.entry = Some(RequestEntry::File(Arc::new(pathtree::RequestFile {
            file_name: absolute_file_name.clone(),
            content: content.clone(),
        })));
        result.register_directory(&mut paths, absolute_file_name.directory());
    }
    let mut seen_directories: FxHashSet<PathKey> = FxHashSet::default();
    let mut listed_directories: Vec<RootedDirectoryPath> = Vec::new();
    for (directory_name, entries) in &params.directories {
        let absolute_directory_name =
            rooted_directory_path_from_path(result.to_absolute_path(directory_name));
        let path = result
            .case_sensitivity
            .path_key(&absolute_directory_name.as_path());
        let node = paths.ensure(&path);
        if !seen_directories.insert(path.clone()) {
            return Err(format!(
                "duplicate request filesystem directory path {:?}",
                absolute_directory_name
            ));
        }
        if !matches!(node.entry, Some(RequestEntry::File(_))) {
            node.entry = Some(RequestEntry::Directory(Arc::new(
                pathtree::RequestDirectory {
                    directory_name: absolute_directory_name.clone(),
                    listing: Some(Entries {
                        files: entries.files.clone(),
                        directories: entries.directories.clone(),
                        symlinks: None,
                    }),
                },
            )));
        }
        result.register_directory(
            &mut paths,
            absolute_directory_name.as_path().directory(),
        );
        for child in &entries.directories {
            listed_directories.push(absolute_directory_name.resolve_directory(child));
        }
    }
    for link_name in params.symlinks.keys() {
        result.register_directory(&mut paths, result.to_absolute_path(link_name).directory());
    }
    let mut seen_symlinks: FxHashMap<PathKey, RootedPath> = FxHashMap::default();
    for (link_name, symlink) in &params.symlinks {
        let absolute_link_name = result.to_absolute_path(link_name);
        let path = result.case_sensitivity.path_key(&absolute_link_name);
        let node = paths.ensure(&path);
        if let Some(existing) = seen_symlinks.get(&path) {
            return Err(format!(
                "duplicate request filesystem symlink path {:?} and {:?}",
                existing, absolute_link_name
            ));
        }
        seen_symlinks.insert(path, absolute_link_name.clone());
        let target_directory = absolute_link_name.directory();
        let absolute_target = result.to_absolute_path_from(&symlink.target, &target_directory);
        if node.entry.is_none() {
            node.entry = Some(RequestEntry::Symlink(Arc::new(RequestSymlink {
                link_name: absolute_link_name,
                target: absolute_target,
                host: symlink.host,
            })));
        }
    }
    for directory_name in listed_directories {
        result.register_directory(&mut paths, directory_name);
    }
    for path in &params.removed_paths {
        paths
            .ensure(&result.case_sensitivity.path_key(&result.to_absolute_path(path)))
            .fallback = RequestFallback::Missing;
    }
    result.paths = Arc::new(compose_request_paths(
        None,
        &paths,
        RequestFallback::Allowed,
        result.case_sensitivity,
    ));
    Ok(result)
}

impl RequestFileSystem {
    fn base_file_system(&self) -> &Arc<dyn Vfs> {
        &self.base
    }

    /// `s.applyTo`
    fn apply_to(mut self, base: RequestFileSystem) -> RequestFileSystem {
        self.paths = Arc::new(compose_request_paths(
            Some(base.paths.as_ref()),
            &self.paths,
            RequestFallback::Allowed,
            self.case_sensitivity,
        ));
        self.kind = base.kind;
        self.base = base.base;
        self.base_source = base.base_source;
        self
    }

    /// `s.blocksFallback`
    fn blocks_fallback(&self, path: &RootedPath) -> bool {
        let (_, fallback) = self.paths.lookup(&self.case_sensitivity.path_key(path));
        fallback == RequestFallback::Missing
    }

    /// `s.toAbsolutePath`
    fn to_absolute_path(&self, path: &str) -> RootedPath {
        self.to_absolute_path_from(path, &self.current_directory)
    }

    /// `s.toAbsolutePathFrom`
    fn to_absolute_path_from(
        &self,
        path: &str,
        current_directory: &RootedDirectoryPath,
    ) -> RootedPath {
        to_rooted_path(path, current_directory)
    }

    /// `s.registerDirectory`
    fn register_directory(
        &self,
        paths: &mut RequestPathNode,
        mut directory_name: RootedDirectoryPath,
    ) {
        loop {
            let node = paths.ensure(&self.case_sensitivity.path_key(&directory_name.as_path()));
            if node.entry.is_some() {
                return;
            }
            node.entry = Some(RequestEntry::Directory(Arc::new(
                pathtree::RequestDirectory {
                    directory_name: directory_name.clone(),
                    listing: None,
                },
            )));
            let parent_name = directory_name.as_path().directory();
            if parent_name == directory_name {
                return;
            }
            directory_name = parent_name;
        }
    }

    /// `s.resolvePath`
    fn resolve_path(&self, path: RootedPath) -> ResolvedRequestPath {
        let mut result = ResolvedRequestPath {
            path,
            followed_symlink: false,
            host: false,
            ok: true,
        };
        let mut seen: FxHashSet<PathKey> = FxHashSet::default();
        loop {
            let canonical_path = self.case_sensitivity.path_key(&result.path);
            if self.paths.contains_file_ancestor(&canonical_path) {
                result.ok = false;
                return result;
            }
            let (match_path, symlink_match) = self.paths.first_symlink(&canonical_path);
            let Some(match_) = symlink_match else {
                result.host = self.is_host_path(&result.path);
                return result;
            };
            if !seen.insert(match_path.clone()) {
                result.ok = false;
                return result;
            }
            result.followed_symlink = true;
            let (suffix, ok) = self
                .case_sensitivity
                .trim_prefix(result.path.as_string(), match_.link_name.as_string());
            if !ok {
                result.ok = false;
                return result;
            }
            result.path = rooted_path_from_absolute(&combine_paths(
                match_.target.as_string(),
                &[suffix.trim_start_matches('/')],
            ));
            if match_.host {
                result.host = true;
                return result;
            }
        }
    }

    /// `s.isHostPath`
    fn is_host_path(&self, path: &RootedPath) -> bool {
        let canonical_path = self.case_sensitivity.path_key(path);
        let mut found = false;
        self.paths.walk_symlinks(&mut |_, symlink| {
            if symlink.host
                && request_path_contains(
                    &self.case_sensitivity.path_key(&symlink.target),
                    &canonical_path,
                )
            {
                found = true;
            }
        });
        found
    }

    /// `s.aliasesForPath`
    fn aliases_for_path(&self, path: RootedPath) -> Vec<RootedPath> {
        let mut symlinks: Vec<RequestSymlink> = Vec::new();
        self.paths.walk_symlinks(&mut |_, symlink| {
            symlinks.push(symlink.clone());
        });

        let mut seen: FxHashSet<PathKey> = FxHashSet::default();
        seen.insert(self.case_sensitivity.path_key(&path));
        let mut queue = vec![path];
        let mut aliases = Vec::new();
        while let Some(candidate) = queue.first().cloned() {
            queue.remove(0);
            for symlink in &symlinks {
                let (suffix, ok) = self
                    .case_sensitivity
                    .trim_prefix(candidate.as_string(), symlink.target.as_string());
                if !ok
                    || (!suffix.is_empty()
                        && !has_trailing_directory_separator(symlink.target.as_string())
                        && !suffix.starts_with('/'))
                {
                    continue;
                }
                let alias = rooted_path_from_absolute(&combine_paths(
                    symlink.link_name.as_string(),
                    &[suffix.trim_start_matches('/')],
                ));
                let alias_path = self.case_sensitivity.path_key(&alias);
                if seen.contains(&alias_path) {
                    continue;
                }
                if !self.resolve_path(alias.clone()).ok {
                    continue;
                }
                seen.insert(alias_path);
                aliases.push(alias.clone());
                queue.push(alias);
            }
        }
        aliases
    }

    /// `s.localPathInfo` — `node.entry.(vfs.FileInfo)`: files and
    /// directories are `FileInfo`; a symlink entry reports `nil`.
    fn local_path_info(&self, path: &RootedPath) -> (Option<RequestEntry>, RequestFallback) {
        let (node, fallback) = self.paths.lookup(&self.case_sensitivity.path_key(path));
        let Some(node) = node else {
            return (None, fallback);
        };
        let info = node
            .entry
            .as_ref()
            .filter(|e| e.as_file_info().is_some())
            .cloned();
        (info, fallback)
    }

    /// `s.lookupPath`
    fn lookup_path(&self, path: RootedPath) -> RequestPathLookup {
        let (info, path_fallback) = self.local_path_info(&path);
        if info.is_some() {
            return RequestPathLookup {
                path,
                info,
                ok: true,
                ..Default::default()
            };
        }
        if path_fallback == RequestFallback::Missing {
            return RequestPathLookup::default();
        }
        let resolved = self.resolve_path(path);
        if !resolved.ok {
            return RequestPathLookup::default();
        }
        let mut result = RequestPathLookup {
            path: resolved.path.clone(),
            followed_symlink: resolved.followed_symlink,
            ok: true,
            ..Default::default()
        };
        let (resolved_info, resolved_fallback) = self.local_path_info(&resolved.path);
        if !resolved.host && resolved_info.is_some() {
            result.info = resolved_info;
        } else if resolved.host || self.kind == Kind::Layer {
            if resolved_fallback == RequestFallback::Missing {
                return RequestPathLookup::default();
            }
            result.ok = true;
            result.file_system = Some(self.base.clone());
        }
        result
    }

    /// `s.mutationPath`
    fn mutation_path(&self, path: &RootedPath) -> Option<(Arc<dyn Vfs>, RootedPath)> {
        if self.kind != Kind::Layer {
            return None;
        }
        let resolved = self.resolve_path(path.clone());
        if !resolved.ok {
            return None;
        }
        Some((self.base.clone(), resolved.path))
    }

    /// `s.getLocalEntries`
    fn get_local_entries(&self, directory_name: &RootedPath) -> (Entries, bool, bool) {
        let (node, _) = self
            .paths
            .lookup(&self.case_sensitivity.path_key(directory_name));
        let Some(node) = node else {
            return (Entries::default(), false, false);
        };
        let (entries, ok) = node.entries();
        let explicit = match &node.entry {
            Some(RequestEntry::Directory(d)) => d.listing.is_some(),
            _ => false,
        };
        (entries, explicit, ok)
    }

    /// `s.filterLocalEntries`
    fn filter_local_entries(
        &self,
        directory_name: &RootedDirectoryPath,
        entries: Entries,
    ) -> Entries {
        let mut result = clone_entries(&entries);
        let keep = |name: &str| -> bool {
            let path = directory_name.resolve_directory(name).as_path();
            let (info, _) = self.local_path_info(&path);
            if info.is_some() {
                return true;
            }
            !self.blocks_fallback(&path)
        };
        result.files.retain(|name| keep(name));
        result.directories.retain(|name| keep(name));
        if let Some(symlinks) = &mut result.symlinks {
            let dead: Vec<String> = symlinks
                .iter()
                .filter(|name| !keep(name))
                .cloned()
                .collect();
            for d in dead {
                symlinks.remove(&d);
            }
        }
        result
    }

    /// `s.removeEntries`
    fn remove_entries(&self, directory_name: &RootedDirectoryPath, entries: Entries) -> Entries {
        let mut result = clone_entries(&entries);
        let keep = |name: &str| -> bool {
            !self.blocks_fallback(&directory_name.resolve_directory(name).as_path())
        };
        result.files.retain(|name| keep(name));
        result.directories.retain(|name| keep(name));
        if let Some(symlinks) = &mut result.symlinks {
            let dead: Vec<String> = symlinks
                .iter()
                .filter(|name| !keep(name))
                .cloned()
                .collect();
            for d in dead {
                symlinks.remove(&d);
            }
        }
        result
    }

    /// `s.addSymlinkEntries`
    fn add_symlink_entries(&self, directory_name: &RootedPath, entries: Entries) -> Entries {
        let mut result = clone_entries(&entries);
        if result.symlinks.is_none() {
            result.symlinks = Some(FxHashSet::default());
        }

        let directory_path = self.case_sensitivity.path_key(directory_name);
        let mut links: Vec<RequestSymlink> = Vec::new();
        if let (Some(node), _) = self.paths.lookup(&directory_path) {
            for child in node.children.values() {
                if let Some(RequestEntry::Symlink(symlink)) = &child.entry {
                    links.push(symlink.as_ref().clone());
                }
            }
        }
        if links.is_empty() {
            return result;
        }
        for symlink in links {
            let name = symlink.link_name.base_name().to_string();
            result.files = self.delete_entry_name(result.files, &name);
            result.directories = self.delete_entry_name(result.directories, &name);
            if let Some(set) = &mut result.symlinks {
                let dead: Vec<String> = set
                    .iter()
                    .filter(|existing| self.equal_entry_names(existing, &name))
                    .cloned()
                    .collect();
                for d in dead {
                    set.remove(&d);
                }
            }
            if self.directory_exists(&rooted_directory_path_from_path(symlink.link_name.clone())) {
                result.directories.push(name.clone());
                result.symlinks.as_mut().unwrap().insert(name);
            } else if self.file_exists(&rooted_file_path_from_path(symlink.link_name.clone())) {
                result.files.push(name.clone());
                result.symlinks.as_mut().unwrap().insert(name);
            }
        }
        result.files.sort();
        result.directories.sort();
        result
    }

    /// `s.deleteEntryName`
    fn delete_entry_name(&self, mut values: Vec<String>, value: &str) -> Vec<String> {
        values.retain(|candidate| !self.equal_entry_names(candidate, value));
        values
    }

    /// `s.equalEntryNames`
    fn equal_entry_names(&self, left: &str, right: &str) -> bool {
        self.case_sensitivity.get_comparer()(left, right) == 0
    }
}

/// `vfs.FS` for `requestFileSystem`.
impl Vfs for RequestFileSystem {
    /// `CaseSensitivity`
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    /// `ReadFile`
    fn read_file(&self, file_name: &RootedFilePath) -> Option<String> {
        let lookup = self.lookup_path(file_name.as_path());
        if !lookup.ok || lookup.info_is_dir() == Some(true) {
            return None;
        }
        if let Some(fs) = &lookup.file_system {
            return fs.read_file(&rooted_file_path_from_path(lookup.path.clone()));
        }
        if let Some(RequestEntry::File(file)) = &lookup.info {
            return Some(file.content.clone());
        }
        None
    }

    /// `FileExists`
    fn file_exists(&self, file_name: &RootedFilePath) -> bool {
        let lookup = self.lookup_path(file_name.as_path());
        if !lookup.ok || lookup.info_is_dir() == Some(true) {
            return false;
        }
        lookup.info.is_some()
            || lookup.file_system.is_some_and(|fs| {
                fs.file_exists(&rooted_file_path_from_path(lookup.path.clone()))
            })
    }

    /// `DirectoryExists`
    fn directory_exists(&self, directory_name: &RootedDirectoryPath) -> bool {
        let lookup = self.lookup_path(directory_name.as_path());
        if !lookup.ok || lookup.info_is_dir() == Some(false) {
            return false;
        }
        lookup.info.is_some()
            || lookup.file_system.is_some_and(|fs| {
                fs.directory_exists(&rooted_directory_path_from_path(lookup.path.clone()))
            })
    }

    /// `GetAccessibleEntries`
    fn get_accessible_entries(&self, directory_name: &RootedDirectoryPath) -> Entries {
        let lookup = self.lookup_path(directory_name.as_path());
        if !lookup.ok || lookup.info_is_dir() == Some(false) {
            return Entries {
                symlinks: Some(FxHashSet::default()),
                ..Default::default()
            };
        }
        let mut result;
        if let Some(fs) = &lookup.file_system {
            let resolved_directory =
                rooted_directory_path_from_path(lookup.path.clone());
            result = self.remove_entries(
                &resolved_directory,
                fs.get_accessible_entries(&resolved_directory),
            );
        } else {
            let (local_entries, explicit, _) = self.get_local_entries(&lookup.path);
            result = local_entries.clone();
            if self.kind == Kind::Layer
                && !explicit
                && !self.blocks_fallback(&directory_name.as_path())
                && !self.blocks_fallback(&lookup.path)
            {
                let resolved_directory =
                    rooted_directory_path_from_path(lookup.path.clone());
                result = self.remove_entries(
                    &resolved_directory,
                    self.base_file_system().get_accessible_entries(&resolved_directory),
                );
                let equal = |l: &str, r: &str| self.equal_entry_names(l, r);
                result = merge_entries(result, &local_entries, &equal);
            }
            result = self.add_symlink_entries(&lookup.path, result);
        }
        self.filter_local_entries(directory_name, result)
    }

    /// `Realpath`
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        let lookup = self.lookup_path(path.clone());
        if !lookup.ok {
            return path.clone();
        }
        if let Some(fs) = &lookup.file_system {
            return fs.realpath(&lookup.path);
        }
        if lookup.info.is_some() || !lookup.followed_symlink {
            return lookup.path;
        }
        path.clone()
    }

    /// `WriteFile`
    fn write_file(&self, file_name: &RootedFilePath, data: &str) -> Result<(), FsError> {
        let Some((host, path)) = self.mutation_path(&file_name.as_path()) else {
            return Err(ERR_INVALID);
        };
        host.write_file(&rooted_file_path_from_path(path.clone()), data)
    }

    /// `AppendFile`
    fn append_file(&self, file_name: &RootedFilePath, data: &str) -> Result<(), FsError> {
        let Some((host, path)) = self.mutation_path(&file_name.as_path()) else {
            return Err(ERR_INVALID);
        };
        host.append_file(&rooted_file_path_from_path(path.clone()), data)
    }

    /// `Remove`
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        let Some((host, path)) = self.mutation_path(path) else {
            return Err(ERR_INVALID);
        };
        host.remove(&path)
    }

    /// `Chtimes`
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        let Some((host, path)) = self.mutation_path(path) else {
            return Err(ERR_INVALID);
        };
        host.chtimes(&path, a_time, m_time)
    }

    /// `Stat`
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn tsc_vfs::fs::FileInfo>> {
        let lookup = self.lookup_path(path.clone());
        if !lookup.ok {
            return None;
        }
        if let Some(fs) = &lookup.file_system {
            return stat_file_system(fs.as_ref(), &lookup.path);
        }
        lookup.info.and_then(|e| e.as_file_info())
    }

    /// `as_concrete` hook for the `getRequestFileSystem` downcast.
    fn as_concrete(&self) -> Option<&dyn std::any::Any> {
        Some(self)
    }
}

/// `statFileSystem`
fn stat_file_system(
    file_system: &dyn Vfs,
    path: &RootedPath,
) -> Option<Arc<dyn tsc_vfs::fs::FileInfo>> {
    if let Some(info) = file_system.stat(path) {
        return Some(info);
    }
    if file_system.directory_exists(&rooted_directory_path_from_path(path.clone())) {
        return Some(Arc::new(pathtree::RequestDirectory {
            directory_name: rooted_directory_path_from_path(path.clone()),
            listing: None,
        }));
    }
    if file_system.file_exists(&rooted_file_path_from_path(path.clone())) {
        return Some(Arc::new(pathtree::RequestFile {
            file_name: rooted_file_path_from_path(path.clone()),
            content: String::new(),
        }));
    }
    None
}

/// `FileHandleSource` — `GetFile`/`GetFileByPath`.
impl FileHandleSource for RequestFileSystem {
    /// `GetFile`
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.get_file_by_path(
            file_name,
            &self.case_sensitivity.path_key(&file_name.as_path()),
        )
    }

    /// `GetFileByPath`
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        _path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        let lookup = self.lookup_path(file_name.as_path());
        if !lookup.ok || lookup.info_is_dir() == Some(true) {
            return None;
        }
        if let Some(fs) = &lookup.file_system {
            let fs = fs.clone();
            // `lookup.fileSystem.(project.FileHandleSource)` — the file
            // system is always `s.base`, so its source twin is
            // `s.base_source`.
            if let Some(source) = &self.base_source {
                return source.get_file(&rooted_file_path_from_path(lookup.path.clone()));
            }
            if let Some(content) =
                fs.read_file(&rooted_file_path_from_path(lookup.path.clone()))
            {
                return Some(new_cached_file_handle(file_name.clone(), content));
            }
            return None;
        }
        if let Some(RequestEntry::File(file)) = &lookup.info {
            return Some(new_cached_file_handle(file_name.clone(), file.content.clone()));
        }
        None
    }
}

/// `project.LayeredFileSystem` — `Overlays` carries forward only overlays
/// whose paths still resolve locally in this filesystem.
impl LayeredFileSystem for RequestFileSystem {
    /// `Overlays` — `s.base.(project.LayeredFileSystem)` filters the
    /// base's overlays to those still resolving locally.
    fn overlays(&self) -> FxHashMap<PathKey, Arc<Overlay>> {
        let Some(layered_base) = as_layered(&self.base) else {
            return FxHashMap::default();
        };
        let mut result = FxHashMap::default();
        for (path, overlay) in layered_base.overlays() {
            let lookup = self.lookup_path(overlay.file_name().as_path());
            if lookup.file_system.is_none()
                || self.case_sensitivity.path_key(&lookup.path) != path
            {
                continue;
            }
            result.insert(path, overlay);
        }
        result
    }

    /// `as_rebasable` — `requestFileSystem` is a `RebasableFileSystem`.
    fn as_rebasable(&self) -> Option<Arc<dyn RebasableFileSystem>> {
        Some(Arc::new(self.clone()))
    }

    /// `ExpandFileChanges` — `FileChangeExpander`.
    fn expand_file_changes(&self, summary: FileChangeSummary) -> FileChangeSummary {
        filechanges::expand_file_changes(self, summary)
    }

    /// `Any` handle — `s.(*requestFileSystem)` assertions.
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

/// `fs.(project.LayeredFileSystem)` — downcast for layered bases.
/// `as_concrete` yields the concrete type; the layered impls in this
/// workspace are `OverlayFs` and `RequestFileSystem`.
fn as_layered(fs: &Arc<dyn Vfs>) -> Option<&dyn LayeredFileSystem> {
    let concrete = fs.as_concrete()?;
    if let Some(r) = concrete.downcast_ref::<RequestFileSystem>() {
        return Some(r);
    }
    if let Some(o) = concrete.downcast_ref::<OverlayFs>() {
        return Some(o);
    }
    None
}

/// `project.RebasableFileSystem`.
impl RebasableFileSystem for RequestFileSystem {
    /// `BaseFileSystem`
    fn base_file_system(&self) -> LayeredFsInput {
        LayeredFsInput::Plain(self.base.clone())
    }

    /// `WithBaseFileSystem`
    fn with_base_file_system(
        &self,
        base: Arc<dyn LayeredFileSystem>,
    ) -> Arc<dyn LayeredFileSystem> {
        let mut clone = self.clone();
        // `LayeredFileSystem` is a `FileHandleSource` — the source twin of
        // the new base is the base itself (trait upcast).
        clone.base_source = Some(base.clone());
        clone.base = layered_as_vfs(base);
        Arc::new(clone)
    }
}
