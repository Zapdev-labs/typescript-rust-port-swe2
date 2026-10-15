// Ported from tsc/internal/api/requestfilesystem/pathtree.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `requestEntry` (Go interface) → the [`RequestEntry`] enum of `Arc`s;
// `*requestPathNode` → owned `RequestPathNode` values inside a `FxHashMap`.
// `vfs.FileInfo`/`vfs.DirEntry` assertions become `Arc<dyn FileInfo>`.
// `maps.Clone(children)` → `children.clone()`; `slices.DeleteFunc` →
// `retain`; `slices.ContainsFunc` → `iter().any`.

use std::sync::Arc;
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::Entries;
use tsc_vfs::fs::{FileMode, MODE_DIR};

/// `requestFallback`
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RequestFallback {
    /// `requestFallbackInherit`
    #[default]
    Inherit,
    /// `requestFallbackAllowed`
    Allowed,
    /// `requestFallbackMissing`
    Missing,
}

/// `requestFile`
pub struct RequestFile {
    pub file_name: RootedFilePath,
    pub content: String,
}

/// `requestSymlink`
#[derive(Clone)]
pub struct RequestSymlink {
    pub link_name: RootedPath,
    pub target: RootedPath,
    pub host: bool,
}

/// `requestDirectory`
#[derive(Clone)]
pub struct RequestDirectory {
    pub directory_name: RootedDirectoryPath,
    /// `listing` — `Some` is an explicit complete listing; `None` means the
    /// directory's structure is implied by children.
    pub listing: Option<Entries>,
}

/// `requestEntry` — the Go interface becomes an enum of `Arc`s so nodes can
/// share entries with the composed trees that reference them.
#[derive(Clone)]
pub enum RequestEntry {
    File(Arc<RequestFile>),
    Symlink(Arc<RequestSymlink>),
    Directory(Arc<RequestDirectory>),
}

impl RequestEntry {
    /// `node.entry.(vfs.FileInfo)` — files and directories satisfy
    /// `FileInfo`; symlinks do not (`nil`).
    pub fn as_file_info(&self) -> Option<Arc<dyn tsc_vfs::fs::FileInfo>> {
        match self {
            RequestEntry::File(f) => Some(f.clone()),
            RequestEntry::Directory(d) => Some(d.clone()),
            RequestEntry::Symlink(_) => None,
        }
    }

    /// `info.IsDir()` — only meaningful when `as_file_info` is `Some`.
    pub fn is_dir(&self) -> bool {
        matches!(self, RequestEntry::Directory(_))
    }
}

/// `requestFile`'s `fs.FileInfo` implementation.
impl tsc_vfs::fs::FileInfo for RequestFile {
    /// `Name`
    fn name(&self) -> String {
        self.file_name.base_name().to_string()
    }
    /// `Size`
    fn size(&self) -> i64 {
        self.content.len() as i64
    }
    /// `Mode` — `0o444`
    fn mode(&self) -> FileMode {
        FileMode(0o444)
    }
    /// `ModTime` — `time.Time{}`
    fn mod_time(&self) -> SystemTime {
        SystemTime::UNIX_EPOCH
    }
    /// `IsDir`
    fn is_dir(&self) -> bool {
        false
    }
    /// `Sys`
    fn sys(&self) -> Option<Arc<dyn std::any::Any + Send + Sync>> {
        None
    }
}

/// `requestDirectory`'s `fs.FileInfo` implementation.
impl tsc_vfs::fs::FileInfo for RequestDirectory {
    /// `Name`
    fn name(&self) -> String {
        self.directory_name.base_name().to_string()
    }
    /// `Size`
    fn size(&self) -> i64 {
        0
    }
    /// `Mode` — `fs.ModeDir | 0o555`
    fn mode(&self) -> FileMode {
        FileMode(MODE_DIR.0 | 0o555)
    }
    /// `ModTime` — `time.Time{}`
    fn mod_time(&self) -> SystemTime {
        SystemTime::UNIX_EPOCH
    }
    /// `IsDir`
    fn is_dir(&self) -> bool {
        true
    }
    /// `Sys`
    fn sys(&self) -> Option<Arc<dyn std::any::Any + Send + Sync>> {
        None
    }
}

/// `requestPathNode`
#[derive(Clone, Default)]
pub struct RequestPathNode {
    pub entry: Option<RequestEntry>,
    pub fallback: RequestFallback,
    pub children: FxHashMap<PathKey, RequestPathNode>,
    pub has_symlinks: bool,
}

impl RequestPathNode {
    /// `node.replacesSubtree` — files and symlinks replace the subtree.
    pub fn replaces_subtree(&self) -> bool {
        matches!(
            self.entry,
            Some(RequestEntry::File(_)) | Some(RequestEntry::Symlink(_))
        )
    }
}

/// `requestPathAncestors` — the chain from the root to `path`, root first.
pub fn request_path_ancestors(path: &PathKey) -> Vec<PathKey> {
    let mut paths = Vec::new();
    let mut path = path.clone();
    loop {
        paths.push(path.clone());
        let parent = path.parent();
        if parent == path {
            break;
        }
        path = parent;
    }
    paths.reverse();
    paths
}

impl RequestPathNode {
    /// `node.ensure`
    pub fn ensure(&mut self, path: &PathKey) -> &mut RequestPathNode {
        let mut node = self;
        for ancestor in request_path_ancestors(path) {
            node = node.children.entry(ancestor).or_default();
        }
        node
    }

    /// `node.lookup` — the node at `path` plus the nearest non-`Inherit`
    /// fallback encountered along the way (inclusive).
    pub fn lookup(&self, path: &PathKey) -> (Option<&RequestPathNode>, RequestFallback) {
        let mut fallback = RequestFallback::Inherit;
        let mut node = Some(self);
        for ancestor in request_path_ancestors(path) {
            let Some(n) = node else { break };
            if n.fallback != RequestFallback::Inherit {
                fallback = n.fallback;
            }
            node = n.children.get(&ancestor);
        }
        if let Some(n) = node {
            if n.fallback != RequestFallback::Inherit {
                fallback = n.fallback;
            }
        }
        (node, fallback)
    }

    /// `node.walkSymlinks`
    pub fn walk_symlinks(&self, visit: &mut impl FnMut(&PathKey, &RequestSymlink)) {
        if !self.has_symlinks {
            return;
        }
        for (path, child) in &self.children {
            if let Some(RequestEntry::Symlink(symlink)) = &child.entry {
                visit(path, symlink);
            }
            child.walk_symlinks(visit);
        }
    }

    /// `node.entries`
    pub fn entries(&self) -> (Entries, bool) {
        let Some(RequestEntry::Directory(directory)) = &self.entry else {
            return (Entries::default(), false);
        };
        if let Some(listing) = &directory.listing {
            return (clone_entries(listing), true);
        }
        let mut entries = Entries::default();
        for child in self.children.values() {
            match &child.entry {
                Some(RequestEntry::File(file)) => {
                    entries.files.push(file.file_name.base_name().to_string());
                }
                Some(RequestEntry::Directory(dir)) => {
                    entries.directories.push(dir.directory_name.base_name().to_string());
                }
                _ => {}
            }
        }
        entries.files.sort();
        entries.directories.sort();
        (entries, true)
    }

    /// `node.firstSymlink`
    pub fn first_symlink(&self, path: &PathKey) -> (PathKey, Option<Arc<RequestSymlink>>) {
        let mut node = Some(self);
        for ancestor in request_path_ancestors(path) {
            let Some(n) = node else { break };
            node = n.children.get(&ancestor);
            if let Some(n) = node {
                if let Some(RequestEntry::Symlink(symlink)) = &n.entry {
                    return (ancestor, Some(symlink.clone()));
                }
            }
        }
        (PathKey::default(), None)
    }

    /// `node.containsFileAncestor`
    pub fn contains_file_ancestor(&self, path: &PathKey) -> bool {
        let mut node = Some(self);
        for ancestor in request_path_ancestors(path) {
            let Some(n) = node else { return false };
            node = n.children.get(&ancestor);
            if ancestor != *path {
                if let Some(n) = node {
                    if matches!(n.entry, Some(RequestEntry::File(_))) {
                        return true;
                    }
                }
            }
        }
        false
    }
}

/// `composeRequestPaths` — merge `overlay` onto `base`, producing a fresh
/// tree; nodes under an `Inherit` boundary keep their inherited `fallback`.
pub fn compose_request_paths(
    base: Option<&RequestPathNode>,
    overlay: &RequestPathNode,
    fallback: RequestFallback,
    case_sensitivity: CaseSensitivity,
) -> RequestPathNode {
    let mut fallback = fallback;
    let mut base = base;
    if overlay.fallback != RequestFallback::Inherit {
        fallback = overlay.fallback;
        base = None;
    }
    if overlay.replaces_subtree() {
        base = None;
    }
    let mut result = base.cloned().unwrap_or_default();
    result.children = result.children.clone();
    if overlay.fallback != RequestFallback::Inherit || overlay.replaces_subtree() {
        result.fallback = fallback;
    }
    let previous_directory = match &result.entry {
        Some(RequestEntry::Directory(d)) => Some(d.clone()),
        _ => None,
    };
    let overlay_directory = match &overlay.entry {
        Some(RequestEntry::Directory(d)) => Some(d.clone()),
        _ => None,
    };
    if let Some(overlay_entry) = &overlay.entry {
        // `overlayDirectory.listing == nil && previousDirectory != nil` —
        // the overlay directory inherits the base's explicit listing.
        result.entry = Some(match overlay_entry {
            RequestEntry::Directory(od)
                if od.listing.is_none() && previous_directory.is_some() =>
            {
                RequestEntry::Directory(Arc::new(RequestDirectory {
                    directory_name: od.directory_name.clone(),
                    listing: previous_directory.as_ref().unwrap().listing.clone(),
                }))
            }
            _ => overlay_entry.clone(),
        });
    }
    for (path, child) in &overlay.children {
        result.children.insert(
            path.clone(),
            compose_request_paths(
                result.children.get(path),
                child,
                fallback,
                case_sensitivity,
            ),
        );
    }
    if let Some(RequestEntry::Directory(directory)) = &result.entry {
        if directory.listing.is_some()
            && overlay_directory.as_ref().is_none_or(|od| od.listing.is_none())
        {
            let mut entries = clone_entries(directory.listing.as_ref().unwrap());
            let equal = |left: &str, right: &str| {
                case_sensitivity.get_comparer()(left, right) == 0
            };
            for (path, child) in &overlay.children {
                let name = path.base_name();
                if child.fallback == RequestFallback::Missing || child.replaces_subtree() {
                    entries.files.retain(|entry| !equal(entry, name));
                    entries.directories.retain(|entry| !equal(entry, name));
                    if let Some(symlinks) = &mut entries.symlinks {
                        symlinks.retain(|entry| !equal(entry, name));
                    }
                }
                match &child.entry {
                    Some(RequestEntry::File(file)) => {
                        let overlay_entries = Entries {
                            files: vec![file.file_name.base_name().to_string()],
                            ..Default::default()
                        };
                        entries = merge_entries(entries, &overlay_entries, &equal);
                    }
                    Some(RequestEntry::Directory(dir)) => {
                        let overlay_entries = Entries {
                            directories: vec![dir.directory_name.base_name().to_string()],
                            ..Default::default()
                        };
                        entries = merge_entries(entries, &overlay_entries, &equal);
                    }
                    _ => {}
                }
            }
            result.entry = Some(RequestEntry::Directory(Arc::new(RequestDirectory {
                directory_name: directory.directory_name.clone(),
                listing: Some(entries),
            })));
        }
    }
    result.has_symlinks = matches!(result.entry, Some(RequestEntry::Symlink(_)));
    for child in result.children.values() {
        result.has_symlinks = result.has_symlinks || child.has_symlinks;
    }
    result
}

/// `cloneEntries`
pub fn clone_entries(entries: &Entries) -> Entries {
    entries.clone()
}

/// `mergeEntries`
pub fn merge_entries(
    base: Entries,
    overlay: &Entries,
    equal: &dyn Fn(&str, &str) -> bool,
) -> Entries {
    let mut result = clone_entries(&base);
    if result.symlinks.is_none() {
        result.symlinks = Some(Default::default());
    }
    // `deleteSymlink` — remove every symlink name equal to `name`.
    let delete_symlink = |result: &mut Entries, name: &str| {
        if let Some(set) = &mut result.symlinks {
            let dead: Vec<String> = set
                .iter()
                .filter(|existing| equal(existing, name))
                .cloned()
                .collect();
            for d in dead {
                set.remove(&d);
            }
        }
    };
    for name in &overlay.files {
        // `addFile`
        result.directories.retain(|value| !equal(value, name));
        if !result.files.iter().any(|value| equal(value, name)) {
            result.files.push(name.clone());
        }
        delete_symlink(&mut result, name);
    }
    for name in &overlay.directories {
        // `addDirectory`
        result.files.retain(|value| !equal(value, name));
        if !result.directories.iter().any(|value| equal(value, name)) {
            result.directories.push(name.clone());
        }
        delete_symlink(&mut result, name);
    }
    if let Some(overlay_symlinks) = &overlay.symlinks {
        for name in overlay_symlinks {
            result.symlinks.as_mut().unwrap().insert(name.clone());
        }
    }
    result.files.sort();
    result.directories.sort();
    result
}

/// `requestPathContains`
pub fn request_path_contains(parent: &PathKey, path: &PathKey) -> bool {
    parent.contains_path(path)
}
