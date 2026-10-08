// Ported from tsc/internal/vfs/walkdir.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashSet;
use std::sync::Arc;
use std::time::SystemTime;

use tsc_tspath::{
    RootedDirectoryPath, RootedPath, rooted_directory_path_from_path,
};

use crate::fs::{
    DirEntry, FileInfo, FileMode, FsError, MODE_DIR, MODE_SYMLINK, file_info_to_dir_entry,
};
use crate::vfs::{ERR_NOT_EXIST, Vfs, WalkDirFunc};

/// walk_dir calls walk_fn for root and each accessible descendant in lexical order.
/// Symbolic links are reported but not followed. Directory read failures are
/// indistinguishable from empty directories because [Vfs::get_accessible_entries]
/// does not return errors. The FileInfo returned by DirEntry::info for a symbolic
/// link contains only its name and mode because [Vfs] does not provide lstat.
/// Using DirEntry::info() requires the FS to implement stat().
pub fn walk_dir(
    file_system: &Arc<dyn Vfs>,
    root: &RootedPath,
    walk_fn: &mut WalkDirFunc<'_>,
) -> Result<(), FsError> {
    let root_path = root;
    let root_info = file_system.stat(root_path);
    let Some(root_info) = root_info else {
        return normalize_walk_dir_error(walk_fn(
            root_path,
            None,
            Some(&ERR_NOT_EXIST),
        ));
    };

    let case_sensitivity = file_system.case_sensitivity();
    let (root_prefix, _) = root_path.root_and_relative_path();
    let same_root = |path: &RootedPath| {
        let (path_root, _) = path.root_and_relative_path();
        case_sensitivity.compare_paths(&path_root.as_path(), &root_prefix.as_path()) == 0
    };
    let equivalent =
        |left: &RootedPath, right: &RootedPath| case_sensitivity.compare_paths(left, right) == 0;
    let canonicalize = |path: &RootedPath| case_sensitivity.path_key(path);

    let mut visited: HashSet<tsc_tspath::PathKey> = HashSet::new();

    // PORT: `visit` is a free function taking the captured context by
    // reference because Rust closures cannot be recursive.
    struct VisitCtx<'a> {
        file_system: &'a Arc<dyn Vfs>,
        visited: &'a mut HashSet<tsc_tspath::PathKey>,
        walk_fn: &'a mut WalkDirFunc<'a>,
        canonicalize: &'a dyn Fn(&RootedPath) -> tsc_tspath::PathKey,
        equivalent: &'a dyn Fn(&RootedPath, &RootedPath) -> bool,
        same_root: &'a dyn Fn(&RootedPath) -> bool,
    }

    fn visit(
        ctx: &mut VisitCtx<'_>,
        path: &RootedPath,
        entry: &Arc<dyn DirEntry>,
        realpath: &RootedPath,
    ) -> Result<(), FsError> {
        if entry.is_dir() {
            let canonical_realpath = (ctx.canonicalize)(realpath);
            if ctx.visited.contains(&canonical_realpath) {
                return Ok(());
            }
            ctx.visited.insert(canonical_realpath);
        }

        if let Err(err) = (ctx.walk_fn)(path, Some(&**entry), None) {
            if err.is_skip_dir() && entry.is_dir() {
                return Ok(());
            }
            return Err(err);
        }
        if !entry.is_dir() {
            return Ok(());
        }

        let directory = rooted_directory_path_from_path(path.clone());
        let entries = ctx.file_system.get_accessible_entries(&directory);
        let directories: HashSet<&str> =
            entries.directories.iter().map(String::as_str).collect();
        let mut names: Vec<String> = entries
            .directories
            .iter()
            .cloned()
            .chain(entries.files.iter().cloned())
            .collect();
        names.sort();
        for name in names {
            let mut mode = FileMode(0);
            if directories.contains(name.as_str()) {
                mode = MODE_DIR;
            }
            let child_path: RootedPath = if mode.is_dir() {
                directory.resolve_directory(&name).as_path()
            } else {
                directory.resolve_file(&name).as_path()
            };
            if !(ctx.same_root)(&child_path) {
                continue;
            }

            let mut child_realpath = RootedPath::default();
            let mut is_symlink = false;
            if let Some(symlinks) = &entries.symlinks {
                is_symlink = symlinks.contains(&name);
                if !is_symlink && mode.is_dir() {
                    child_realpath = rooted_directory_path_from_path(realpath.clone())
                        .resolve_directory(&name)
                        .as_path();
                }
            } else {
                child_realpath = ctx.file_system.realpath(&child_path);
                let real_directory = rooted_directory_path_from_path(realpath.clone());
                let expected_realpath = if mode.is_dir() {
                    real_directory.resolve_directory(&name).as_path()
                } else {
                    real_directory.resolve_file(&name).as_path()
                };
                is_symlink = !(ctx.equivalent)(&child_realpath, &expected_realpath);
            }
            if is_symlink {
                mode = MODE_SYMLINK;
            }
            let child_entry: Arc<dyn DirEntry> = Arc::new(WalkDirEntry {
                file_system: ctx.file_system.clone(),
                path: child_path.clone(),
                name: name.clone(),
                mode,
            });
            if !mode.is_dir() {
                if let Err(err) = visit(ctx, &child_path, &child_entry, &RootedPath::default()) {
                    if err.is_skip_dir() {
                        return Ok(());
                    }
                    return Err(err);
                }
                continue;
            }

            if child_realpath.as_string().is_empty() {
                child_realpath = ctx.file_system.realpath(&child_path);
            }
            if let Err(err) = visit(ctx, &child_path, &child_entry, &child_realpath) {
                if err.is_skip_dir() {
                    return Ok(());
                }
                return Err(err);
            }
        }
        Ok(())
    }

    let mut root_entry: Arc<dyn DirEntry> = file_info_to_dir_entry(root_info);
    let root_realpath = file_system.realpath(root_path);
    if root_path != &root_prefix.as_path() {
        let parent = root_path.directory();
        let expected_realpath = rooted_directory_path_from_path(
            file_system.realpath(&parent.as_path()),
        )
        .resolve_directory(&root_path.base_name())
        .as_path();
        if !equivalent(&root_realpath, &expected_realpath) {
            root_entry = Arc::new(WalkDirEntry {
                file_system: file_system.clone(),
                path: root_path.clone(),
                name: root_path.base_name().to_string(),
                mode: MODE_SYMLINK,
            });
        }
    }

    let mut ctx = VisitCtx {
        file_system,
        visited: &mut visited,
        walk_fn,
        canonicalize: &canonicalize,
        equivalent: &equivalent,
        same_root: &same_root,
    };
    normalize_walk_dir_error(visit(&mut ctx, root_path, &root_entry, &root_realpath))
}

fn normalize_walk_dir_error(err: Result<(), FsError>) -> Result<(), FsError> {
    match err {
        Err(e) if e.is_skip_dir() || e.is_skip_all() => Ok(()),
        other => other,
    }
}

struct WalkDirEntry {
    file_system: Arc<dyn Vfs>,
    path: RootedPath,
    name: String,
    mode: FileMode,
}

impl DirEntry for WalkDirEntry {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn is_dir(&self) -> bool {
        self.mode.is_dir()
    }

    fn type_(&self) -> FileMode {
        self.mode.type_()
    }

    fn info(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        if self.mode & MODE_SYMLINK != FileMode(0) {
            return Ok(Arc::new(WalkDirFileInfo {
                name: self.name.clone(),
                mode: self.mode,
            }));
        }
        match self.file_system.stat(&self.path) {
            None => Err(ERR_NOT_EXIST),
            Some(info) => Ok(info),
        }
    }
}

struct WalkDirFileInfo {
    name: String,
    mode: FileMode,
}

impl FileInfo for WalkDirFileInfo {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn size(&self) -> i64 {
        0
    }
    fn mode(&self) -> FileMode {
        self.mode
    }
    fn mod_time(&self) -> SystemTime {
        SystemTime::UNIX_EPOCH // PORT: Go uses time.Time{}; UNIX_EPOCH is Rust's zero-ish time.
    }
    fn is_dir(&self) -> bool {
        self.mode.is_dir()
    }
    fn sys(&self) -> Option<Arc<dyn std::any::Any + Send + Sync>> {
        None
    }
}
