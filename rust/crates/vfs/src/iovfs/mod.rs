// Ported from tsc/internal/vfs/iovfs/iofs.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;
use std::time::SystemTime;

use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{self, FileInfo, FileMode, Fs, FsError};
use crate::internal::Common;
use crate::vfs::{Entries, Vfs};

/// RealpathFS is iovfs.RealpathFS: an fs.FS that can resolve real paths.
pub trait RealpathFs: Fs {
    fn realpath(&self, path: &str) -> Result<String, FsError>;
}

/// WritableFS is iovfs.WritableFS: an fs.FS that supports mutation.
pub trait WritableFs: Fs {
    fn write_file(&self, path: &str, data: &str, perm: FileMode) -> Result<(), FsError>;
    fn append_file(&self, path: &str, data: &str, perm: FileMode) -> Result<(), FsError>;
    fn mkdir_all(&self, path: &str, perm: FileMode) -> Result<(), FsError>;
    /// Removes `path` and all its contents. Will return the first error it encounters.
    fn remove(&self, path: &str) -> Result<(), FsError>;
    fn chtimes(&self, path: &str, a_time: SystemTime, m_time: SystemTime)
    -> Result<(), FsError>;
}

/// FsWithSys is iovfs.FsWithSys.
pub trait FsWithSys: Vfs {
    fn fsys(&self) -> Arc<dyn Fs>;
}

/// From creates a new FS from an [fs::Fs].
///
/// For paths like `c:/foo/bar`, fsys will be used as though it's rooted at `/` and the path is `/c:/foo/bar`.
///
/// If the provided [Fs] implements [RealpathFs], it will be used to implement the realpath method.
/// If the provided [Fs] implements [WritableFs], it will be used to implement the write_file method.
///
/// From does not actually handle case-insensitivity; ensure the passed in [Fs]
/// respects case-insensitive file names if needed. Consider using [crate::vfstest::from_map] for testing.
///
/// PORT: returns the concrete [IoFs] so callers can coerce it to
/// `Arc<dyn Vfs>` or `Arc<dyn FsWithSys>` (Go returns the interface type).
pub fn from(fsys: Arc<dyn Fs>, case_sensitivity: CaseSensitivity) -> Arc<IoFs> {
    let realpath: Arc<dyn Fn(&str) -> Result<String, FsError> + Send + Sync>;
    if let Some(realpath_fs) = fsys.as_realpath_fs() {
        // PORT: the closure captures the trait object, equivalent to Go's
        // `fsys.(RealpathFS)` re-assertion inside the closure.
        let _ = realpath_fs;
        let inner = fsys.clone();
        realpath = Arc::new(move |path: &str| {
            let fsys = inner.as_realpath_fs().expect("checked above");
            let rest = path.strip_prefix('/');
            let (rest, had_slash) = match rest {
                Some(rest) => (rest, true),
                None => (path, false),
            };
            let rp = fsys.realpath(rest)?;
            if had_slash {
                return Ok(format!("/{}", rp));
            }
            Ok(rp)
        });
    } else {
        realpath = Arc::new(|path: &str| Ok(path.to_string()));
    }

    let write_file: Arc<dyn Fn(&str, &str) -> Result<(), FsError> + Send + Sync>;
    let append_file: Arc<dyn Fn(&str, &str) -> Result<(), FsError> + Send + Sync>;
    let mkdir_all: Arc<dyn Fn(&str) -> Result<(), FsError> + Send + Sync>;
    let remove: Arc<dyn Fn(&str) -> Result<(), FsError> + Send + Sync>;
    let chtimes: Arc<dyn Fn(&str, SystemTime, SystemTime) -> Result<(), FsError> + Send + Sync>;
    if fsys.as_writable_fs().is_some() {
        let wfs = fsys.clone();
        write_file = Arc::new(move |path: &str, content: &str| {
            let fsys = wfs.as_writable_fs().expect("checked above");
            let rest = path.strip_prefix('/').unwrap_or(path);
            fsys.write_file(rest, content, FileMode(0o666))
        });
        let wfs = fsys.clone();
        append_file = Arc::new(move |path: &str, content: &str| {
            let fsys = wfs.as_writable_fs().expect("checked above");
            let rest = path.strip_prefix('/').unwrap_or(path);
            fsys.append_file(rest, content, FileMode(0o666))
        });
        let wfs = fsys.clone();
        mkdir_all = Arc::new(move |path: &str| {
            let fsys = wfs.as_writable_fs().expect("checked above");
            let rest = path.strip_prefix('/').unwrap_or(path);
            fsys.mkdir_all(rest, FileMode(0o777))
        });
        let wfs = fsys.clone();
        remove = Arc::new(move |path: &str| {
            let fsys = wfs.as_writable_fs().expect("checked above");
            let rest = path.strip_prefix('/').unwrap_or(path);
            fsys.remove(rest)
        });
        let wfs = fsys.clone();
        chtimes = Arc::new(move |path: &str, a_time: SystemTime, m_time: SystemTime| {
            let fsys = wfs.as_writable_fs().expect("checked above");
            let rest = path.strip_prefix('/').unwrap_or(path);
            fsys.chtimes(rest, a_time, m_time)
        });
    } else {
        write_file = Arc::new(|_: &str, _: &str| -> Result<(), FsError> {
            panic!("writeFile not supported")
        });
        append_file = Arc::new(|_: &str, _: &str| -> Result<(), FsError> {
            panic!("appendFile not supported")
        });
        mkdir_all = Arc::new(|_: &str| -> Result<(), FsError> {
            panic!("mkdirAll not supported")
        });
        remove = Arc::new(|_: &str| -> Result<(), FsError> { panic!("remove not supported") });
        chtimes = Arc::new(
            |_: &str, _: SystemTime, _: SystemTime| -> Result<(), FsError> {
                panic!("chtimes not supported")
            },
        );
    }

    let root_fs = fsys.clone();
    Arc::new(IoFs {
        common: Common {
            root_for: Arc::new(move |root: &str| {
                if root == "/" {
                    return Some(root_fs.clone());
                }

                let p = tsc_tspath::remove_trailing_directory_separator(root);
                match fs::sub(&root_fs, p) {
                    Ok(sub) => Some(sub),
                    Err(err) => {
                        if tsc_tspath::is_url(root) {
                            return None;
                        }
                        panic!(
                            "vfs: failed to create sub file system for {}: {}",
                            fs::go_quote(p),
                            err
                        );
                    }
                }
            }),
            is_reparse_point: None,
        },
        case_sensitivity,
        realpath,
        write_file,
        append_file,
        mkdir_all,
        remove,
        chtimes,
        fsys,
    })
}

/// IoFs is iovfs.ioFS.
pub struct IoFs {
    common: Common,

    case_sensitivity: CaseSensitivity,
    realpath: Arc<dyn Fn(&str) -> Result<String, FsError> + Send + Sync>,
    write_file: Arc<dyn Fn(&str, &str) -> Result<(), FsError> + Send + Sync>,
    append_file: Arc<dyn Fn(&str, &str) -> Result<(), FsError> + Send + Sync>,
    mkdir_all: Arc<dyn Fn(&str) -> Result<(), FsError> + Send + Sync>,
    remove: Arc<dyn Fn(&str) -> Result<(), FsError> + Send + Sync>,
    chtimes: Arc<dyn Fn(&str, SystemTime, SystemTime) -> Result<(), FsError> + Send + Sync>,
    fsys: Arc<dyn Fs>,
}

impl IoFs {
    fn write_file_ensuring_dir(
        &self,
        path: &RootedFilePath,
        content: &str,
        write: &Arc<dyn Fn(&str, &str) -> Result<(), FsError> + Send + Sync>,
    ) -> Result<(), FsError> {
        let path_string = path.as_string();
        if write(path_string, content).is_ok() {
            return Ok(());
        }
        (self.mkdir_all)(path.directory().as_string())?;
        write(path_string, content)
    }
}

impl Vfs for IoFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.common.directory_exists(path)
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.common.file_exists(path)
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.common.get_accessible_entries(path)
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.common.stat(path)
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.common.read_file(path)
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        (self.remove)(path.as_string())
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        (self.chtimes)(path.as_string(), a_time, m_time)
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        let (root, rest) = path.root_and_relative_path();
        match (self.realpath)(&format!("{}{}", root.as_string(), rest)) {
            Ok(realpath) => tsc_tspath::rooted_path_from_absolute(&realpath),
            Err(_) => path.clone(),
        }
    }

    fn write_file(&self, path: &RootedFilePath, content: &str) -> Result<(), FsError> {
        self.write_file_ensuring_dir(path, content, &self.write_file)
    }

    fn append_file(&self, path: &RootedFilePath, content: &str) -> Result<(), FsError> {
        self.write_file_ensuring_dir(path, content, &self.append_file)
    }

    fn as_fs_with_sys(&self) -> Option<&dyn FsWithSys> {
        Some(self)
    }
}

impl FsWithSys for IoFs {
    fn fsys(&self) -> Arc<dyn Fs> {
        self.fsys.clone()
    }
}
