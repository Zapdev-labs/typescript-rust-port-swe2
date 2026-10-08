// Ported from tsc/internal/bundled/{bundled,embed,embed_generated,libs_generated}.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Package bundled provides access to files bundled with TypeScript.
//
// PORT: Go's `noembed` build tag switches to serving libs off disk next to
// the executable; Rust always embeds (`EMBEDDED = true`) — the embed path is
// the shipping configuration and the only one the spec requires.
use std::any::Any;
use std::sync::{Arc, OnceLock};
use std::time::SystemTime;

use tsc_tspath::{RootedDirectoryPath, RootedFilePath, RootedPath, rooted_directory_path_from_normalized};
use tsc_vfs::fs::{DirEntry, FileInfo, FileMode, FsError, MODE_DIR};
use tsc_vfs::{Entries, Vfs};

mod generated {
    include!(concat!(env!("OUT_DIR"), "/libs_generated.rs"));
}
pub use generated::LIB_NAMES;
use generated::EMBEDDED_CONTENTS;

/// `Embedded` is true if the bundled files are implemented through an embedded FS.
pub const EMBEDDED: bool = true;

const SCHEME: &str = "bundled:///";

fn split_path(path: &str) -> Option<&str> {
    path.strip_prefix(SCHEME)
}

/// WrapFS returns an FS which redirects embedded paths to the embedded file
/// system. If the embedded file system is not available, it returns the
/// original FS.
pub fn wrap_fs(fs: Arc<dyn Vfs>) -> Arc<dyn Vfs> {
    Arc::new(WrappedFs { fs })
}

/// LibPath returns the path to the directory containing the bundled lib.d.ts
/// files.
pub fn lib_path() -> RootedDirectoryPath {
    rooted_directory_path_from_normalized(&format!("{SCHEME}libs"))
}

pub fn is_bundled(path: &str) -> bool {
    split_path(path).is_some()
}

/// TestingLibPath is the on-disk libs directory, usable in tests.
///
/// PORT: Go locates the source dir via runtime.Caller; Rust uses
/// CARGO_MANIFEST_DIR (the crate dir, containing the `libs` symlink) at
/// compile time — equivalent for a workspace checkout.
pub fn testing_lib_path() -> RootedDirectoryPath {
    static PATH: OnceLock<RootedDirectoryPath> = OnceLock::new();
    PATH.get_or_init(|| {
        rooted_directory_path_from_normalized(&format!(
            "{}/libs",
            env!("CARGO_MANIFEST_DIR")
        ))
    })
    .clone()
}

fn embedded_contents(rest: &str) -> Option<&'static str> {
    EMBEDDED_CONTENTS
        .binary_search_by(|(k, _)| (*k).cmp(rest))
        .ok()
        .map(|i| EMBEDDED_CONTENTS[i].1)
}

// wrappedFS is implemented directly rather than going through `io::fs::FS`.
// Our vfs works with file contents in terms of strings, and that's what
// include_str! does under the hood, but going through fs::FS would cause
// copying to bytes and back.
struct WrappedFs {
    fs: Arc<dyn Vfs>,
}

impl Vfs for WrappedFs {
    fn case_sensitivity(&self) -> tsc_tspath::CaseSensitivity {
        self.fs.case_sensitivity()
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        if let Some(rest) = split_path(path.as_string()) {
            return embedded_contents(rest).is_some();
        }
        self.fs.file_exists(path)
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        if let Some(rest) = split_path(path.as_string()) {
            return embedded_contents(rest).map(str::to_owned);
        }
        self.fs.read_file(path)
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        if let Some(rest) = split_path(path.as_string()) {
            return rest == "libs";
        }
        self.fs.directory_exists(path)
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        if let Some(rest) = split_path(path.as_string()) {
            let mut result = Entries::default();
            if rest.is_empty() {
                result.directories = vec!["libs".to_string()];
            } else if rest == "libs" {
                result.files = LIB_NAMES.iter().map(|s| s.to_string()).collect();
            }
            return result;
        }
        self.fs.get_accessible_entries(path)
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        if let Some(rest) = split_path(path.as_string()) {
            if rest.is_empty() || rest == "libs" {
                return Some(Arc::new(BundledFileInfo {
                    mode: MODE_DIR,
                    name: rest.to_string(),
                    size: 0,
                }));
            }
            if let Some(lib) = embedded_contents(rest) {
                let lib_name = rest.strip_prefix("libs/").unwrap_or(rest);
                return Some(Arc::new(BundledFileInfo {
                    mode: FileMode(0),
                    name: lib_name.to_string(),
                    size: lib.len() as i64,
                }));
            }
            return None;
        }
        self.fs.stat(path)
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        if split_path(path.as_string()).is_some() {
            return path.clone();
        }
        self.fs.realpath(path)
    }

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        if split_path(path.as_string()).is_some() {
            panic!("cannot write to embedded file system");
        }
        self.fs.write_file(path, data)
    }

    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        if split_path(path.as_string()).is_some() {
            panic!("cannot write to embedded file system");
        }
        self.fs.append_file(path, data)
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        if split_path(path.as_string()).is_some() {
            panic!("cannot remove from embedded file system");
        }
        self.fs.remove(path)
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        if split_path(path.as_string()).is_some() {
            panic!("cannot change times on embedded file system");
        }
        self.fs.chtimes(path, a_time, m_time)
    }
}

#[derive(Clone)]
struct BundledFileInfo {
    mode: FileMode,
    name: String,
    size: i64,
}

impl FileInfo for BundledFileInfo {
    fn is_dir(&self) -> bool {
        self.mode.is_dir()
    }

    fn mod_time(&self) -> SystemTime {
        // PORT: Go returns time.Time{} (year 1), unrepresentable by
        // SystemTime; UNIX_EPOCH is the closest "unset" sentinel.
        SystemTime::UNIX_EPOCH
    }

    fn mode(&self) -> FileMode {
        self.mode
    }

    fn name(&self) -> String {
        self.name.clone()
    }

    fn size(&self) -> i64 {
        self.size
    }

    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>> {
        None
    }
}

impl DirEntry for BundledFileInfo {
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
        Ok(Arc::new(self.clone()))
    }
}
