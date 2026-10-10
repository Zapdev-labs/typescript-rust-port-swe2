//! `fs.go` — in-memory FS serving only the synthesized input (and optional
//! barebones lib) files; every other operation panics, matching Go's
//! embedded-`vfs.FS` "unsupported operations" behavior.

use std::sync::Arc;
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_tspath::{
    CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath,
};
use tsc_vfs::fs::{DirEntry, FileInfo, FsError};
use tsc_vfs::vfs::{Entries, Vfs};

/// `transpileFS` embeds unsupported operations so unexpected filesystem
/// access panics.
pub struct TranspileFs {
    pub files: FxHashMap<RootedFilePath, String>,
}

impl Vfs for TranspileFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        CaseSensitivity::CaseSensitive
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        match self.files.contains_key(path) {
            true => true,
            false => panic!("unexpected file existence check for {:?}", path.as_string()),
        }
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        match self.files.get(path) {
            Some(content) => Some(content.clone()),
            None => panic!("unexpected file read for {:?}", path.as_string()),
        }
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        panic!(
            "unexpected directory existence check for {:?}",
            path.as_string()
        )
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        panic!("unexpected realpath request for {:?}", path.as_string())
    }

    fn write_file(&self, path: &RootedFilePath, _data: &str) -> Result<(), FsError> {
        panic!("unexpected file write for {:?}", path.as_string())
    }

    fn append_file(&self, path: &RootedFilePath, _data: &str) -> Result<(), FsError> {
        panic!("unexpected file append for {:?}", path.as_string())
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        panic!("unexpected remove request for {:?}", path.as_string())
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        _a_time: SystemTime,
        _m_time: SystemTime,
    ) -> Result<(), FsError> {
        panic!("unexpected chtimes request for {:?}", path.as_string())
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        panic!(
            "unexpected get-accessible-entries request for {:?}",
            path.as_string()
        )
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        panic!("unexpected stat request for {:?}", path.as_string())
    }
}

// `DirEntry` referenced for trait completeness; unused import avoidance.
#[allow(dead_code)]
fn _unused(_: Arc<dyn DirEntry>) {}
