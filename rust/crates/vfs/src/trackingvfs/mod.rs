// Ported from tsc/internal/vfs/trackingvfs/trackingvfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// trackingvfs provides a VFS wrapper that records every file path
// accessed during compilation. This allows watch mode to know exactly which
// files and directories the compiler depended on, including non-existent
// paths from failed module resolution.

use std::sync::Arc;
use std::time::SystemTime;

use tsc_collections::syncset::SyncSet;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{FileInfo, FsError};
use crate::vfs::{Entries, Vfs};

/// Fs wraps a [Vfs] and records every path accessed via read-like operations.
/// Write operations (write_file, remove, chtimes) are not tracked since they
/// represent outputs, not dependencies.
pub struct Fs {
    pub inner: Arc<dyn Vfs>,
    pub seen_files: SyncSet<RootedPath>,
}

impl Fs {
    pub fn new(inner: Arc<dyn Vfs>) -> Fs {
        Fs {
            inner,
            seen_files: SyncSet::new(),
        }
    }
}

impl Vfs for Fs {
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.seen_files.add(path.as_path());
        self.inner.read_file(path)
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.seen_files.add(path.as_path());
        self.inner.file_exists(path)
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        self.inner.case_sensitivity()
    }

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.write_file(path, data)
    }

    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.inner.remove(path)
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.seen_files.add(path.as_path());
        self.inner.directory_exists(path)
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.seen_files.add(path.as_path());
        self.inner.get_accessible_entries(path)
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.seen_files.add(path.clone());
        self.inner.stat(path)
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.seen_files.add(path.clone());
        self.inner.realpath(path)
    }
}
