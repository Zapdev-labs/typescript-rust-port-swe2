// Ported from tsc/internal/vfs/cachedvfs/cachedvfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763

#[cfg(test)]
mod tests;

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::SystemTime;

use tsc_collections::syncmap::SyncMap;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{FileInfo, FsError};
use crate::vfs::{Entries, Vfs};

/// Fs is cachedvfs.FS: a [Vfs] wrapper that caches read-only queries.
pub struct Fs {
    fs: Arc<dyn Vfs>,
    enabled: AtomicBool,

    directory_exists_cache: SyncMap<RootedDirectoryPath, bool>,
    file_exists_cache: SyncMap<RootedFilePath, bool>,
    get_accessible_entries_cache: SyncMap<RootedDirectoryPath, Entries>,
    realpath_cache: SyncMap<RootedPath, RootedPath>,
    stat_cache: SyncMap<RootedPath, Option<Arc<dyn FileInfo>>>,
}

/// from is cachedvfs.From.
pub fn from(fs: Arc<dyn Vfs>) -> Arc<Fs> {
    Arc::new(Fs {
        fs,
        enabled: AtomicBool::new(true),
        directory_exists_cache: SyncMap::new(),
        file_exists_cache: SyncMap::new(),
        get_accessible_entries_cache: SyncMap::new(),
        realpath_cache: SyncMap::new(),
        stat_cache: SyncMap::new(),
    })
}

impl Fs {
    pub fn disable_and_clear_cache(&self) {
        if self
            .enabled
            .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            self.clear_cache();
        }
    }

    pub fn enable(&self) {
        self.enabled.store(true, Ordering::SeqCst);
    }

    pub fn clear_cache(&self) {
        self.directory_exists_cache.clear();
        self.file_exists_cache.clear();
        self.get_accessible_entries_cache.clear();
        self.realpath_cache.clear();
        self.stat_cache.clear();
    }
}

impl Vfs for Fs {
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        if self.enabled.load(Ordering::SeqCst) {
            if let Some(ret) = self.directory_exists_cache.load(path) {
                return ret;
            }
        }

        let ret = self.fs.directory_exists(path);

        if self.enabled.load(Ordering::SeqCst) {
            self.directory_exists_cache.store(path.clone(), ret);
        }

        ret
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        if self.enabled.load(Ordering::SeqCst) {
            if let Some(ret) = self.file_exists_cache.load(path) {
                return ret;
            }
        }

        let ret = self.fs.file_exists(path);

        if self.enabled.load(Ordering::SeqCst) {
            self.file_exists_cache.store(path.clone(), ret);
        }

        ret
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        if self.enabled.load(Ordering::SeqCst) {
            if let Some(ret) = self.get_accessible_entries_cache.load(path) {
                return ret;
            }
        }

        let ret = self.fs.get_accessible_entries(path);

        if self.enabled.load(Ordering::SeqCst) {
            self.get_accessible_entries_cache
                .store(path.clone(), ret.clone());
        }

        ret
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.fs.read_file(path)
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        if self.enabled.load(Ordering::SeqCst) {
            if let Some(ret) = self.realpath_cache.load(path) {
                return ret;
            }
        }

        let ret = self.fs.realpath(path);

        if self.enabled.load(Ordering::SeqCst) {
            self.realpath_cache.store(path.clone(), ret.clone());
        }

        ret
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

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        if self.enabled.load(Ordering::SeqCst) {
            if let Some(ret) = self.stat_cache.load(path) {
                return ret;
            }
        }

        let ret = self.fs.stat(path);

        if self.enabled.load(Ordering::SeqCst) {
            self.stat_cache.store(path.clone(), ret.clone());
        }

        ret
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        self.fs.case_sensitivity()
    }

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.fs.write_file(path, data)
    }

    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.fs.append_file(path, data)
    }
}
