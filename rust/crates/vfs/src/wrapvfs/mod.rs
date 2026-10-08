// Ported from tsc/internal/vfs/wrapvfs/wrapvfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;
use std::time::SystemTime;

use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{FileInfo, FsError};
use crate::vfs::{Entries, Vfs};

/// Boxed function overrides used by [Replacements].
type ReplFn0<R> = Box<dyn Fn() -> R + Send + Sync>;
type ReplFn1<A, R> = Box<dyn Fn(&A) -> R + Send + Sync>;
type ReplFn2<A, B, R> = Box<dyn for<'a, 'b> Fn(&'a A, &'b B) -> R + Send + Sync>;
type ReplFn3<A, B, C, R> = Box<dyn Fn(&A, B, C) -> R + Send + Sync>;

/// Replacements is wrapvfs.Replacements: per-method overrides for [wrap].
/// None fields delegate to the wrapped [Vfs].
#[derive(Default)]
pub struct Replacements {
    pub case_sensitivity: Option<ReplFn0<CaseSensitivity>>,
    pub file_exists: Option<ReplFn1<RootedFilePath, bool>>,
    pub read_file: Option<ReplFn1<RootedFilePath, Option<String>>>,
    pub write_file: Option<ReplFn2<RootedFilePath, str, Result<(), FsError>>>,
    pub append_file: Option<ReplFn2<RootedFilePath, str, Result<(), FsError>>>,
    pub remove: Option<ReplFn1<RootedPath, Result<(), FsError>>>,
    pub chtimes: Option<ReplFn3<RootedPath, SystemTime, SystemTime, Result<(), FsError>>>,
    pub directory_exists: Option<ReplFn1<RootedDirectoryPath, bool>>,
    pub get_accessible_entries: Option<ReplFn1<RootedDirectoryPath, Entries>>,
    pub stat: Option<ReplFn1<RootedPath, Option<Arc<dyn FileInfo>>>>,
    pub realpath: Option<ReplFn1<RootedPath, RootedPath>>,
}

/// wrap is wrapvfs.Wrap.
pub fn wrap(fs: Arc<dyn Vfs>, replacements: Replacements) -> Arc<dyn Vfs> {
    Arc::new(WrappedFs { fs, replacements })
}

struct WrappedFs {
    fs: Arc<dyn Vfs>,
    replacements: Replacements,
}

impl Vfs for WrappedFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        match &self.replacements.case_sensitivity {
            Some(f) => f(),
            None => self.fs.case_sensitivity(),
        }
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        match &self.replacements.file_exists {
            Some(f) => f(path),
            None => self.fs.file_exists(path),
        }
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        match &self.replacements.read_file {
            Some(f) => f(path),
            None => self.fs.read_file(path),
        }
    }

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        match &self.replacements.write_file {
            Some(f) => f(path, data),
            None => self.fs.write_file(path, data),
        }
    }

    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        match &self.replacements.append_file {
            Some(f) => f(path, data),
            None => self.fs.append_file(path, data),
        }
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        match &self.replacements.remove {
            Some(f) => f(path),
            None => self.fs.remove(path),
        }
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        match &self.replacements.chtimes {
            Some(f) => f(path, a_time, m_time),
            None => self.fs.chtimes(path, a_time, m_time),
        }
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        match &self.replacements.directory_exists {
            Some(f) => f(path),
            None => self.fs.directory_exists(path),
        }
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        match &self.replacements.get_accessible_entries {
            Some(f) => f(path),
            None => self.fs.get_accessible_entries(path),
        }
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        match &self.replacements.stat {
            Some(f) => f(path),
            None => self.fs.stat(path),
        }
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        match &self.replacements.realpath {
            Some(f) => f(path),
            None => self.fs.realpath(path),
        }
    }

    // PORT: as_fs_with_sys deliberately not forwarded — replacements cannot be
    // applied to the inner fs.FS, matching Go where wrappedFS does not
    // implement FsWithSys.
}
