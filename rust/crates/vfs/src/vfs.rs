// Ported from tsc/internal/vfs/vfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;
use std::time::SystemTime;

use rustc_hash::FxHashSet;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{DirEntry, FileInfo, FsError};

// Vfs is a file system abstraction over rooted, normalized paths. Operations
// declare whether they require a file, directory, or either kind of path.
// (Go: vfs.FS)
pub trait Vfs: Send + Sync {
    /// CaseSensitivity returns whether path comparison is case-sensitive.
    fn case_sensitivity(&self) -> CaseSensitivity;

    /// FileExists returns true if the file exists.
    fn file_exists(&self, path: &RootedFilePath) -> bool;

    /// ReadFile reads the file specified by path and returns the content.
    /// If the file fails to be read, returns None.
    fn read_file(&self, path: &RootedFilePath) -> Option<String>;

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError>;

    /// AppendFile appends data to the file at path, creating it if it does not exist.
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError>;

    /// Removes `path` and all its contents. Will return the first error it encounters.
    fn remove(&self, path: &RootedPath) -> Result<(), FsError>;

    /// Chtimes changes the access and modification times of the named file.
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError>;

    /// DirectoryExists returns true if the path is a directory.
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool;

    /// GetAccessibleEntries returns the files/directories in the specified directory.
    /// If any entry is a symlink, it will be followed.
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries;

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>>;

    /// Realpath returns the "real path" of the specified path,
    /// following symlinks and correcting filename casing.
    fn realpath(&self, path: &RootedPath) -> RootedPath;

    /// PORT: Go callers downcast an FS value with `fs.(iovfs.FsWithSys)` and
    /// `fs.(iovfs.FsWithSys).FSys().(*vfstest.MapFS)`; the first assertion is
    /// modeled by this hook, the second by [crate::fs::Fs::as_any].
    fn as_fs_with_sys(&self) -> Option<&dyn crate::iovfs::FsWithSys> {
        None
    }
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct Entries {
    pub files: Vec<String>,
    pub directories: Vec<String>,
    /// Symlinks contains the names of entries in Files or Directories that were
    /// originally symbolic links (or reparse points) on disk. The names are the
    /// same as those in Files/Directories (i.e., the link name, not the target).
    /// None means symlink information is not available and the entries may need
    /// to be re-checked for symlinks.
    pub symlinks: Option<FxHashSet<String>>,
}

// PORT: Go aliases `DirEntry = fs.DirEntry` and `FileInfo = fs.FileInfo`; in
// Rust, the traits are used as `Arc<dyn DirEntry>` / `Arc<dyn FileInfo>`.

// pub use of the sentinels so callers can write vfs::ERR_NOT_EXIST just as Go
// callers write vfs.ErrNotExist.
pub use crate::fs::{ERR_CLOSED, ERR_EXIST, ERR_INVALID, ERR_NOT_EXIST, ERR_PERMISSION};

// WalkDirFunc is like fs.WalkDirFunc, but reports rooted, normalized
// RootedPath paths.
//
// PORT: Go's `err error` and `d fs.DirEntry` parameters are both nullable;
// they are `Option<&FsError>` / `Option<&dyn DirEntry>` here.
pub type WalkDirFunc<'a> = dyn FnMut(&RootedPath, Option<&dyn DirEntry>, Option<&FsError>) -> Result<(), FsError>
    + Send
    + 'a;

// SkipAll is fs.SkipAll.
pub use crate::fs::SKIP_ALL;
// SkipDir is fs.SkipDir.
pub use crate::fs::SKIP_DIR;

