// Ported from tsc/internal/vfs/osvfs/os.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The DirFs implementation below is a port of os.dirFS (os/file.go), which the
// Go code uses via `RootFor: os.DirFS`.

use std::any::Any;
use std::io::{Read, Seek, Write};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::SystemTime;

use tsc_core::semaphore::{Semaphore, new_limited_semaphore};
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{
    self, DirEntry, File, FileInfo, FileMode, Fs, FsError, ReadDirFile, ReadDirFs,
    ReadFileFs, ReadLinkFs, ReaderAt, SeekWhence, Seeker, StatFs, MODE_CHAR_DEVICE,
    MODE_DEVICE, MODE_DIR, MODE_IRREGULAR, MODE_NAMED_PIPE, MODE_PERM, MODE_SOCKET,
    MODE_SYMLINK,
};
use crate::internal::Common;
use crate::vfs::{Entries, Vfs};

// Semaphore for operations that are effectively blocking syscalls.
static BLOCKING_OP_SEMA: std::sync::LazyLock<tsc_core::semaphore::LimitedSemaphore> =
    std::sync::LazyLock::new(|| new_limited_semaphore(128));
// Semaphore for file reads.
static READ_SEMA: std::sync::LazyLock<tsc_core::semaphore::LimitedSemaphore> =
    std::sync::LazyLock::new(|| new_limited_semaphore(128));
// Semaphore for file writes.
static WRITE_SEMA: std::sync::LazyLock<tsc_core::semaphore::LimitedSemaphore> =
    std::sync::LazyLock::new(|| new_limited_semaphore(32));

/// fs returns the singleton FS backed by the OS file system. (Go: osvfs.FS)
pub fn fs() -> Arc<dyn Vfs> {
    static OS_VFS: OnceLock<Arc<OsFs>> = OnceLock::new();
    OS_VFS.get_or_init(|| Arc::new(OsFs::new())).clone() as Arc<dyn Vfs>
}

struct OsFs {
    common: Common,
}

impl OsFs {
    fn new() -> OsFs {
        OsFs {
            common: Common {
                root_for: Arc::new(|root| Some(Arc::new(DirFs::new(root)) as Arc<dyn Fs>)),
                is_reparse_point: Some(Arc::new(is_reparse_point)),
            },
        }
    }
}

// We do this right at startup to minimize the chance that executable gets moved or deleted.
static FILE_SYSTEM_CASE_SENSITIVITY: OnceLock<CaseSensitivity> = OnceLock::new();

fn file_system_case_sensitivity() -> CaseSensitivity {
    *FILE_SYSTEM_CASE_SENSITIVITY.get_or_init(|| {
        // win32/win64 are case insensitive platforms
        if cfg!(windows) {
            return CaseSensitivity::CaseInsensitive;
        }

        if cfg!(target_arch = "wasm32") {
            // !!! Who knows; this depends on the host implementation.
            return CaseSensitivity::CaseSensitive;
        }

        // As a proxy for case-insensitivity, we check if the current executable exists under a different case.
        // This is not entirely correct, since different OSs can have differing case sensitivity in different paths,
        // but this is largely good enough for our purposes (and what sys.ts used to do with __filename).
        let exe = match tsc_osutil::executable() {
            Ok(exe) => exe,
            Err(err) => panic!("vfs: failed to get executable path: {}", err),
        };

        // If the current executable exists under a different case, we must be case-insensitive.
        let swapped = swap_case(&exe);
        match std::fs::metadata(&swapped) {
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                CaseSensitivity::CaseSensitive
            }
            Err(err) => panic!("vfs: failed to stat {}: {}", fs::go_quote(&swapped), err),
            Ok(_) => CaseSensitivity::CaseInsensitive,
        }
    })
}

/// Convert all lowercase chars to uppercase, and vice-versa
fn swap_case(str: &str) -> String {
    str.chars()
        .map(|r| {
            // unicode.ToUpper/ToLower are simple (1:1) case mappings; skip
            // multi-char mappings, which correspond to runes Go would leave
            // unchanged.
            let mut up = r.to_uppercase();
            let upper = up.next().unwrap_or(r);
            if up.next().is_some() {
                return r;
            }
            if upper == r {
                let mut lo = r.to_lowercase();
                let lower = lo.next().unwrap_or(r);
                let _ = lo; // multi-char lowercase results collapse to the first char
                return lower;
            }
            upper
        })
        .collect()
}

impl Vfs for OsFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        file_system_case_sensitivity()
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        let _guard = READ_SEMA.acquire();
        self.common.read_file(path)
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        let _guard = BLOCKING_OP_SEMA.acquire();
        self.common.directory_exists(path)
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        let _guard = BLOCKING_OP_SEMA.acquire();
        self.common.file_exists(path)
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        let _guard = BLOCKING_OP_SEMA.acquire();
        self.common.get_accessible_entries(path)
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        let _guard = BLOCKING_OP_SEMA.acquire();
        self.common.stat(path)
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        let _guard = BLOCKING_OP_SEMA.acquire();
        os_fs_realpath(path)
    }

    fn write_file(&self, path: &RootedFilePath, content: &str) -> Result<(), FsError> {
        self.write_file_ensuring_dir(path, content, false)
    }

    fn append_file(&self, path: &RootedFilePath, content: &str) -> Result<(), FsError> {
        self.write_file_ensuring_dir(path, content, true)
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        let _guard = BLOCKING_OP_SEMA.acquire();
        // todo: #701 add retry mechanism?
        remove_all(path.as_string())
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        let _guard = BLOCKING_OP_SEMA.acquire();
        // PORT: Go uses os.Chtimes (utimensat on the path, follows symlinks);
        // std has no path-based chtimes, so we open (following symlinks) and
        // use File::set_times (futimens) which behaves the same for existing
        // files and directories.
        let file = std::fs::File::open(path.as_string())?;
        let times = std::fs::FileTimes::new()
            .set_accessed(a_time)
            .set_modified(m_time);
        file.set_times(times)?;
        Ok(())
    }
}

impl OsFs {
    fn write_file_with_flag(&self, path: &str, content: &str, append: bool) -> Result<(), FsError> {
        let _guard = WRITE_SEMA.acquire();

        let mut options = std::fs::OpenOptions::new();
        options.write(true).create(true);
        if append {
            options.append(true);
        } else {
            options.truncate(true);
        }
        let file = options.open(path)?;
        let mut file = file;
        file.write_all(content.as_bytes())?;
        Ok(())
    }

    fn ensure_directory_exists(&self, directory_path: &str) -> Result<(), FsError> {
        let _guard = BLOCKING_OP_SEMA.acquire();
        std::fs::create_dir_all(directory_path)?;
        Ok(())
    }

    fn write_file_ensuring_dir(
        &self,
        path: &RootedFilePath,
        content: &str,
        append: bool,
    ) -> Result<(), FsError> {
        let path_string = path.as_string();
        if self
            .write_file_with_flag(path_string, content, append)
            .is_ok()
        {
            return Ok(());
        }
        self.ensure_directory_exists(path.directory().as_string())?;
        self.write_file_with_flag(path_string, content, append)
    }
}

fn os_fs_realpath(path: &RootedPath) -> RootedPath {
    let orig = path.clone();
    let native_path = from_slash(path.as_string());
    let Ok(native_path) = tsc_nativepath::realpath(&native_path) else {
        return orig;
    };
    let Ok(native_path) = abs_path(&native_path) else {
        return orig;
    };
    tsc_tspath::rooted_path_from_absolute(&native_path)
}

/// filepath.FromSlash — on unix the path is already slash-separated.
fn from_slash(path: &str) -> String {
    if std::path::MAIN_SEPARATOR == '/' {
        return path.to_string();
    }
    path.replace('/', &std::path::MAIN_SEPARATOR.to_string())
}

/// filepath.Abs — lexical join against the current working directory.
fn abs_path(path: &str) -> Result<String, std::io::Error> {
    if std::path::Path::new(path).is_absolute() {
        return Ok(path.to_string());
    }
    let cwd = std::env::current_dir()?;
    let joined = cwd.join(path);
    joined
        .into_os_string()
        .into_string()
        .map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidData, "path is not valid UTF-8"))
}

fn is_reparse_point(path: &str) -> bool {
    #[cfg(unix)]
    {
        return tsc_nativepath::is_symlink_or_reparse_point(&from_slash(path));
    }
    #[cfg(not(unix))]
    {
        // TODO(port): windows — FILE_ATTRIBUTE_REPARSE_POINT check.
        let _ = path;
        false
    }
}

/// os.RemoveAll.
fn remove_all(path: &str) -> Result<(), FsError> {
    match std::fs::symlink_metadata(path) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e.into()),
        Ok(meta) => {
            // A symlink to a directory is removed like a file: RemoveAll does
            // not descend through symlinks.
            if meta.is_dir() && !meta.file_type().is_symlink() {
                std::fs::remove_dir_all(path)?;
            } else {
                std::fs::remove_file(path)?;
            }
            Ok(())
        }
    }
}

/// get_global_typings_cache_location is osvfs.GetGlobalTypingsCacheLocation.
pub fn get_global_typings_cache_location() -> String {
    let cache_dir = user_cache_dir().unwrap_or_else(std::env::temp_dir);

    let subdir = if cfg!(windows) {
        "Microsoft/TypeScript"
    } else {
        "typescript"
    };
    tsc_tspath::combine_paths(
        &cache_dir.to_string_lossy(),
        &[subdir, tsc_core::version::version_major_minor()],
    )
}

/// os.UserCacheDir.
fn user_cache_dir() -> Option<std::path::PathBuf> {
    // PORT: unix-only resolution (os.UserCacheDir on unix consults
    // $XDG_CACHE_HOME then $HOME/.cache; windows/darwin are TODO).
    #[cfg(unix)]
    {
        if let Some(dir) = std::env::var_os("XDG_CACHE_HOME").filter(|v| !v.is_empty()) {
            return Some(dir.into());
        }
        if let Some(home) = std::env::var_os("HOME") {
            let mut dir = std::path::PathBuf::from(home);
            dir.push(".cache");
            return Some(dir);
        }
        return None;
    }
    #[cfg(not(unix))]
    {
        None
    }
}

// ---------------------------------------------------------------------------
// os.DirFS (os/file.go) and its file/entry types.
// ---------------------------------------------------------------------------

/// DirFs is os.DirFS: an [Fs] view of the OS file system rooted at dir.
/// Note that os.DirFS is only a *view* and provides no path sandboxing; the
/// caller (internal.Common) only ever hands it relative, slash-separated names.
pub struct DirFs {
    dir: String,
}

impl DirFs {
    pub fn new(dir: &str) -> DirFs {
        DirFs { dir: dir.to_string() }
    }

    /// join returns the path for name in dir.
    fn join(&self, name: &str) -> Result<String, FsError> {
        if self.dir.is_empty() {
            return Err(FsError::Message("os: DirFS with empty root".to_string()));
        }
        // filepathlite.Localize — on unix it requires fs.ValidPath and no NUL
        // byte; other platforms additionally translate separators.
        if !fs::valid_path(name) || name.contains('\0') {
            return Err(FsError::Invalid);
        }
        let name = if std::path::MAIN_SEPARATOR != '/' {
            name.replace('/', &std::path::MAIN_SEPARATOR.to_string())
        } else {
            name.to_string()
        };
        if self.dir.ends_with(std::path::MAIN_SEPARATOR) {
            return Ok(format!("{}{}", self.dir, name));
        }
        Ok(format!("{}{}{}", self.dir, std::path::MAIN_SEPARATOR, name))
    }
}

impl Fs for DirFs {
    fn open(&self, name: &str) -> Result<Box<dyn File>, FsError> {
        let fullname = match self.join(name) {
            Ok(fullname) => fullname,
            Err(err) => return Err(fs::path_error("open", name, err)),
        };
        match std::fs::File::open(&fullname) {
            Err(err) => {
                // dir.join mixed the two; report the io/fs name.
                Err(fs::path_error("open", name, err.into()))
            }
            Ok(file) => Ok(Box::new(OsFile::new(name, &fullname, file))),
        }
    }

    fn as_stat_fs(&self) -> Option<&dyn StatFs> {
        Some(self)
    }
    fn as_read_dir_fs(&self) -> Option<&dyn ReadDirFs> {
        Some(self)
    }
    fn as_read_file_fs(&self) -> Option<&dyn ReadFileFs> {
        Some(self)
    }
    fn as_read_link_fs(&self) -> Option<&dyn ReadLinkFs> {
        Some(self)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl StatFs for DirFs {
    fn stat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError> {
        let fullname = match self.join(name) {
            Ok(fullname) => fullname,
            Err(err) => return Err(fs::path_error("stat", name, err)),
        };
        match std::fs::metadata(&fullname) {
            Err(err) => Err(fs::path_error("stat", name, err.into())),
            Ok(meta) => Ok(Arc::new(OsFileInfo::new(name, meta))),
        }
    }
}

impl ReadDirFs for DirFs {
    /// ReadDir reads the named directory, returning all its directory entries
    /// sorted by filename.
    fn read_dir(&self, name: &str) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        let fullname = match self.join(name) {
            Ok(fullname) => fullname,
            Err(err) => return Err(fs::path_error("readdir", name, err)),
        };
        let mut entries: Vec<Arc<dyn DirEntry>> = Vec::new();
        match std::fs::read_dir(&fullname) {
            Err(err) => return Err(fs::path_error("readdir", name, err.into())),
            Ok(read_dir) => {
                for entry in read_dir {
                    match entry {
                        Ok(entry) => entries.push(Arc::new(OsDirEntry::new(&fullname, entry))),
                        Err(err) => {
                            return Err(fs::path_error("readdir", name, err.into()));
                        }
                    }
                }
            }
        }
        entries.sort_by(|a, b| a.name().cmp(&b.name()));
        Ok(entries)
    }
}

impl ReadFileFs for DirFs {
    fn read_file(&self, name: &str) -> Result<Vec<u8>, FsError> {
        let fullname = match self.join(name) {
            Ok(fullname) => fullname,
            Err(err) => return Err(fs::path_error("readfile", name, err)),
        };
        match std::fs::read(&fullname) {
            Err(err) => Err(fs::path_error("readfile", name, err.into())),
            Ok(data) => Ok(data),
        }
    }
}

impl ReadLinkFs for DirFs {
    fn read_link(&self, name: &str) -> Result<String, FsError> {
        let fullname = match self.join(name) {
            Ok(fullname) => fullname,
            Err(err) => return Err(fs::path_error("readlink", name, err)),
        };
        match std::fs::read_link(&fullname) {
            Err(err) => Err(fs::path_error("readlink", name, err.into())),
            Ok(target) => target.into_os_string().into_string().map_err(|_| {
                fs::path_error(
                    "readlink",
                    name,
                    FsError::Io(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "path is not valid UTF-8",
                    )),
                )
            }),
        }
    }

    fn lstat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError> {
        let fullname = match self.join(name) {
            Ok(fullname) => fullname,
            Err(err) => return Err(fs::path_error("lstat", name, err)),
        };
        match std::fs::symlink_metadata(&fullname) {
            Err(err) => Err(fs::path_error("lstat", name, err.into())),
            Ok(meta) => Ok(Arc::new(OsFileInfo::new(name, meta))),
        }
    }
}

/// OsFile is *os.File: fs.File + ReadDirFile + io.Seeker + io.ReaderAt.
struct OsFile {
    name: String,
    path: String,
    file: Mutex<Option<std::fs::File>>,
    // ReadDir state, populated lazily from self.path.
    dir_state: Mutex<Option<OsDirState>>,
}

struct OsDirState {
    entries: Vec<Arc<dyn DirEntry>>,
    offset: usize,
}

impl OsFile {
    fn new(name: &str, path: &str, file: std::fs::File) -> OsFile {
        OsFile {
            name: name.to_string(),
            path: path.to_string(),
            file: Mutex::new(Some(file)),
            dir_state: Mutex::new(None),
        }
    }

    fn with_file<T>(
        &self,
        op: &'static str,
        f: impl FnOnce(&std::fs::File) -> Result<T, std::io::Error>,
    ) -> Result<T, FsError> {
        let guard = self.file.lock().unwrap();
        match &*guard {
            None => Err(fs::path_error(op, &self.name, FsError::Closed)),
            Some(file) => f(file).map_err(|e| fs::path_error(op, &self.name, e.into())),
        }
    }

    fn with_file_mut<T>(
        &self,
        op: &'static str,
        f: impl FnOnce(&mut std::fs::File) -> Result<T, std::io::Error>,
    ) -> Result<T, FsError> {
        let mut guard = self.file.lock().unwrap();
        match &mut *guard {
            None => Err(fs::path_error(op, &self.name, FsError::Closed)),
            Some(file) => f(file).map_err(|e| fs::path_error(op, &self.name, e.into())),
        }
    }
}

impl File for OsFile {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        self.with_file("stat", |f| {
            f.metadata()
                .map(|meta| Arc::new(OsFileInfo::new(&self.name, meta)) as Arc<dyn FileInfo>)
        })
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize, FsError> {
        self.with_file_mut("read", |f| f.read(buf))
            .and_then(|n| {
                if n == 0 && !buf.is_empty() {
                    // io.Reader contract: (0, io.EOF) at end of file.
                    Err(FsError::Eof)
                } else {
                    Ok(n)
                }
            })
    }

    fn close(&self) -> Result<(), FsError> {
        let mut guard = self.file.lock().unwrap();
        if guard.is_none() {
            return Err(fs::path_error("close", &self.name, FsError::Closed));
        }
        *guard = None;
        Ok(())
    }

    fn as_read_dir_file(&self) -> Option<&dyn ReadDirFile> {
        // Go's *os.File always satisfies fs.ReadDirFile; ReadDir on a
        // non-directory returns an error from readdir rather than failing the
        // assertion.
        Some(self)
    }

    fn as_seeker(&self) -> Option<&dyn Seeker> {
        Some(self)
    }

    fn as_reader_at(&self) -> Option<&dyn ReaderAt> {
        Some(self)
    }
}

impl ReadDirFile for OsFile {
    /// os.File.ReadDir — entries in directory order.
    fn read_dir(&self, count: i32) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        let mut state = self.dir_state.lock().unwrap();
        if state.is_none() {
            // Check the file is still open.
            self.with_file("readdirent", |_| Ok(()))?;
            let mut entries: Vec<Arc<dyn DirEntry>> = Vec::new();
            match std::fs::read_dir(&self.path) {
                Err(err) => {
                    return Err(fs::path_error("readdirent", &self.name, err.into()))
                }
                Ok(read_dir) => {
                    for entry in read_dir {
                        match entry {
                            Ok(entry) => {
                                entries.push(Arc::new(OsDirEntry::new(&self.path, entry)))
                            }
                            Err(err) => {
                                return Err(fs::path_error(
                                    "readdirent",
                                    &self.name,
                                    err.into(),
                                ))
                            }
                        }
                    }
                }
            }
            *state = Some(OsDirState { entries, offset: 0 });
        }

        let state = state.as_mut().unwrap();
        let mut n = state.entries.len() - state.offset;
        if n == 0 && count > 0 {
            return Err(FsError::Eof);
        }
        if count > 0 && n > count as usize {
            n = count as usize;
        }
        let list: Vec<Arc<dyn DirEntry>> =
            state.entries[state.offset..state.offset + n].to_vec();
        state.offset += n;
        Ok(list)
    }
}

impl Seeker for OsFile {
    fn seek(&self, offset: i64, whence: SeekWhence) -> Result<i64, FsError> {
        let pos = match whence {
            SeekWhence::Start => std::io::SeekFrom::Start(offset as u64),
            SeekWhence::Current => std::io::SeekFrom::Current(offset),
            SeekWhence::End => std::io::SeekFrom::End(offset),
        };
        self.with_file_mut("seek", |f| f.seek(pos).map(|p| p as i64))
    }
}

#[cfg(unix)]
impl ReaderAt for OsFile {
    fn read_at(&self, buf: &mut [u8], offset: i64) -> Result<usize, FsError> {
        use std::os::unix::fs::FileExt;
        if offset < 0 {
            return Err(fs::path_error("readat", &self.name, FsError::Invalid));
        }
        self.with_file("readat", |f| f.read_at(buf, offset as u64))
            .and_then(|n| {
                if n < buf.len() {
                    // io.ReaderAt returns io.EOF when fewer than len(buf)
                    // bytes were read.
                    Err(FsError::Eof)
                } else {
                    Ok(n)
                }
            })
    }
}

#[cfg(not(unix))]
impl ReaderAt for OsFile {
    fn read_at(&self, buf: &mut [u8], offset: i64) -> Result<usize, FsError> {
        if offset < 0 {
            return Err(fs::path_error("readat", &self.name, FsError::Invalid));
        }
        self.with_file_mut("readat", |f| {
            let prev = f.stream_position()?;
            f.seek(std::io::SeekFrom::Start(offset as u64))?;
            let n = f.read(buf);
            let _ = f.seek(std::io::SeekFrom::Start(prev));
            n
        })
        .and_then(|n| if n < buf.len() { Err(FsError::Eof) } else { Ok(n) })
    }
}

/// OsFileInfo is os.fileStat.
struct OsFileInfo {
    name: String,
    meta: std::fs::Metadata,
}

impl OsFileInfo {
    fn new(name: &str, meta: std::fs::Metadata) -> OsFileInfo {
        OsFileInfo {
            name: fs::path_base(name),
            meta,
        }
    }
}

/// os mode bits for a std FileType (the non-permission part of os FileMode).
fn file_type_mode(file_type: &std::fs::FileType) -> FileMode {
    if file_type.is_dir() {
        return MODE_DIR;
    }
    if file_type.is_symlink() {
        return MODE_SYMLINK;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileTypeExt;
        if file_type.is_fifo() {
            return MODE_NAMED_PIPE;
        }
        if file_type.is_socket() {
            return MODE_SOCKET;
        }
        if file_type.is_char_device() {
            return MODE_DEVICE | MODE_CHAR_DEVICE;
        }
        if file_type.is_block_device() {
            return MODE_DEVICE;
        }
    }
    if file_type.is_file() {
        return FileMode(0);
    }
    MODE_IRREGULAR
}

fn metadata_mode(meta: &std::fs::Metadata) -> FileMode {
    let mut mode = file_type_mode(&meta.file_type());
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        mode = mode | FileMode(meta.permissions().mode() & MODE_PERM.0);
    }
    mode
}

impl FileInfo for OsFileInfo {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn size(&self) -> i64 {
        self.meta.len() as i64
    }
    fn mode(&self) -> FileMode {
        metadata_mode(&self.meta)
    }
    fn mod_time(&self) -> SystemTime {
        self.meta.modified().unwrap_or(SystemTime::UNIX_EPOCH)
    }
    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>> {
        None // PORT: Go returns *syscall.Stat_t; unused by the VFS.
    }
}

/// OsDirEntry is os.unixDirent.
struct OsDirEntry {
    parent: String,
    name: String,
    typ: FileMode,
}

impl OsDirEntry {
    fn new(parent: &str, entry: std::fs::DirEntry) -> OsDirEntry {
        let name = entry.file_name().to_string_lossy().into_owned();
        let typ = match entry.file_type() {
            Ok(ft) => {
                let mode = file_type_mode(&ft);
                // dirent DT_UNKNOWN falls back to lstatat in Go.
                if mode == FileMode(0) && !ft.is_file() {
                    match std::fs::symlink_metadata(entry.path()) {
                        Ok(meta) => metadata_mode(&meta).type_(),
                        Err(_) => MODE_IRREGULAR,
                    }
                } else {
                    mode
                }
            }
            Err(_) => match std::fs::symlink_metadata(entry.path()) {
                Ok(meta) => metadata_mode(&meta).type_(),
                Err(_) => MODE_IRREGULAR,
            },
        };
        OsDirEntry {
            parent: parent.to_string(),
            name,
            typ,
        }
    }
}

impl DirEntry for OsDirEntry {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn is_dir(&self) -> bool {
        self.typ.is_dir()
    }
    fn type_(&self) -> FileMode {
        self.typ
    }
    fn info(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        // Lazy lstat, matching os.unixDirent.Info.
        let path = format!("{}/{}", self.parent, self.name);
        match std::fs::symlink_metadata(&path) {
            Err(err) => Err(fs::path_error("lstat", &path, err.into())),
            Ok(meta) => Ok(Arc::new(OsFileInfo::new(&self.name, meta))),
        }
    }
}
