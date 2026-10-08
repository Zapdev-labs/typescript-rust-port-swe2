// Ported from io/fs @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: This module ports the subset of Go's `io/fs` package that the VFS
// implementation and its tests exercise: the [Fs] interface and its optional
// interfaces ([StatFs], [ReadDirFs], [ReadFileFs], [SubFs], [ReadLinkFs]), the
// [File]/[ReadDirFile]/[Seeker]/[ReaderAt] interfaces, [FileInfo]/[DirEntry],
// [FileMode], [PathError], the package-level sentinel errors, and the free
// functions [stat], [read_dir], [read_file], [sub], [file_info_to_dir_entry],
// and [valid_path].
//
// Go's `io/fs` is not part of `tsc/internal/vfs`, but `tsc/internal/vfs` is
// specified entirely in terms of it, so a faithful local port is required.

use std::any::Any;
use std::fmt;
use std::io;
use std::sync::Arc;
use std::time::SystemTime;

/// FsError mirrors Go's `error` values as used by `io/fs` and the VFS
/// implementation. The sentinel variants correspond to the package-level
/// `fs.Err*` errors and `io.EOF`; [`FsError::is`] implements the `errors.Is`
/// unwrapping semantics those APIs rely on.
#[derive(Debug)]
pub enum FsError {
    /// fs.ErrInvalid — "invalid argument"
    Invalid,
    /// fs.ErrPermission — "permission denied"
    Permission,
    /// fs.ErrExist — "file already exists"
    Exist,
    /// fs.ErrNotExist — "file does not exist"
    NotExist,
    /// fs.ErrClosed — "file already closed"
    Closed,
    /// io.EOF — "EOF"
    Eof,
    /// fs.SkipDir — "skip this directory"
    SkipDir,
    /// fs.SkipAll — "skip everything"
    SkipAll,
    /// *fs.PathError — `Op + " " + Path + ": " + Err`
    PathError {
        op: &'static str,
        path: String,
        err: Box<FsError>,
    },
    /// An error created with fmt.Errorf without a wrapped %w error.
    Message(String),
    /// fmt.Errorf("...: %w", err) — a message that wraps an inner error.
    Wrap { msg: String, err: Box<FsError> },
    /// *vfstest.brokenSymlinkError — declared here (rather than in vfstest) so
    /// `is`-style classification is available crate-wide.
    BrokenSymlink { from: String, to: String },
    /// A std::io::Error, e.g. produced by osvfs. [`FsError::is`] maps the
    /// common io::ErrorKinds onto the corresponding fs.Err* sentinels the way
    /// Go's os errors map onto the io/fs sentinels via errors.Is.
    Io(io::Error),
}

pub const ERR_INVALID: FsError = FsError::Invalid;
pub const ERR_PERMISSION: FsError = FsError::Permission;
pub const ERR_EXIST: FsError = FsError::Exist;
pub const ERR_NOT_EXIST: FsError = FsError::NotExist;
pub const ERR_CLOSED: FsError = FsError::Closed;
pub const EOF: FsError = FsError::Eof;

/// SkipDir is used as a return value from walk functions to indicate that
/// the directory named in the call is to be skipped. It is not returned as
/// an error by any function.
pub const SKIP_DIR: FsError = FsError::SkipDir;
/// SkipAll is used as a return value from walk functions to indicate that
/// the walk should be aborted. It is not returned as an error by any function.
pub const SKIP_ALL: FsError = FsError::SkipAll;

/// go_quote renders the %q verb for the path/error strings the VFS produces.
/// PORT: Go's strconv.Quote escapes non-printable and non-ASCII characters;
/// the VFS only quotes file paths and canonical paths, where plain quoting is
/// sufficient in practice.
pub fn go_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\x{:02x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub fn path_error(op: &'static str, path: impl Into<String>, err: FsError) -> FsError {
    FsError::PathError {
        op,
        path: path.into(),
        err: Box::new(err),
    }
}

impl FsError {
    /// errors.Is: identity for sentinels, unwrap through PathError/Wrap, and
    /// map io::Error kinds onto the fs sentinels.
    pub fn is(&self, other: &FsError) -> bool {
        use FsError::*;
        let matches_sentinel = match (self, other) {
            (Invalid, Invalid)
            | (Permission, Permission)
            | (Exist, Exist)
            | (NotExist, NotExist)
            | (Closed, Closed)
            | (Eof, Eof)
            | (SkipDir, SkipDir)
            | (SkipAll, SkipAll) => true,
            (Io(e), Invalid) => e.kind() == io::ErrorKind::InvalidInput,
            (Io(e), Permission) => e.kind() == io::ErrorKind::PermissionDenied,
            (Io(e), Exist) => e.kind() == io::ErrorKind::AlreadyExists,
            (Io(e), NotExist) => e.kind() == io::ErrorKind::NotFound,
            _ => false,
        };
        if matches_sentinel {
            return true;
        }
        match self {
            PathError { err, .. } | Wrap { err, .. } => err.is(other),
            _ => false,
        }
    }

    pub fn is_not_exist(&self) -> bool {
        self.is(&ERR_NOT_EXIST)
    }

    pub fn is_eof(&self) -> bool {
        self.is(&EOF)
    }

    pub fn is_skip_dir(&self) -> bool {
        self.is(&SKIP_DIR)
    }

    pub fn is_skip_all(&self) -> bool {
        self.is(&SKIP_ALL)
    }

    pub fn is_broken_symlink(&self) -> bool {
        match self {
            FsError::BrokenSymlink { .. } => true,
            FsError::PathError { err, .. } | FsError::Wrap { err, .. } => err.is_broken_symlink(),
            _ => false,
        }
    }
}

impl fmt::Display for FsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use FsError::*;
        match self {
            Invalid => f.write_str("invalid argument"),
            Permission => f.write_str("permission denied"),
            Exist => f.write_str("file already exists"),
            NotExist => f.write_str("file does not exist"),
            Closed => f.write_str("file already closed"),
            Eof => f.write_str("EOF"),
            SkipDir => f.write_str("skip this directory"),
            SkipAll => f.write_str("skip everything"),
            PathError { op, path, err } => write!(f, "{} {}: {}", op, path, err),
            Message(msg) => f.write_str(msg),
            Wrap { msg, err } => write!(f, "{}: {}", msg, err),
            BrokenSymlink { from, to } => {
                write!(f, "broken symlink {} -> {}", go_quote(from), go_quote(to))
            }
            Io(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for FsError {}

impl From<io::Error> for FsError {
    fn from(e: io::Error) -> Self {
        FsError::Io(e)
    }
}

// FileMode is fs.FileMode: a file's mode and permission bits.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileMode(pub u32);

// The order of the mode constants matches io/fs exactly; ModeType masks off
// the non-permission bits that identify the file kind.
pub const MODE_DIR: FileMode = FileMode(1 << 31); // d: is a directory
pub const MODE_APPEND: FileMode = FileMode(1 << 30); // a: append-only
pub const MODE_EXCLUSIVE: FileMode = FileMode(1 << 29); // l: exclusive use
pub const MODE_TEMPORARY: FileMode = FileMode(1 << 28); // T: temporary file
pub const MODE_SYMLINK: FileMode = FileMode(1 << 27); // L: symbolic link
pub const MODE_DEVICE: FileMode = FileMode(1 << 26); // D: device file
pub const MODE_NAMED_PIPE: FileMode = FileMode(1 << 25); // p: named pipe (FIFO)
pub const MODE_SOCKET: FileMode = FileMode(1 << 24); // S: Unix domain socket
pub const MODE_SETUID: FileMode = FileMode(1 << 23); // u: setuid
pub const MODE_SETGID: FileMode = FileMode(1 << 22); // g: setgid
pub const MODE_CHAR_DEVICE: FileMode = FileMode(1 << 21); // c: Unix character device
pub const MODE_STICKY: FileMode = FileMode(1 << 20); // t: sticky
pub const MODE_IRREGULAR: FileMode = FileMode(1 << 19); // ?: non-regular file

pub const MODE_TYPE: FileMode = FileMode(
    MODE_DIR.0
        | MODE_SYMLINK.0
        | MODE_NAMED_PIPE.0
        | MODE_SOCKET.0
        | MODE_DEVICE.0
        | MODE_CHAR_DEVICE.0
        | MODE_IRREGULAR.0,
);
pub const MODE_PERM: FileMode = FileMode(0o777); // Unix permission bits

impl std::ops::BitOr for FileMode {
    type Output = FileMode;
    fn bitor(self, other: FileMode) -> FileMode {
        FileMode(self.0 | other.0)
    }
}

impl std::ops::BitOr<u32> for FileMode {
    type Output = FileMode;
    fn bitor(self, other: u32) -> FileMode {
        FileMode(self.0 | other)
    }
}

impl std::ops::BitAnd for FileMode {
    type Output = FileMode;
    fn bitand(self, other: FileMode) -> FileMode {
        FileMode(self.0 & other.0)
    }
}

impl std::ops::BitAnd<u32> for FileMode {
    type Output = FileMode;
    fn bitand(self, other: u32) -> FileMode {
        FileMode(self.0 & other)
    }
}

impl std::ops::Not for FileMode {
    type Output = FileMode;
    fn not(self) -> FileMode {
        FileMode(!self.0)
    }
}

impl FileMode {
    /// IsDir reports whether m describes a directory.
    /// That is, it tests for the [MODE_DIR] bit being set in m.
    pub fn is_dir(&self) -> bool {
        self.0 & MODE_DIR.0 != 0
    }

    /// IsRegular reports whether m describes a regular file.
    /// That is, it tests that no mode type bits are set.
    pub fn is_regular(&self) -> bool {
        self.0 & MODE_TYPE.0 == 0
    }

    /// Perm returns the Unix permission bits in m (m & [MODE_PERM]).
    pub fn perm(&self) -> FileMode {
        FileMode(self.0 & MODE_PERM.0)
    }

    /// Type returns type bits in m (m & [MODE_TYPE]).
    pub fn type_(&self) -> FileMode {
        *self & MODE_TYPE
    }
}

impl fmt::Debug for FileMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for FileMode {
    // Port of FileMode.String: e.g. "drwxr-xr-x", "Lrwxrwxrwx", "-rw-r--r--".
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const STR: &[u8] = b"dalTLDpSugct?";
        let mut buf = [0u8; 32];
        let mut w = 0;
        for (i, &c) in STR.iter().enumerate() {
            if self.0 & (1u32 << (32 - 1 - i as u32)) != 0 {
                buf[w] = c;
                w += 1;
            }
        }
        if w == 0 {
            buf[w] = b'-';
            w += 1;
        }
        const RWX: &[u8] = b"rwxrwxrwx";
        for (i, &c) in RWX.iter().enumerate() {
            if self.0 & (1u32 << (9 - 1 - i as u32)) != 0 {
                buf[w] = c;
            } else {
                buf[w] = b'-';
            }
            w += 1;
        }
        // SAFETY-free: buf contains only ASCII by construction.
        f.write_str(std::str::from_utf8(&buf[..w]).unwrap_or("?"))
    }
}

/// FileInfo is fs.FileInfo: metadata about a file.
/// PORT: returns are owned/`Arc` because trait objects cannot borrow computed
/// names; `sys` carries the Go `any`-typed per-implementation data.
pub trait FileInfo: Send + Sync {
    /// base name of the file
    fn name(&self) -> String;
    /// length in bytes for regular files; system-dependent for others
    fn size(&self) -> i64;
    /// file mode bits
    fn mode(&self) -> FileMode;
    /// modification time
    fn mod_time(&self) -> SystemTime;
    /// abbreviation for Mode().IsDir()
    fn is_dir(&self) -> bool {
        self.mode().is_dir()
    }
    /// underlying data source (can return None)
    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>>;
}

impl fmt::Debug for dyn FileInfo + '_ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} IsDir={} Mode={} Size={} ModTime={:?}",
            self.name(),
            self.is_dir(),
            self.mode(),
            self.size(),
            self.mod_time()
        )
    }
}

/// DirEntry is fs.DirEntry: an entry read from a directory
/// (using the [read_dir] function or a [ReadDirFile]'s read_dir method).
pub trait DirEntry: Send + Sync {
    /// Name returns the name of the file (or subdirectory) described by the entry.
    /// This name is only the final element of the path (the base name), not the entire path.
    fn name(&self) -> String;

    /// IsDir reports whether the entry describes a directory.
    fn is_dir(&self) -> bool;

    /// Type returns the type bits for the entry.
    /// The type bits are a subset of the usual [FileMode] bits, those returned by the
    /// FileMode.type_ method.
    fn type_(&self) -> FileMode;

    /// Info returns the [FileInfo] for the file or subdirectory described by the entry.
    /// The returned FileInfo may be from the time of the original directory read
    /// or from the time of the call to Info. If the file has been removed or renamed
    /// since the directory read, Info may report an error that satisfies
    /// is(ERR_NOT_EXIST).
    fn info(&self) -> Result<Arc<dyn FileInfo>, FsError>;
}

impl fmt::Debug for dyn DirEntry + '_ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} IsDir={} Type={}",
            self.name(),
            self.is_dir(),
            self.type_()
        )
    }
}

/// dirInfo is a DirEntry based on a FileInfo.
struct DirInfo {
    file_info: Arc<dyn FileInfo>,
}

impl DirEntry for DirInfo {
    fn is_dir(&self) -> bool {
        self.file_info.is_dir()
    }

    fn type_(&self) -> FileMode {
        self.file_info.mode().type_()
    }

    fn info(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        Ok(self.file_info.clone())
    }

    fn name(&self) -> String {
        self.file_info.name()
    }
}

/// file_info_to_dir_entry returns a [DirEntry] that returns information from info.
pub fn file_info_to_dir_entry(info: Arc<dyn FileInfo>) -> Arc<dyn DirEntry> {
    Arc::new(DirInfo { file_info: info })
}

/// SeekWhence is the `whence` argument of [Seeker::seek] (io.SeekStart,
/// io.SeekCurrent, io.SeekEnd).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeekWhence {
    Start = 0,
    Current = 1,
    End = 2,
}

/// File is fs.File: the minimum interface required of an open file.
/// Directory files should also implement [ReadDirFile] (see
/// [File::as_read_dir_file]). A file may implement [ReaderAt] or [Seeker]
/// as optimizations.
pub trait File: Send + Sync {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError>;
    /// io.Reader.Read; at end of file this returns Err(EOF).
    fn read(&self, buf: &mut [u8]) -> Result<usize, FsError>;
    fn close(&self) -> Result<(), FsError>;

    /// PORT: Go asserts optional interfaces (`f.(fs.ReadDirFile)`,
    /// `f.(io.Seeker)`, `f.(io.ReaderAt)`) at run time; Rust exposes the
    /// capabilities explicitly instead.
    fn as_read_dir_file(&self) -> Option<&dyn ReadDirFile> {
        None
    }
    fn as_seeker(&self) -> Option<&dyn Seeker> {
        None
    }
    fn as_reader_at(&self) -> Option<&dyn ReaderAt> {
        None
    }
}

/// ReadDirFile is fs.ReadDirFile: a directory [File] whose entries can be
/// reread incrementally.
pub trait ReadDirFile: File {
    /// ReadDir reads the contents of the directory and returns
    /// a slice of up to count [DirEntry] values in directory order.
    /// Subsequent calls on the same file will yield further DirEntry values.
    ///
    /// If count > 0, ReadDir returns at most count DirEntry structures.
    /// In this case, if read_dir returns an empty slice, it will return
    /// Err(EOF).
    ///
    /// If count <= 0, ReadDir returns all the DirEntry values from the directory
    /// in a single slice. In this case, if ReadDir returns an empty slice,
    /// it will return a nil error (Ok).
    fn read_dir(&self, count: i32) -> Result<Vec<Arc<dyn DirEntry>>, FsError>;
}

/// Seeker is io.Seeker.
pub trait Seeker: File {
    fn seek(&self, offset: i64, whence: SeekWhence) -> Result<i64, FsError>;
}

/// ReaderAt is io.ReaderAt.
pub trait ReaderAt: File {
    /// ReadAt reads len(buf) bytes from the file starting at byte offset `offset`.
    /// It returns the number of bytes read. At end of file it returns
    /// Err(EOF) (possibly with n > 0).
    fn read_at(&self, buf: &mut [u8], offset: i64) -> Result<usize, FsError>;
}

/// Fs is fs.FS: a file system with slash-separated paths.
///
/// PORT: Go code probes optional interfaces with type assertions
/// (`fsys.(fs.StatFS)`); here each capability has an explicit hook returning
/// Option. `as_any` serves the `fsys.(*T)` concrete-type assertions.
pub trait Fs: Any + Send + Sync {
    fn open(&self, name: &str) -> Result<Box<dyn File>, FsError>;

    fn as_stat_fs(&self) -> Option<&dyn StatFs> {
        None
    }
    fn as_read_dir_fs(&self) -> Option<&dyn ReadDirFs> {
        None
    }
    fn as_read_file_fs(&self) -> Option<&dyn ReadFileFs> {
        None
    }
    fn as_sub_fs(&self) -> Option<&dyn SubFs> {
        None
    }
    fn as_read_link_fs(&self) -> Option<&dyn ReadLinkFs> {
        None
    }
    fn as_glob_fs(&self) -> Option<&dyn GlobFs> {
        None
    }

    /// `fsys.(iovfs.RealpathFS)` — the traits live in iovfs, matching Go's
    /// package layout; the hook itself is declared here.
    fn as_realpath_fs(&self) -> Option<&dyn crate::iovfs::RealpathFs> {
        None
    }
    /// `fsys.(iovfs.WritableFS)`
    fn as_writable_fs(&self) -> Option<&dyn crate::iovfs::WritableFs> {
        None
    }

    /// `fsys.(*ConcreteType)` — concrete downcast for `Fs` implementations.
    fn as_any(&self) -> &dyn Any;
}

/// StatFs is fs.StatFS: an FS with a Stat method.
pub trait StatFs: Fs {
    fn stat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError>;
}

/// ReadDirFs is fs.ReadDirFS: an FS whose read_dir shortcut returns entries
/// sorted by filename.
pub trait ReadDirFs: Fs {
    fn read_dir(&self, name: &str) -> Result<Vec<Arc<dyn DirEntry>>, FsError>;
}

/// ReadFileFs is fs.ReadFileFS: an FS with a ReadFile method.
pub trait ReadFileFs: Fs {
    fn read_file(&self, name: &str) -> Result<Vec<u8>, FsError>;
}

/// SubFs is fs.SubFS: an FS with a Sub method returning a sub-file-system.
pub trait SubFs: Fs {
    /// Sub returns an [Fs] corresponding to the subtree rooted at dir.
    fn sub(&self, dir: &str) -> Result<Arc<dyn Fs>, FsError>;
}

/// ReadLinkFs is fs.ReadLinkFS: an FS with ReadLink and Lstat.
pub trait ReadLinkFs: Fs {
    /// read_link returns the destination of the named symbolic link.
    fn read_link(&self, name: &str) -> Result<String, FsError>;
    /// lstat returns a [FileInfo] describing the file. If the file is a
    /// symbolic link, lstat returns info about the link itself.
    fn lstat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError>;
}

/// GlobFs is fs.GlobFS. Not implemented by any VFS fs in this port;
/// it exists so that helpers which check for it can do so faithfully.
pub trait GlobFs: Fs {
    fn glob(&self, pattern: &str) -> Result<Vec<String>, FsError>;
}

/// stat is fs.Stat.
pub fn stat(fsys: &dyn Fs, name: &str) -> Result<Arc<dyn FileInfo>, FsError> {
    if let Some(fsys) = fsys.as_stat_fs() {
        return fsys.stat(name);
    }

    let file = fsys.open(name)?;
    let result = file.stat();
    let _ = file.close();
    result
}

/// read_dir is fs.ReadDir: reads the named directory and returns a list of
/// directory entries sorted by filename.
pub fn read_dir(fsys: &dyn Fs, name: &str) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
    if let Some(fsys) = fsys.as_read_dir_fs() {
        return fsys.read_dir(name);
    }
    read_dir_via_open(fsys, name)
}

/// The Open + ReadDirFile fallback used by fs.ReadDir.
pub(crate) fn read_dir_via_open(
    fsys: &dyn Fs,
    name: &str,
) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
    let file = fsys.open(name)?;
    let dir = match file.as_read_dir_file() {
        Some(dir) => dir,
        None => {
            let _ = file.close();
            return Err(path_error(
                "readdir",
                name,
                FsError::Message("not implemented".to_string()),
            ));
        }
    };

    let result = dir.read_dir(-1);
    let _ = file.close();
    let mut list = result?;
    list.sort_by(|a, b| a.name().cmp(&b.name()));
    Ok(list)
}

/// read_file is fs.ReadFile.
pub fn read_file(fsys: &dyn Fs, name: &str) -> Result<Vec<u8>, FsError> {
    if let Some(fsys) = fsys.as_read_file_fs() {
        return fsys.read_file(name);
    }
    read_file_via_open(fsys, name)
}

/// The Open + io.ReadAll fallback used by fs.ReadFile.
pub(crate) fn read_file_via_open(fsys: &dyn Fs, name: &str) -> Result<Vec<u8>, FsError> {
    let file = fsys.open(name)?;

    let mut size = 0;
    if let Ok(info) = file.stat() {
        // PORT: Go guards `int64(int(size64)) == size64`; usize is the
        // same width as int here so the cast can't wrap.
        size = usize::try_from(info.size()).unwrap_or(0);
    }

    let mut data = Vec::with_capacity(size + 1);
    let mut buf = [0u8; 512];
    loop {
        match file.read(&mut buf) {
            Ok(0) => {
                // A read that returns (0, nil) forever would loop; the Go
                // contract is (0, io.EOF) at end of file, but guard anyway.
                break;
            }
            Ok(n) => data.extend_from_slice(&buf[..n]),
            Err(e) if e.is_eof() => break,
            Err(e) => {
                let _ = file.close();
                return Err(e);
            }
        }
    }
    let _ = file.close();
    Ok(data)
}

/// read_all is io.ReadAll over a [File].
pub(crate) fn read_all(file: &dyn File) -> Result<Vec<u8>, FsError> {
    let mut data = Vec::new();
    let mut buf = [0u8; 512];
    loop {
        match file.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => data.extend_from_slice(&buf[..n]),
            Err(e) if e.is_eof() => break,
            Err(e) => return Err(e),
        }
    }
    Ok(data)
}

/// valid_path is fs.ValidPath: reports whether name is a valid path element
/// for an fs.FS.
pub fn valid_path(name: &str) -> bool {
    // PORT: Go checks utf8.ValidString(name); a Rust &str is always valid
    // UTF-8, so that check is a no-op here.

    if name == "." {
        // special case
        return true;
    }

    // Iterate over elements in name, checking each.
    let mut name = name;
    loop {
        let mut i = 0;
        while i < name.len() && name.as_bytes()[i] != b'/' {
            i += 1;
        }
        let elem = &name[..i];
        if elem.is_empty() || elem == "." || elem == ".." {
            return false;
        }
        if i == name.len() {
            return true; // reached clean ending
        }
        name = &name[i + 1..];
    }
}

/// sub is fs.Sub: returns an [Fs] rooted at dir within fsys.
pub fn sub(fsys: &Arc<dyn Fs>, dir: &str) -> Result<Arc<dyn Fs>, FsError> {
    if !valid_path(dir) {
        return Err(path_error("sub", dir, ERR_INVALID));
    }
    if dir == "." {
        return Ok(fsys.clone());
    }
    if let Some(fsys) = fsys.as_sub_fs() {
        return fsys.sub(dir);
    }
    Ok(Arc::new(SubFsImpl {
        fsys: fsys.clone(),
        dir: dir.to_string(),
    }))
}

/// SubFsImpl is fs.subFS.
struct SubFsImpl {
    fsys: Arc<dyn Fs>,
    dir: String,
}

impl SubFsImpl {
    /// full_name maps name to the fully-qualified name dir/name.
    fn full_name(&self, op: &'static str, name: &str) -> Result<String, FsError> {
        if !valid_path(name) {
            return Err(path_error(op, name, ERR_INVALID));
        }
        Ok(path_join(&self.dir, name))
    }

    /// shorten maps name, which should start with self.dir, back to the
    /// suffix after self.dir.
    fn shorten<'a>(&self, name: &'a str) -> Option<&'a str> {
        if name == self.dir {
            return Some(".");
        }
        if name.len() >= self.dir.len() + 2
            && name.as_bytes()[self.dir.len()] == b'/'
            && &name[..self.dir.len()] == self.dir
        {
            return Some(&name[self.dir.len() + 1..]);
        }
        None
    }

    /// fix_err shortens any reported names in PathErrors by stripping self.dir.
    fn fix_err(&self, err: FsError) -> FsError {
        if let FsError::PathError { op, path, err } = err {
            if let Some(short) = self.shorten(&path) {
                return FsError::PathError {
                    op,
                    path: short.to_string(),
                    err,
                };
            }
            return FsError::PathError { op, path, err };
        }
        err
    }
}

impl Fs for SubFsImpl {
    fn open(&self, name: &str) -> Result<Box<dyn File>, FsError> {
        let full = self.full_name("open", name)?;
        self.fsys.open(&full).map_err(|e| self.fix_err(e))
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

impl ReadDirFs for SubFsImpl {
    fn read_dir(&self, name: &str) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        let full = self.full_name("read", name)?;
        read_dir(&*self.fsys, &full).map_err(|e| self.fix_err(e))
    }
}

impl ReadFileFs for SubFsImpl {
    fn read_file(&self, name: &str) -> Result<Vec<u8>, FsError> {
        let full = self.full_name("read", name)?;
        read_file(&*self.fsys, &full).map_err(|e| self.fix_err(e))
    }
}

impl ReadLinkFs for SubFsImpl {
    fn read_link(&self, name: &str) -> Result<String, FsError> {
        let full = self.full_name("readlink", name)?;
        let target = self
            .fsys
            .as_read_link_fs()
            .map(|f| f.read_link(&full))
            .unwrap_or_else(|| Err(ERR_INVALID));
        target.map_err(|e| self.fix_err(e))
    }

    fn lstat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError> {
        let full = self.full_name("lstat", name)?;
        let info = self
            .fsys
            .as_read_link_fs()
            .map(|f| f.lstat(&full))
            .unwrap_or_else(|| Err(ERR_INVALID));
        info.map_err(|e| self.fix_err(e))
    }
}

// POSIX path helpers used by the io/fs ports (Go's `path` package).

/// path.Join
pub fn path_join(dir: &str, name: &str) -> String {
    let joined = if dir.is_empty() {
        name.to_string()
    } else {
        format!("{}/{}", dir, name)
    };
    path_clean(&joined)
}

/// path.Dir
pub fn path_dir(path: &str) -> String {
    let (dir, _) = path_split(path);
    path_clean(dir)
}

/// path.Base
pub fn path_base(path: &str) -> String {
    if path.is_empty() {
        return ".".to_string();
    }
    // Strip trailing slashes.
    let mut path = path;
    while !path.is_empty() && path.ends_with('/') {
        path = &path[..path.len() - 1];
    }
    match path.rfind('/') {
        Some(i) => path[i + 1..].to_string(),
        None => path.to_string(),
    }
}

/// path.IsAbs
pub fn path_is_abs(path: &str) -> bool {
    path.starts_with('/')
}

/// path.Split
pub fn path_split(path: &str) -> (&str, &str) {
    match path.rfind('/') {
        Some(i) => (&path[..i + 1], &path[i + 1..]),
        None => ("", path),
    }
}

/// path.Clean (the lexical dot-dot elimination used by path.Join).
pub fn path_clean(path: &str) -> String {
    if path.is_empty() {
        return ".".to_string();
    }
    let rooted = path.starts_with('/');
    let mut out: Vec<&str> = Vec::new();
    for elem in path.split('/') {
        match elem {
            "" | "." => {}
            ".." => {
                if let Some(last) = out.last() {
                    if *last != ".." {
                        out.pop();
                        continue;
                    }
                }
                if !rooted {
                    out.push("..");
                }
            }
            e => out.push(e),
        }
    }
    let mut result = String::new();
    if rooted {
        result.push('/');
    }
    result.push_str(&out.join("/"));
    if result.is_empty() {
        if rooted {
            return "/".to_string();
        }
        return ".".to_string();
    }
    result
}
