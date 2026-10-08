// Ported from tsc/internal/vfs/vfstest/vfstest.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// fstest is the port of GOROOT testing/fstest (MapFS + TestFS) and
// testing/iotest (TestReader) that the Go vfstest package builds upon.
pub mod fstest;

use std::any::Any;
use std::sync::{Arc, RwLock};
use std::time::{Duration, SystemTime};

use rustc_hash::FxHashMap;
use tsc_tspath::CaseSensitivity;

use crate::fs::{
    self, DirEntry, File, FileInfo, FileMode, Fs, FsError, ReadDirFile, ReaderAt, Seeker,
    MODE_DIR, MODE_SYMLINK,
};
use crate::iovfs::{self, RealpathFs, WritableFs};
use crate::vfs::Vfs;
use self::fstest::{MapFile, MapFs as FstestMapFs};

/// A MapFS is a test VFS backed by an fstest MapFS whose keys are canonical
/// (case-normalized) paths. It tracks symlinks separately so that realpath
/// and broken-symlink behavior match the Go implementation.
///
/// Go: `type MapFS struct { mu; m fstest.MapFS; caseSensitivity; symlinks; clock }`
pub struct MapFs {
    /// mu protects m and symlinks.
    /// A single mutex is sufficient as we only use fstest.MapFs's Open method.
    state: RwLock<MapFsState>,

    /// keys in m are canonicalPaths
    case_sensitivity: CaseSensitivity,

    clock: Arc<dyn Clock>,
}

struct MapFsState {
    m: FstestMapFs,
    symlinks: FxHashMap<String, String>,
}

/// Clock is vfstest.Clock.
pub trait Clock: Send + Sync {
    fn now(&self) -> SystemTime;
    fn since_start(&self) -> Duration;
}

/// clockImpl is vfstest.clockImpl.
struct ClockImpl {
    start: SystemTime,
}

impl Clock for ClockImpl {
    fn now(&self) -> SystemTime {
        SystemTime::now()
    }
    fn since_start(&self) -> Duration {
        SystemTime::now()
            .duration_since(self.start)
            .unwrap_or_default()
    }
}

/// sys is vfstest.sys: the FileInfo::sys payload for map entries, carrying the
/// user-provided Sys plus the entry's realpath (original casing).
#[derive(Debug)]
pub struct Sys {
    pub original: Option<Arc<dyn Any + Send + Sync>>,
    pub realpath: String,
}

/// A file entry for [from_map]: a string, byte slice, or [MapFile].
pub enum TestFile {
    Text(String),
    Bytes(Vec<u8>),
    MapFile(MapFile),
}

impl From<&str> for TestFile {
    fn from(s: &str) -> TestFile {
        TestFile::Text(s.to_string())
    }
}
impl From<String> for TestFile {
    fn from(s: String) -> TestFile {
        TestFile::Text(s)
    }
}
impl From<Vec<u8>> for TestFile {
    fn from(b: Vec<u8>) -> TestFile {
        TestFile::Bytes(b)
    }
}
impl From<&[u8]> for TestFile {
    fn from(b: &[u8]) -> TestFile {
        TestFile::Bytes(b.to_vec())
    }
}
impl From<MapFile> for TestFile {
    fn from(f: MapFile) -> TestFile {
        TestFile::MapFile(f)
    }
}
impl From<&MapFile> for TestFile {
    fn from(f: &MapFile) -> TestFile {
        TestFile::MapFile(f.clone())
    }
}

/// from_map creates a new [Vfs] from a map of paths to file contents.
/// Those file contents may be strings, byte slices, or [MapFile]s.
///
/// The paths must be normalized absolute paths according to the tspath package,
/// without trailing directory separators.
/// The paths must be all POSIX-style or all Windows-style, but not both.
pub fn from_map<I, K, F>(m: I, case_sensitivity: CaseSensitivity) -> Arc<dyn Vfs>
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<TestFile>,
{
    from_map_with_clock(
        m,
        case_sensitivity,
        Arc::new(ClockImpl {
            start: SystemTime::now(),
        }),
    )
}

/// from_map_with_clock is FromMapWithClock.
pub fn from_map_with_clock<I, K, F>(
    m: I,
    case_sensitivity: CaseSensitivity,
    clock: Arc<dyn Clock>,
) -> Arc<dyn Vfs>
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<TestFile>,
{
    let mut posix = false;
    let mut windows = false;

    let mut check_path = |p: &str| {
        if !tsc_tspath::is_rooted_disk_path(p) {
            panic!("non-rooted path {}", fs::go_quote(p));
        }

        if tsc_tspath::remove_trailing_directory_separator(&tsc_tspath::normalize_path(p)) != p {
            panic!("non-normalized path {}", fs::go_quote(p));
        }

        if p.starts_with('/') {
            posix = true;
        } else {
            windows = true;
        }
    };

    let mut input: FxHashMap<String, MapFile> = FxHashMap::default();
    // Sorted creation to ensure times are always guaranteed to be in order.
    let mut keyed: Vec<(String, TestFile)> = m
        .into_iter()
        .map(|(k, f)| (k.into(), f.into()))
        .collect();
    keyed.sort_by(|a, b| compare_paths_by_parts(&a.0, &b.0));
    for (p, f) in keyed {
        check_path(&p);

        let mut file = match f {
            TestFile::Text(s) => MapFile {
                data: Arc::from(s.into_bytes().into_boxed_slice()),
                mode: FileMode(0),
                mod_time: clock.now(),
                sys: None,
            },
            TestFile::Bytes(b) => MapFile {
                data: Arc::from(b.into_boxed_slice()),
                mode: FileMode(0),
                mod_time: clock.now(),
                sys: None,
            },
            TestFile::MapFile(mut f) => {
                f.mod_time = clock.now();
                f
            }
        };

        if file.mode & MODE_SYMLINK != FileMode(0) {
            let mut target = String::from_utf8_lossy(&file.data).into_owned();
            check_path(&target);

            if let Some(rest) = target.strip_prefix('/') {
                target = rest.to_string();
            }
            file.data = Arc::from(target.into_bytes().into_boxed_slice());
        }

        let p = p.strip_prefix('/').unwrap_or(&p).to_string();
        input.insert(p, file);
    }

    if posix && windows {
        panic!("mixed posix and windows paths");
    }

    let map_fs = convert_map_fs(input, case_sensitivity, clock);
    iovfs::from(Arc::new(map_fs), case_sensitivity) as Arc<dyn Vfs>
}

fn convert_map_fs(
    input: FxHashMap<String, MapFile>,
    case_sensitivity: CaseSensitivity,
    clock: Arc<dyn Clock>,
) -> MapFs {
    let m = MapFs {
        state: RwLock::new(MapFsState {
            m: FstestMapFs {
                map: FxHashMap::with_capacity_and_hasher(input.len(), Default::default()),
            },
            symlinks: FxHashMap::default(),
        }),
        case_sensitivity,
        clock,
    };

    // Verify that the input is well-formed.
    let mut canonical_paths: FxHashMap<String, String> =
        FxHashMap::with_capacity_and_hasher(input.len(), Default::default());
    for path in input.keys() {
        let canonical = m.get_canonical_path(path);
        if let Some(other) = canonical_paths.get(&canonical) {
            // Ensure consistent panic messages
            let (a, b) = if path < other {
                (path.as_str(), other.as_str())
            } else {
                (other.as_str(), path.as_str())
            };
            panic!(
                "duplicate path: {:?} and {:?} have the same canonical path",
                a, b
            );
        }
        canonical_paths.insert(canonical, path.clone());
    }

    // Sort the input by depth and path so we ensure parent dirs are created
    // before their children, if explicitly specified by the input.
    let mut input_keys: Vec<String> = input.keys().cloned().collect();
    input_keys.sort_by(|a, b| compare_paths_by_parts(a, b));

    for p in input_keys {
        let file = input[&p].clone();

        // Create all missing intermediate directories so we can attach the realpath to each of them.
        // fstest.MapFS doesn't require this as it synthesizes directories on the fly, but it's a lot
        // harder to reapply a realpath onto those when we're deep in some FileInfo method.
        if !dir_name(&p).is_empty() {
            let dir = dir_name(&p);
            if let Err(err) = m.mkdir_all(&dir, FileMode(0o777)) {
                panic!("failed to create intermediate directories for {:?}: {}", p, err);
            }
        }
        let canonical = m.get_canonical_path(&p);
        m.set_entry(&p, &canonical, file);
    }

    m
}

/// comparePathsByParts.
fn compare_paths_by_parts(a: &str, b: &str) -> std::cmp::Ordering {
    let mut a = a;
    let mut b = b;
    loop {
        // strings.Cut(a, "/")
        let (a_start, a_end, a_ok) = match a.find('/') {
            Some(i) => (&a[..i], &a[i + 1..], true),
            None => (a, "", false),
        };
        let (b_start, b_end, b_ok) = match b.find('/') {
            Some(i) => (&b[..i], &b[i + 1..], true),
            None => (b, "", false),
        };

        if !a_ok || !b_ok {
            return a.cmp(b);
        }

        match a_start.cmp(b_start) {
            std::cmp::Ordering::Equal => {}
            ord => return ord,
        }

        a = a_end;
        b = b_end;
    }
}

impl MapFs {
    fn get_canonical_path(&self, p: &str) -> String {
        self.case_sensitivity.canonicalize(p).into_owned()
    }

    /// remove is vfstest.MapFS.remove.
    fn remove(&self, path: &str) {
        let mut state = self.state.write().unwrap();
        let canonical = self.get_canonical_path(path);
        let canonical_string = canonical.clone();
        let Some(file_info) = state.m.map.get(&canonical_string).cloned() else {
            // file does not exist
            return;
        };
        state.m.map.remove(&canonical_string);
        state.symlinks.remove(&canonical);

        if file_info.mode.is_dir() {
            let prefix = format!("{}/", canonical_string);
            let keys: Vec<String> = state
                .m
                .map
                .keys()
                .filter(|p| p.starts_with(&prefix))
                .cloned()
                .collect();
            for path in keys {
                state.m.map.remove(&path);
                state.symlinks.remove(&path);
            }
        }
    }

    /// Symlink creates a MapFile describing a symlink to target.
    fn get_following_symlinks(
        &self,
        state: &MapFsState,
        p: &str,
    ) -> Result<(MapFile, String), FsError> {
        self.get_following_symlinks_worker(state, p, "", "")
    }

    fn get_following_symlinks_worker(
        &self,
        state: &MapFsState,
        p: &str,
        symlink_from: &str,
        symlink_to: &str,
    ) -> Result<(MapFile, String), FsError> {
        if let Some(file) = state.m.map.get(p) {
            if file.mode & MODE_SYMLINK == FileMode(0) {
                return Ok((file.clone(), p.to_string()));
            }
        }

        if let Some(target) = state.symlinks.get(p) {
            return self.get_following_symlinks_worker(state, target, p, target);
        }

        // This could be a path underneath a symlinked directory.
        // PORT: Go iterates the symlinks map in nondeterministic order; if
        // multiple symlinked directories could prefix p the result could vary.
        // Here the longest prefix wins deterministically.
        let mut best: Option<(&String, &String)> = None;
        for (other, target) in &state.symlinks {
            if other.len() < p.len()
                && p.starts_with(other.as_str())
                && p.as_bytes()[other.len()] == b'/'
            {
                match best {
                    Some((b, _)) if b.len() >= other.len() => {}
                    _ => best = Some((other, target)),
                }
            }
        }
        if let Some((other, target)) = best {
            let joined = format!("{}{}", target, &p[other.len()..]);
            return self.get_following_symlinks_worker(state, &joined, other, target);
        }

        let mut err = FsError::NotExist;
        if !symlink_from.is_empty() {
            err = FsError::BrokenSymlink {
                from: symlink_from.to_string(),
                to: symlink_to.to_string(),
            };
        }
        Err(err)
    }

    fn set_entry(&self, realpath: &str, canonical: &str, mut file: MapFile) {
        if realpath.is_empty() || canonical.is_empty() {
            panic!("empty path");
        }

        file.sys = Some(Arc::new(Sys {
            original: file.sys.take(),
            realpath: realpath.to_string(),
        }));
        let mut state = self.state.write().unwrap();
        state.m.map.insert(canonical.to_string(), file.clone());

        if file.mode & MODE_SYMLINK != FileMode(0) {
            let target = String::from_utf8_lossy(&file.data).into_owned();
            let canonical_target = self.get_canonical_path(&target);
            state.symlinks.insert(canonical.to_string(), canonical_target);
        }
    }

    /// mkdirAll is vfstest.MapFS.mkdirAll.
    fn mkdir_all(&self, p: &str, perm: FileMode) -> Result<(), FsError> {
        if p.is_empty() {
            panic!("empty path");
        }

        // Fast path; already exists.
        {
            let state = self.state.read().unwrap();
            if let Ok((other, _)) =
                self.get_following_symlinks(&state, &self.get_canonical_path(p))
            {
                if !other.mode.is_dir() {
                    return Err(FsError::Message(format!(
                        "mkdir {}: path exists but is not a directory",
                        fs::go_quote(p)
                    )));
                }
                return Ok(());
            }
        }

        let mut to_create: Vec<String> = Vec::new();
        let mut p = p.to_string();
        let mut offset = 0usize;
        loop {
            let (dir, rest) = split_path(&p, offset);
            let canonical = self.get_canonical_path(&dir);
            let state = self.state.read().unwrap();
            match self.get_following_symlinks(&state, &canonical) {
                Err(err) => {
                    drop(state);
                    if !err.is_not_exist() {
                        return Err(err);
                    }
                    to_create.push(dir.clone());
                }
                Ok((other, other_path)) => {
                    if !other.mode.is_dir() {
                        drop(state);
                        return Err(FsError::Message(format!(
                            "mkdir {}: path exists but is not a directory",
                            fs::go_quote(&other_path)
                        )));
                    }
                    if canonical != other_path {
                        // We have a symlinked parent, reset and start again.
                        let realpath = other
                            .sys
                            .as_ref()
                            .and_then(|s| s.downcast_ref::<Sys>())
                            .map(|s| s.realpath.clone())
                            .unwrap_or_default();
                        drop(state);
                        p = format!("{}/{}", realpath, rest);
                        to_create.clear();
                        offset = 0;
                        continue;
                    }
                }
            }
            if rest.is_empty() {
                break;
            }
            offset = dir.len() + 1;
        }

        for dir in to_create {
            let canonical = self.get_canonical_path(&dir);
            self.set_entry(
                &dir,
                &canonical,
                MapFile {
                    data: Arc::from(&[][..]),
                    mode: MODE_DIR | (perm & !UMASK),
                    mod_time: self.clock.now(),
                    sys: None,
                },
            );
        }
        Ok(())
    }
}

/// splitPath.
fn split_path(s: &str, offset: usize) -> (String, String) {
    match s[offset..].find('/') {
        None => (s.to_string(), String::new()),
        Some(idx) => (
            s[..idx + offset].to_string(),
            s[idx + 1 + offset..].to_string(),
        ),
    }
}

/// dirName is path.Split + TrimSuffix(dir, "/") — note: no path cleaning.
fn dir_name(p: &str) -> String {
    match p.rfind('/') {
        Some(i) => p[..i].to_string(),
        None => String::new(),
    }
}

/// baseName.
fn base_name(p: &str) -> String {
    fs::path_base(p).to_string()
}

const UMASK: FileMode = FileMode(0o022);

/// fileInfo is vfstest.fileInfo: wraps a FileInfo, restoring the original
/// realpath'd name and the user's Sys value.
struct VfsFileInfo {
    info: Arc<dyn FileInfo>,
    sys: Option<Arc<dyn Any + Send + Sync>>,
    realpath: String,
}

impl FileInfo for VfsFileInfo {
    fn name(&self) -> String {
        base_name(&self.realpath)
    }
    fn size(&self) -> i64 {
        self.info.size()
    }
    fn mode(&self) -> FileMode {
        self.info.mode()
    }
    fn mod_time(&self) -> SystemTime {
        self.info.mod_time()
    }
    fn is_dir(&self) -> bool {
        self.info.is_dir()
    }
    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>> {
        self.sys.clone()
    }
}

fn convert_info(info: &Arc<dyn FileInfo>) -> Option<Arc<VfsFileInfo>> {
    let sys_any = info.sys()?;
    let sys = sys_any.downcast_ref::<Sys>()?;
    Some(Arc::new(VfsFileInfo {
        info: info.clone(),
        sys: sys.original.clone(),
        realpath: sys.realpath.clone(),
    }))
}

/// file is vfstest.file: a File whose Stat returns the corrected FileInfo.
struct WrappedFile {
    inner: Box<dyn File>,
    file_info: Arc<VfsFileInfo>,
}

impl File for WrappedFile {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        Ok(self.file_info.clone())
    }
    fn read(&self, buf: &mut [u8]) -> Result<usize, FsError> {
        self.inner.read(buf)
    }
    fn close(&self) -> Result<(), FsError> {
        self.inner.close()
    }
    fn as_seeker(&self) -> Option<&dyn Seeker> {
        self.inner.as_seeker()
    }
    fn as_reader_at(&self) -> Option<&dyn ReaderAt> {
        self.inner.as_reader_at()
    }
}

/// readDirFile is vfstest.readDirFile.
struct WrappedReadDirFile {
    inner: Box<dyn File>,
    file_info: Arc<VfsFileInfo>,
}

impl File for WrappedReadDirFile {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        Ok(self.file_info.clone())
    }
    fn read(&self, buf: &mut [u8]) -> Result<usize, FsError> {
        self.inner.read(buf)
    }
    fn close(&self) -> Result<(), FsError> {
        self.inner.close()
    }
    fn as_read_dir_file(&self) -> Option<&dyn ReadDirFile> {
        Some(self)
    }
}

impl ReadDirFile for WrappedReadDirFile {
    fn read_dir(&self, n: i32) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        let rd = match self.inner.as_read_dir_file() {
            Some(rd) => rd,
            None => {
                return Err(fs::path_error(
                    "readdir",
                    "",
                    FsError::Message("not implemented".to_string()),
                ))
            }
        };
        let list = rd.read_dir(n)?;

        let mut entries: Vec<Arc<dyn DirEntry>> = Vec::with_capacity(list.len());
        for entry in list {
            let info = entry.info().map_err(|e| {
                // Go: must(entry.Info()) panics; convert to error to avoid
                // poisoning the fs lock.
                FsError::Message(format!("entry.Info: {}", e))
            })?;
            match convert_info(&info) {
                None => panic!("unexpected synthesized dir: {:?}", info.name()),
                Some(new_info) => {
                    entries.push(fs::file_info_to_dir_entry(new_info as Arc<dyn FileInfo>))
                }
            }
        }
        Ok(entries)
    }
}

impl Fs for MapFs {
    fn open(&self, name: &str) -> Result<Box<dyn File>, FsError> {
        let state = self.state.read().unwrap();

        let canonical = self.get_canonical_path(name);
        // Go: _, cp, _ := m.getFollowingSymlinks(...) — the error is ignored.
        let cp = match self.get_following_symlinks(&state, &canonical) {
            Ok((_, cp)) => cp,
            Err(_) => canonical,
        };

        // m.open(cp)
        let f = state.m.open(&cp)?;

        let info = f.stat()?;

        match convert_info(&info) {
            None => {
                // This is a synthesized dir.
                if name != "." {
                    panic!("unexpected synthesized dir: {:?}", name);
                }
                if f.as_read_dir_file().is_none() {
                    return Err(fs::path_error(
                        "readdir",
                        name,
                        FsError::Message("not implemented".to_string()),
                    ));
                }
                Ok(Box::new(RootDirFile {
                    inner: f,
                    realpath: ".".to_string(),
                }))
            }
            Some(new_info) => {
                if f.as_read_dir_file().is_some() {
                    Ok(Box::new(WrappedReadDirFile {
                        inner: f,
                        file_info: new_info,
                    }))
                } else {
                    Ok(Box::new(WrappedFile {
                        inner: f,
                        file_info: new_info,
                    }))
                }
            }
        }
    }

    fn as_realpath_fs(&self) -> Option<&dyn RealpathFs> {
        Some(self)
    }

    fn as_writable_fs(&self) -> Option<&dyn WritableFs> {
        Some(self)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// RootDirFile handles the synthesized "." root, which has no Sys entry.
struct RootDirFile {
    inner: Box<dyn File>,
    realpath: String,
}

impl File for RootDirFile {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        let info = self.inner.stat()?;
        let sys = info.sys();
        Ok(Arc::new(VfsFileInfo {
            info,
            sys,
            realpath: self.realpath.clone(),
        }))
    }
    fn read(&self, buf: &mut [u8]) -> Result<usize, FsError> {
        self.inner.read(buf)
    }
    fn close(&self) -> Result<(), FsError> {
        self.inner.close()
    }
    fn as_read_dir_file(&self) -> Option<&dyn ReadDirFile> {
        Some(self)
    }
}

impl ReadDirFile for RootDirFile {
    fn read_dir(&self, n: i32) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        let rd = self.inner.as_read_dir_file().unwrap();
        let list = rd.read_dir(n)?;
        let mut entries: Vec<Arc<dyn DirEntry>> = Vec::with_capacity(list.len());
        for entry in list {
            let info = entry.info().map_err(|e| {
                FsError::Message(format!("entry.Info: {}", e))
            })?;
            match convert_info(&info) {
                None => panic!("unexpected synthesized dir: {:?}", info.name()),
                Some(new_info) => {
                    entries.push(fs::file_info_to_dir_entry(new_info as Arc<dyn FileInfo>))
                }
            }
        }
        Ok(entries)
    }
}

impl RealpathFs for MapFs {
    fn realpath(&self, name: &str) -> Result<String, FsError> {
        let state = self.state.read().unwrap();
        let (file, _) =
            self.get_following_symlinks(&state, &self.get_canonical_path(name))?;
        // Go: file.Sys.(*sys).realpath — every stored entry has a sys.
        file.sys
            .and_then(|s| s.downcast_ref::<Sys>().map(|s| s.realpath.clone()))
            .ok_or_else(|| FsError::Message("vfstest: entry missing sys".to_string()))
    }
}

impl WritableFs for MapFs {
    fn mkdir_all(&self, path: &str, perm: FileMode) -> Result<(), FsError> {
        self.mkdir_all(path, perm)
    }

    fn write_file(&self, path: &str, data: &str, perm: FileMode) -> Result<(), FsError> {
        if !dir_name(path).is_empty() {
            let parent = dir_name(path);
            let canonical = self.get_canonical_path(&parent);
            let state = self.state.read().unwrap();
            match self.get_following_symlinks(&state, &canonical) {
                Err(err) => {
                    return Err(FsError::Message(format!(
                        "write {}: {}",
                        fs::go_quote(path),
                        err
                    )))
                }
                Ok((parent_file, _)) => {
                    if !parent_file.mode.is_dir() {
                        return Err(FsError::Message(format!(
                            "write {}: parent path exists but is not a directory",
                            fs::go_quote(path)
                        )));
                    }
                }
            }
        }

        let canonical = self.get_canonical_path(path);
        let cp;
        {
            let state = self.state.read().unwrap();
            match self.get_following_symlinks(&state, &canonical) {
                Err(err) => {
                    if !err.is_not_exist() && !err.is_broken_symlink() {
                        // No other errors are possible.
                        panic!("{}", err);
                    }
                    cp = canonical.clone();
                }
                Ok((file, resolved)) => {
                    if !file.mode.is_regular() {
                        return Err(FsError::Message(format!(
                            "write {}: path exists but is not a regular file",
                            fs::go_quote(path)
                        )));
                    }
                    cp = resolved;
                }
            }
        }

        self.set_entry(
            path,
            &cp,
            MapFile {
                data: Arc::from(data.as_bytes().to_vec().into_boxed_slice()),
                mod_time: self.clock.now(),
                mode: perm & !UMASK,
                sys: None,
            },
        );
        Ok(())
    }

    fn append_file(&self, path: &str, data: &str, perm: FileMode) -> Result<(), FsError> {
        if !dir_name(path).is_empty() {
            let parent = dir_name(path);
            let canonical = self.get_canonical_path(&parent);
            let state = self.state.read().unwrap();
            match self.get_following_symlinks(&state, &canonical) {
                Err(err) => {
                    return Err(FsError::Message(format!(
                        "append {}: {}",
                        fs::go_quote(path),
                        err
                    )))
                }
                Ok((parent_file, _)) => {
                    if !parent_file.mode.is_dir() {
                        return Err(FsError::Message(format!(
                            "append {}: parent path exists but is not a directory",
                            fs::go_quote(path)
                        )));
                    }
                }
            }
        }

        let mut existing: Vec<u8> = Vec::new();
        let mut existing_mode = FileMode(0);
        let canonical = self.get_canonical_path(path);
        let cp;
        {
            let state = self.state.read().unwrap();
            match self.get_following_symlinks(&state, &canonical) {
                Err(err) => {
                    if !err.is_not_exist() && !err.is_broken_symlink() {
                        // No other errors are possible.
                        panic!("{}", err);
                    }
                    cp = canonical.clone();
                }
                Ok((file, resolved)) => {
                    if !file.mode.is_regular() {
                        return Err(FsError::Message(format!(
                            "append {}: path exists but is not a regular file",
                            fs::go_quote(path)
                        )));
                    }
                    existing = file.data.to_vec();
                    existing_mode = file.mode;
                    cp = resolved;
                }
            }
        }

        let mut combined = Vec::with_capacity(existing.len() + data.len());
        combined.extend_from_slice(&existing);
        combined.extend_from_slice(data.as_bytes());

        let mode = if existing_mode == FileMode(0) {
            perm & !UMASK
        } else {
            existing_mode
        };

        self.set_entry(
            path,
            &cp,
            MapFile {
                data: Arc::from(combined.into_boxed_slice()),
                mod_time: self.clock.now(),
                mode,
                sys: None,
            },
        );
        Ok(())
    }

    fn remove(&self, path: &str) -> Result<(), FsError> {
        self.remove(path);
        Ok(())
    }

    fn chtimes(&self, path: &str, _a_time: SystemTime, m_time: SystemTime) -> Result<(), FsError> {
        let mut state = self.state.write().unwrap();
        let canonical = self.get_canonical_path(path);
        match state.m.map.get_mut(&canonical) {
            None => Err(FsError::NotExist),
            Some(file_info) => {
                file_info.mod_time = m_time;
                Ok(())
            }
        }
    }
}

impl MapFs {
    /// AddSymlink adds a symlink entry pointing at target.
    pub fn add_symlink(&self, path: &str, target: &str) {
        let canonical = self.get_canonical_path(path);
        self.set_entry(
            path,
            &canonical,
            MapFile {
                data: Arc::from(target.as_bytes().to_vec().into_boxed_slice()),
                mode: MODE_SYMLINK,
                mod_time: SystemTime::UNIX_EPOCH,
                sys: None,
            },
        );
    }

    /// GetTargetOfSymlink returns the symlink's target.
    pub fn get_target_of_symlink(&self, path: &str) -> Option<String> {
        let path = path.strip_prefix('/').unwrap_or(path);
        let state = self.state.read().unwrap();
        let canonical = self.get_canonical_path(path);
        if let Some(file_info) = state.m.map.get(&canonical) {
            if file_info.mode & MODE_SYMLINK != FileMode(0) {
                return Some(format!("/{}", String::from_utf8_lossy(&file_info.data)));
            }
        }
        None
    }

    /// GetModTime returns the mod time of path, or the zero time if absent.
    pub fn get_mod_time(&self, path: &str) -> SystemTime {
        let path = path.strip_prefix('/').unwrap_or(path);
        let state = self.state.read().unwrap();
        let canonical = self.get_canonical_path(path);
        match state.m.map.get(&canonical) {
            Some(file_info) => file_info.mod_time,
            None => SystemTime::UNIX_EPOCH,
        }
    }

    /// Entries yields each (realpath, MapFile) pair sorted by path parts.
    pub fn entries(&self) -> Vec<(String, MapFile)> {
        let state = self.state.read().unwrap();
        let mut input_keys: Vec<String> = state.m.map.keys().cloned().collect();
        input_keys.sort_by(|a, b| compare_paths_by_parts(a, b));
        let mut out = Vec::with_capacity(input_keys.len());
        for p in input_keys {
            let file = state.m.map[&p].clone();
            let mut path = file
                .sys
                .as_ref()
                .and_then(|s| s.downcast_ref::<Sys>())
                .map(|s| s.realpath.clone())
                .unwrap_or_default();
            if !tsc_tspath::path_is_absolute(&path) {
                path = format!("/{}", path);
            }
            out.push((path, file));
        }
        out
    }

    /// GetFileInfo returns the MapFile for path.
    pub fn get_file_info(&self, path: &str) -> Option<MapFile> {
        let path = path.strip_prefix('/').unwrap_or(path);
        let state = self.state.read().unwrap();
        let canonical = self.get_canonical_path(path);
        state.m.map.get(&canonical).cloned()
    }
}

/// Symlink creates a [MapFile] describing a symlink to target.
pub fn symlink(target: &str) -> MapFile {
    MapFile {
        data: Arc::from(target.as_bytes().to_vec().into_boxed_slice()),
        mode: MODE_SYMLINK,
        mod_time: SystemTime::UNIX_EPOCH,
        sys: None,
    }
}
