// Ported from GOROOT testing/fstest/mapfs.go + testfs.go and
// testing/iotest/reader.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's testing/fstest is stdlib, not part of tsc/internal/vfs, but
// vfstest is implemented on top of fstest.MapFS and its tests rely on
// fstest.TestFS, so both are ported here.
//
// The Go MapFS is `map[string]*MapFile`; here it is a struct wrapping an
// FxHashMap<String, MapFile>. Go's *MapFile pointer sharing means an open
// file observes later in-place mutations (e.g. Chtimes) of the map entry;
// our cloned MapFile does not. This is observable only through the
// (unsupported) pattern of stat-ing an open file after mutating the map.
//
// GlobFS is not implemented (Go's MapFS implements it via fs.Glob over
// path.Match); nothing in the VFS uses it, and TestFS's glob check no-ops
// without it.

use std::any::Any;
use std::collections::HashSet;
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use rustc_hash::FxHashMap;

use crate::fs::{
    self, DirEntry, File, FileInfo, FileMode, Fs, FsError, ReadDirFile, ReadDirFs,
    ReadFileFs, ReadLinkFs, ReaderAt, SeekWhence, Seeker, StatFs, MODE_DIR,
    MODE_SYMLINK,
};

/// A MapFs is a simple in-memory file system for use in tests,
/// represented as a map from path names (arguments to Open)
/// to information about the files, directories, or symbolic links they represent.
///
/// The map need not include parent directories for files contained
/// in the map; those will be synthesized if needed.
/// But a directory can still be included by setting the [MapFile::mode]'s
/// [MODE_DIR] bit; this may be necessary for detailed control over the
/// directory's [FileInfo] or to create an empty directory.
#[derive(Clone, Default)]
pub struct MapFs {
    pub map: FxHashMap<String, MapFile>,
}

impl<K: AsRef<str>> FromIterator<(K, MapFile)> for MapFs {
    fn from_iter<T: IntoIterator<Item = (K, MapFile)>>(iter: T) -> Self {
        MapFs {
            map: iter
                .into_iter()
                .map(|(k, v)| (k.as_ref().to_string(), v))
                .collect(),
        }
    }
}

impl IntoIterator for MapFs {
    type Item = (String, MapFile);
    type IntoIter = std::collections::hash_map::IntoIter<String, MapFile>;
    fn into_iter(self) -> Self::IntoIter {
        // FxHashMap iterates like std HashMap.
        self.map.into_iter().collect::<FxHashMap<_, _>>().into_iter()
    }
}

/// A MapFile describes a single file in a [MapFs].
#[derive(Clone)]
pub struct MapFile {
    pub data: Arc<[u8]>,      // file content or symlink destination
    pub mode: FileMode,       // fs.FileInfo.Mode
    pub mod_time: SystemTime, // fs.FileInfo.ModTime
    pub sys: Option<Arc<dyn Any + Send + Sync>>, // fs.FileInfo.Sys
}

impl MapFile {
    pub fn new(data: impl Into<Arc<[u8]>>) -> MapFile {
        MapFile {
            data: data.into(),
            mode: FileMode(0),
            mod_time: SystemTime::UNIX_EPOCH,
            sys: None,
        }
    }
}

impl Fs for MapFs {
    /// Open opens the named file after following any symbolic links.
    fn open(&self, name: &str) -> Result<Box<dyn File>, FsError> {
        if !fs::valid_path(name) {
            return Err(fs::path_error("open", name, FsError::NotExist));
        }
        let Some(real_name) = self.resolve_symlinks(name) else {
            return Err(fs::path_error("open", name, FsError::NotExist));
        };

        let file = self.map.get(&real_name);
        if let Some(file) = file {
            if file.mode & MODE_DIR == FileMode(0) {
                // Ordinary file
                return Ok(Box::new(OpenMapFile {
                    path: name.to_string(),
                    map_file_info: MapFileInfo::new(fs::path_base(name), file.clone()),
                    offset: Mutex::new(0),
                }));
            }
        }

        // Directory, possibly synthesized.
        // Note that file can be nil here: the map need not contain explicit parent directories for all its files.
        // But file can also be non-nil, in case the user wants to set metadata for the directory explicitly.
        // Either way, we need to construct the list of children of this directory.
        let mut list: Vec<MapFileInfo> = Vec::new();
        let mut need: HashSet<String> = HashSet::new();
        if real_name == "." {
            for (fname, f) in &self.map {
                match fname.find('/') {
                    None => {
                        if fname != "." {
                            list.push(MapFileInfo::new(fname.clone(), f.clone()));
                        }
                    }
                    Some(i) => {
                        need.insert(fname[..i].to_string());
                    }
                }
            }
        } else {
            let prefix = format!("{}/", real_name);
            for (fname, f) in &self.map {
                if let Some(felem) = fname.strip_prefix(&prefix) {
                    match felem.find('/') {
                        None => {
                            list.push(MapFileInfo::new(felem.to_string(), f.clone()));
                        }
                        Some(i) => {
                            need.insert(felem[..i].to_string());
                        }
                    }
                }
            }
            // If the directory name is not in the map,
            // and there are no children of the name in the map,
            // then the directory is treated as not existing.
            if file.is_none() && list.is_empty() && need.is_empty() {
                return Err(fs::path_error("open", name, FsError::NotExist));
            }
        }
        for fi in &list {
            need.remove(&fi.name);
        }
        for name in need {
            list.push(MapFileInfo::new(
                name,
                MapFile {
                    data: Arc::from(&[][..]),
                    mode: MODE_DIR | FileMode(0o555),
                    mod_time: SystemTime::UNIX_EPOCH,
                    sys: None,
                },
            ));
        }
        list.sort_by(|a, b| a.name.cmp(&b.name));

        let file = match file {
            Some(file) => file.clone(),
            None => MapFile {
                data: Arc::from(&[][..]),
                mode: MODE_DIR | FileMode(0o555),
                mod_time: SystemTime::UNIX_EPOCH,
                sys: None,
            },
        };
        let elem = if name == "." {
            "."
        } else {
            &name[name.rfind('/').map(|i| i + 1).unwrap_or(0)..]
        };
        Ok(Box::new(MapDir {
            path: name.to_string(),
            map_file_info: MapFileInfo::new(elem.to_string(), file),
            entry: list,
            offset: Mutex::new(0),
        }))
    }

    // Go's MapFS implements StatFS/ReadDirFS/ReadFileFS via fsOnly wrappers
    // that route back through Open; see the impls at the bottom of this file.
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

impl MapFs {
    fn resolve_symlinks(&self, name: &str) -> Option<String> {
        // Fast path: if a symlink is in the map, resolve it.
        if let Some(file) = self.map.get(name) {
            if file.mode.type_() == MODE_SYMLINK {
                let target = String::from_utf8_lossy(&file.data).into_owned();
                if fs::path_is_abs(&target) {
                    return None;
                }
                return self.resolve_symlinks(&fs::path_join(&fs::path_dir(name), &target));
            }
        }

        // Check if each parent directory (starting at root) is a symlink.
        let mut i = 0;
        let name_bytes = name.as_bytes();
        while i < name_bytes.len() {
            let dir;
            match name[i..].find('/') {
                None => {
                    dir = name;
                    i = name.len();
                }
                Some(j) => {
                    dir = &name[..i + j];
                    i += j;
                }
            }
            if let Some(file) = self.map.get(dir) {
                if file.mode.type_() == MODE_SYMLINK {
                    let target = String::from_utf8_lossy(&file.data).into_owned();
                    if fs::path_is_abs(&target) {
                        return None;
                    }
                    let joined = fs::path_join(&fs::path_dir(dir), &target) + &name[i..];
                    return self.resolve_symlinks(&joined);
                }
            }
            i += 1; // len("/")
        }
        if fs::valid_path(name) {
            Some(name.to_string())
        } else {
            None
        }
    }
}

impl ReadLinkFs for MapFs {
    /// ReadLink returns the destination of the named symbolic link.
    fn read_link(&self, name: &str) -> Result<String, FsError> {
        let info = self
            .lstat_inner(name)
            .ok_or_else(|| fs::path_error("readlink", name, FsError::NotExist))?;
        if info.f.mode.type_() != MODE_SYMLINK {
            return Err(fs::path_error("readlink", name, FsError::Invalid));
        }
        Ok(String::from_utf8_lossy(&info.f.data).into_owned())
    }

    /// Lstat returns a FileInfo describing the named file.
    /// If the file is a symbolic link, the returned FileInfo describes the symbolic link.
    /// Lstat makes no attempt to follow the link.
    fn lstat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError> {
        match self.lstat_inner(name) {
            Some(info) => Ok(Arc::new(info)),
            None => Err(fs::path_error("lstat", name, FsError::NotExist)),
        }
    }
}

impl MapFs {
    fn lstat_inner(&self, name: &str) -> Option<MapFileInfo> {
        if !fs::valid_path(name) {
            return None;
        }
        let real_dir = self.resolve_symlinks(&fs::path_dir(name))?;
        let elem = fs::path_base(name);
        let real_name = fs::path_join(&real_dir, &elem);

        if let Some(file) = self.map.get(&real_name) {
            return Some(MapFileInfo::new(elem, file.clone()));
        }

        if real_name == "." {
            return Some(MapFileInfo::new(
                elem,
                MapFile {
                    data: Arc::from(&[][..]),
                    mode: MODE_DIR | FileMode(0o555),
                    mod_time: SystemTime::UNIX_EPOCH,
                    sys: None,
                },
            ));
        }
        // Maybe a directory.
        let prefix = format!("{}/", real_name);
        for fname in self.map.keys() {
            if fname.starts_with(&prefix) {
                return Some(MapFileInfo::new(
                    elem,
                    MapFile {
                        data: Arc::from(&[][..]),
                        mode: MODE_DIR | FileMode(0o555),
                        mod_time: SystemTime::UNIX_EPOCH,
                        sys: None,
                    },
                ));
            }
        }
        // If the directory name is not in the map,
        // and there are no children of the name in the map,
        // then the directory is treated as not existing.
        None
    }
}

/// MapFileInfo implements fs.FileInfo and fs.DirEntry for a given map file.
#[derive(Clone)]
pub(crate) struct MapFileInfo {
    pub(crate) name: String,
    pub(crate) f: MapFile,
}

impl MapFileInfo {
    fn new(name: String, f: MapFile) -> MapFileInfo {
        MapFileInfo { name, f }
    }
}

impl FileInfo for MapFileInfo {
    fn name(&self) -> String {
        fs::path_base(&self.name)
    }
    fn size(&self) -> i64 {
        self.f.data.len() as i64
    }
    fn mode(&self) -> FileMode {
        self.f.mode
    }
    fn mod_time(&self) -> SystemTime {
        self.f.mod_time
    }
    fn is_dir(&self) -> bool {
        self.f.mode & MODE_DIR != FileMode(0)
    }
    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>> {
        self.f.sys.clone()
    }
}

impl DirEntry for MapFileInfo {
    fn name(&self) -> String {
        fs::path_base(&self.name)
    }
    fn is_dir(&self) -> bool {
        <Self as FileInfo>::is_dir(self)
    }
    fn type_(&self) -> FileMode {
        self.f.mode.type_()
    }
    fn info(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        Ok(Arc::new(self.clone()))
    }
}

/// An OpenMapFile is a regular (non-directory) fs.File open for reading.
struct OpenMapFile {
    path: String,
    map_file_info: MapFileInfo,
    offset: Mutex<i64>,
}

impl File for OpenMapFile {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        Ok(Arc::new(self.map_file_info.clone()))
    }

    fn close(&self) -> Result<(), FsError> {
        Ok(())
    }

    fn read(&self, b: &mut [u8]) -> Result<usize, FsError> {
        let mut offset = self.offset.lock().unwrap();
        if *offset >= self.map_file_info.f.data.len() as i64 {
            return Err(FsError::Eof);
        }
        if *offset < 0 {
            return Err(fs::path_error("read", &self.path, FsError::Invalid));
        }
        let n = b.len().min(self.map_file_info.f.data.len() - *offset as usize);
        b[..n].copy_from_slice(&self.map_file_info.f.data[*offset as usize..*offset as usize + n]);
        *offset += n as i64;
        Ok(n)
    }

    fn as_seeker(&self) -> Option<&dyn Seeker> {
        Some(self)
    }

    fn as_reader_at(&self) -> Option<&dyn ReaderAt> {
        Some(self)
    }
}

impl Seeker for OpenMapFile {
    fn seek(&self, offset: i64, whence: SeekWhence) -> Result<i64, FsError> {
        let mut current = self.offset.lock().unwrap();
        let len = self.map_file_info.f.data.len() as i64;
        let offset = match whence {
            SeekWhence::Start => offset,
            SeekWhence::Current => offset + *current,
            SeekWhence::End => offset + len,
        };
        if offset < 0 || offset > len {
            return Err(fs::path_error("seek", &self.path, FsError::Invalid));
        }
        *current = offset;
        Ok(offset)
    }
}

impl ReaderAt for OpenMapFile {
    fn read_at(&self, b: &mut [u8], offset: i64) -> Result<usize, FsError> {
        if offset < 0 || offset > self.map_file_info.f.data.len() as i64 {
            return Err(fs::path_error("read", &self.path, FsError::Invalid));
        }
        let n = b
            .len()
            .min(self.map_file_info.f.data.len() - offset as usize);
        b[..n].copy_from_slice(&self.map_file_info.f.data[offset as usize..offset as usize + n]);
        if n < b.len() {
            return Err(FsError::Eof);
        }
        Ok(n)
    }
}

/// A MapDir is a directory fs.File (so also an fs.ReadDirFile) open for reading.
struct MapDir {
    path: String,
    map_file_info: MapFileInfo,
    entry: Vec<MapFileInfo>,
    offset: Mutex<usize>,
}

impl File for MapDir {
    fn stat(&self) -> Result<Arc<dyn FileInfo>, FsError> {
        Ok(Arc::new(self.map_file_info.clone()))
    }

    fn close(&self) -> Result<(), FsError> {
        Ok(())
    }

    fn read(&self, _b: &mut [u8]) -> Result<usize, FsError> {
        Err(fs::path_error("read", &self.path, FsError::Invalid))
    }

    fn as_read_dir_file(&self) -> Option<&dyn ReadDirFile> {
        Some(self)
    }
}

impl ReadDirFile for MapDir {
    fn read_dir(&self, count: i32) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        let mut offset = self.offset.lock().unwrap();
        let mut n = self.entry.len() - *offset;
        if n == 0 && count > 0 {
            return Err(FsError::Eof);
        }
        if count > 0 && n > count as usize {
            n = count as usize;
        }
        let list: Vec<Arc<dyn DirEntry>> = self.entry[*offset..*offset + n]
            .iter()
            .map(|e| Arc::new(e.clone()) as Arc<dyn DirEntry>)
            .collect();
        *offset += n;
        Ok(list)
    }
}

// ---------------------------------------------------------------------------
// testing/fstest testfs.go — TestFS
// ---------------------------------------------------------------------------

/// test_fs is fstest.TestFS: it walks the entire tree of files in fsys,
/// opening and checking that each file behaves correctly.
/// Symbolic links are not followed, but their Lstat values are checked
/// if the file system implements [ReadLinkFs].
/// It also checks that the file system contains at least the expected files.
/// As a special case, if no expected files are listed, fsys must be empty.
/// Otherwise, fsys must contain at least the listed files; it can also contain others.
pub fn test_fs(fsys: &Arc<dyn Fs>, expected: &[&str]) -> Result<(), FsError> {
    test_fs_impl(fsys, expected)?;

    for name in expected {
        if let Some(i) = name.find('/') {
            let (dir, dir_slash) = (&name[..i], &name[..i + 1]);
            let mut sub_expected: Vec<&str> = Vec::new();
            for name in expected {
                if let Some(rest) = name.strip_prefix(dir_slash) {
                    sub_expected.push(rest);
                }
            }
            let sub = fs::sub(fsys, dir)?;
            let sub_expected_strings: Vec<String> =
                sub_expected.iter().map(|s| s.to_string()).collect();
            if let Err(err) = test_fs_impl(
                &sub,
                &sub_expected_strings
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            ) {
                return Err(FsError::Message(format!(
                    "testing fs.Sub(fsys, {}): {}",
                    dir, err
                )));
            }
            break; // one sub-test is enough
        }
    }
    Ok(())
}

fn test_fs_impl(fsys: &Arc<dyn Fs>, expected: &[&str]) -> Result<(), FsError> {
    let mut t = FsTester::new(fsys);
    t.check_dir(".");
    t.check_open(".");
    let mut found: HashSet<String> = HashSet::new();
    for dir in &t.dirs {
        found.insert(dir.clone());
    }
    for file in &t.files {
        found.insert(file.clone());
    }
    found.remove(".");
    if expected.is_empty() && !found.is_empty() {
        let mut list: Vec<String> = found.iter().cloned().collect();
        list.sort();
        if list.len() > 15 {
            list.truncate(10);
            list.push("...".to_string());
        }
        t.errorf(format!(
            "expected empty file system but found files:\n{}",
            list.join("\n")
        ));
    }
    for name in expected {
        if !found.contains(*name) {
            t.errorf(format!("expected but not found: {}", name));
        }
    }
    if t.errors.is_empty() {
        return Ok(());
    }
    Err(FsError::Message(format!(
        "TestFS found errors:\n{}",
        t.errors.join("\n")
    )))
}

/// FsTester is fstest.fsTester: it accumulates errors rather than failing
/// immediately, matching Go's t.errorf.
struct FsTester<'a> {
    fsys: &'a Arc<dyn Fs>,
    errors: Vec<String>,
    dirs: Vec<String>,
    files: Vec<String>,
}

impl<'a> FsTester<'a> {
    fn new(fsys: &'a Arc<dyn Fs>) -> FsTester<'a> {
        FsTester {
            fsys,
            errors: Vec::new(),
            dirs: Vec::new(),
            files: Vec::new(),
        }
    }

    fn errorf(&mut self, msg: String) {
        self.errors.push(msg);
    }

    fn open_dir(&mut self, dir: &str) -> Option<Box<dyn File>> {
        let f = match self.fsys.open(dir) {
            Err(err) => {
                self.errorf(format!("{}: Open: {}", dir, err));
                return None;
            }
            Ok(f) => f,
        };
        if f.as_read_dir_file().is_none() {
            let _ = f.close();
            self.errorf(format!(
                "{}: Open returned File that is not a fs.ReadDirFile",
                dir
            ));
            return None;
        }
        Some(f)
    }

    /// check_dir checks the directory dir, which is expected to exist
    /// (it is either the root or was found in a directory listing with
    /// is_dir true).
    fn check_dir(&mut self, dir: &str) {
        // Read entire directory.
        self.dirs.push(dir.to_string());
        let Some(d) = self.open_dir(dir) else {
            return;
        };
        let rd = d.as_read_dir_file().unwrap();
        let list = match rd.read_dir(-1) {
            Err(err) => {
                let _ = d.close();
                self.errorf(format!("{}: ReadDir(-1): {}", dir, err));
                return;
            }
            Ok(list) => list,
        };

        // Check all children.
        let prefix = if dir == "." {
            String::new()
        } else {
            format!("{}/", dir)
        };
        for info in &list {
            let name = info.name();
            if name == "." || name == ".." || name.is_empty() {
                self.errorf(format!(
                    "{}: ReadDir: child has invalid name: {}",
                    dir,
                    fs::go_quote(&name)
                ));
                continue;
            } else if name.contains('/') {
                self.errorf(format!(
                    "{}: ReadDir: child name contains slash: {}",
                    dir,
                    fs::go_quote(&name)
                ));
                continue;
            } else if name.contains('\\') {
                self.errorf(format!(
                    "{}: ReadDir: child name contains backslash: {}",
                    dir,
                    fs::go_quote(&name)
                ));
                continue;
            }
            let path = format!("{}{}", prefix, name);
            self.check_stat(&path, &**info);
            self.check_open(&path);
            match info.type_() {
                t if t == MODE_DIR => self.check_dir(&path),
                t if t == MODE_SYMLINK => {
                    // No further processing.
                    // Avoid following symlinks to avoid potentially unbounded recursion.
                    self.files.push(path);
                }
                _ => self.check_file(&path),
            }
        }

        // Check ReadDir(-1) at EOF.
        match rd.read_dir(-1) {
            Ok(list2) if list2.is_empty() => {}
            result => {
                let _ = d.close();
                let (n, e) = match result {
                    Ok(l) => (l.len(), "nil".to_string()),
                    Err(e) => (0, e.to_string()),
                };
                self.errorf(format!(
                    "{}: ReadDir(-1) at EOF = {} entries, {}, wanted 0 entries, nil",
                    dir, n, e
                ));
                return;
            }
        }

        // Check ReadDir(1) at EOF (different results).
        match rd.read_dir(1) {
            Err(e) if e.is_eof() => {}
            result => {
                let _ = d.close();
                let (n, e) = match result {
                    Ok(l) => (l.len(), "nil".to_string()),
                    Err(e) => (0, e.to_string()),
                };
                self.errorf(format!(
                    "{}: ReadDir(1) at EOF = {} entries, {}, wanted 0 entries, EOF",
                    dir, n, e
                ));
                return;
            }
        }

        // Check that close does not report an error.
        if let Err(err) = d.close() {
            self.errorf(format!("{}: Close: {}", dir, err));
        }

        // Check that closing twice doesn't crash.
        // The return value doesn't matter.
        let _ = d.close();

        // Reopen directory, read a second time, make sure contents match.
        let Some(d2) = self.open_dir(dir) else {
            return;
        };
        let list2 = match d2.as_read_dir_file().unwrap().read_dir(-1) {
            Err(err) => {
                self.errorf(format!("{}: second Open+ReadDir(-1): {}", dir, err));
                return;
            }
            Ok(list2) => list2,
        };
        self.check_dir_list(
            dir,
            "first Open+ReadDir(-1) vs second Open+ReadDir(-1)",
            &list,
            &list2,
        );
        let _ = d2.close();

        // Reopen directory, read a third time in pieces, make sure contents match.
        let Some(d3) = self.open_dir(dir) else {
            return;
        };
        let rd3 = d3.as_read_dir_file().unwrap();
        let mut list2: Vec<Arc<dyn DirEntry>> = Vec::new();
        loop {
            let n: i32 = if list2.is_empty() { 1 } else { 2 };
            match rd3.read_dir(n) {
                Ok(frag) => {
                    if frag.len() > n as usize {
                        self.errorf(format!(
                            "{}: third Open: ReadDir({}) after {}: {} entries (too many)",
                            dir,
                            n,
                            list2.len(),
                            frag.len()
                        ));
                        return;
                    }
                    if frag.is_empty() {
                        self.errorf(format!(
                            "{}: third Open: ReadDir({}) after {}: 0 entries but nil error",
                            dir,
                            n,
                            list2.len()
                        ));
                        return;
                    }
                    list2.extend(frag);
                }
                Err(e) if e.is_eof() => break,
                Err(e) => {
                    self.errorf(format!(
                        "{}: third Open: ReadDir({}) after {}: {}",
                        dir,
                        n,
                        list2.len(),
                        e
                    ));
                    return;
                }
            }
        }
        let _ = d3.close();
        self.check_dir_list(
            dir,
            "first Open+ReadDir(-1) vs third Open+ReadDir(1,2) loop",
            &list,
            &list2,
        );

        // If fsys has ReadDir, check that it matches and is sorted.
        if let Some(rfs) = self.fsys.as_read_dir_fs() {
            match rfs.read_dir(dir) {
                Err(err) => {
                    self.errorf(format!("{}: fsys.ReadDir: {}", dir, err));
                    return;
                }
                Ok(list2) => {
                    self.check_dir_list(
                        dir,
                        "first Open+ReadDir(-1) vs fsys.ReadDir",
                        &list,
                        &list2,
                    );
                    for i in 0..list2.len().saturating_sub(1) {
                        if list2[i].name() >= list2[i + 1].name() {
                            self.errorf(format!(
                                "{}: fsys.ReadDir: list not sorted: {} before {}",
                                dir,
                                list2[i].name(),
                                list2[i + 1].name()
                            ));
                        }
                    }
                }
            }
        }

        // Check fs.ReadDir as well.
        match fs::read_dir(&**self.fsys, dir) {
            Err(err) => {
                self.errorf(format!("{}: fs.ReadDir: {}", dir, err));
                return;
            }
            Ok(list2) => {
                self.check_dir_list(
                    dir,
                    "first Open+ReadDir(-1) vs fs.ReadDir",
                    &list,
                    &list2,
                );
                for i in 0..list2.len().saturating_sub(1) {
                    if list2[i].name() >= list2[i + 1].name() {
                        self.errorf(format!(
                            "{}: fs.ReadDir: list not sorted: {} before {}",
                            dir,
                            list2[i].name(),
                            list2[i + 1].name()
                        ));
                    }
                }
            }
        }

        // Go passes the fs.ReadDir list here; checkGlob no-ops without GlobFs.
        self.check_glob(dir, &list);
    }

    /// checkGlob checks that various glob patterns work if the file system
    /// implements GlobFS.
    fn check_glob(&mut self, dir: &str, list: &[Arc<dyn DirEntry>]) {
        let _ = (dir, list);
        if self.fsys.as_glob_fs().is_none() {
            return;
        }
        // PORT: no Fs implementation in this crate implements GlobFs, so the
        // glob-pattern checks are unreachable and omitted.
    }

    /// checkStat checks that a direct stat of path matches entry,
    /// which was found in the parent's directory listing.
    fn check_stat(&mut self, path: &str, entry: &dyn DirEntry) {
        let file = match self.fsys.open(path) {
            Err(err) => {
                self.errorf(format!("{}: Open: {}", path, err));
                return;
            }
            Ok(file) => file,
        };
        let info_result = file.stat();
        let _ = file.close();
        let info = match info_result {
            Err(err) => {
                self.errorf(format!("{}: Stat: {}", path, err));
                return;
            }
            Ok(info) => info,
        };
        let fentry = format_entry(entry);
        let fientry = format_info_entry(&*info);
        // Note: mismatch here is OK for symlink, because Open dereferences symlink.
        if fentry != fientry && entry.type_() & MODE_SYMLINK == FileMode(0) {
            self.errorf(format!(
                "{}: mismatch:\n\tentry = {}\n\tfile.Stat() = {}",
                path, fentry, fientry
            ));
        }

        let einfo = match entry.info() {
            Err(err) => {
                self.errorf(format!("{}: entry.Info: {}", path, err));
                return;
            }
            Ok(einfo) => einfo,
        };
        let finfo = format_info(&*info);
        if entry.type_() & MODE_SYMLINK != FileMode(0) {
            // For symlink, just check that entry.Info matches entry on common fields.
            // Open dereferences symlink, so info itself may differ.
            let feentry = format_info_entry(&*einfo);
            if fentry != feentry {
                self.errorf(format!(
                    "{}: mismatch\n\tentry = {}\n\tentry.Info() = {}\n",
                    path, fentry, feentry
                ));
            }
        } else {
            let feinfo = format_info(&*einfo);
            if feinfo != finfo {
                self.errorf(format!(
                    "{}: mismatch:\n\tentry.Info() = {}\n\tfile.Stat() = {}\n",
                    path, feinfo, finfo
                ));
            }
        }

        // Stat should be the same as Open+Stat, even for symlinks.
        match fs::stat(&**self.fsys, path) {
            Err(err) => {
                self.errorf(format!("{}: fs.Stat: {}", path, err));
                return;
            }
            Ok(info2) => {
                if format_info(&*info2) != finfo {
                    self.errorf(format!(
                        "{}: fs.Stat(...) = {}\n\twant {}",
                        path,
                        format_info(&*info2),
                        finfo
                    ));
                }
            }
        }

        if let Some(sfs) = self.fsys.as_stat_fs() {
            match sfs.stat(path) {
                Err(err) => {
                    self.errorf(format!("{}: fsys.Stat: {}", path, err));
                    return;
                }
                Ok(info2) => {
                    if format_info(&*info2) != finfo {
                        self.errorf(format!(
                            "{}: fsys.Stat(...) = {}\n\twant {}",
                            path,
                            format_info(&*info2),
                            finfo
                        ));
                    }
                }
            }
        }

        if let Some(lsys) = self.fsys.as_read_link_fs() {
            match lsys.lstat(path) {
                Err(err) => {
                    self.errorf(format!("{}: fsys.Lstat: {}", path, err));
                    return;
                }
                Ok(info2) => {
                    if fentry != format_info_entry(&*info2) {
                        self.errorf(format!(
                            "{}: mismatch:\n\tentry = {}\n\tfsys.Lstat(...) = {}",
                            path,
                            fentry,
                            format_info_entry(&*info2)
                        ));
                    }
                    let feinfo = format_info(&*einfo);
                    let finfo2 = format_info(&*info2);
                    if feinfo != finfo2 {
                        self.errorf(format!(
                            "{}: mismatch:\n\tentry.Info() = {}\n\tfsys.Lstat(...) = {}\n",
                            path, feinfo, finfo2
                        ));
                    }
                }
            }
        }
    }

    /// checkDirList checks that two directory lists contain the same files
    /// and file info. The order of the lists need not match.
    fn check_dir_list(
        &mut self,
        dir: &str,
        desc: &str,
        list1: &[Arc<dyn DirEntry>],
        list2: &[Arc<dyn DirEntry>],
    ) {
        let mut old: FxHashMap<String, Arc<dyn DirEntry>> = FxHashMap::default();
        for entry1 in list1 {
            self.check_entry_mode(dir, &**entry1);
            old.insert(entry1.name(), entry1.clone());
        }

        let mut diffs: Vec<String> = Vec::new();
        for entry2 in list2 {
            match old.get(&entry2.name()) {
                None => {
                    self.check_entry_mode(dir, &**entry2);
                    diffs.push(format!("+ {}", format_entry(&**entry2)));
                }
                Some(entry1) => {
                    if format_entry(&**entry1) != format_entry(&**entry2) {
                        diffs.push(format!("- {}", format_entry(&**entry1)));
                        diffs.push(format!("+ {}", format_entry(&**entry2)));
                    }
                    old.remove(&entry2.name());
                }
            }
        }
        for (_, entry1) in old {
            diffs.push(format!("- {}", format_entry(&*entry1)));
        }

        if diffs.is_empty() {
            return;
        }

        // Go: slices.SortFunc comparing fa[1]+" "+fb[0] vs fb[1]+" "+fa[0]
        // (sort by name, then +/-).
        diffs.sort_by(|a, b| {
            let fa: Vec<&str> = a.split_whitespace().collect();
            let fb: Vec<&str> = b.split_whitespace().collect();
            let ka = format!(
                "{} {}",
                fa.get(1).copied().unwrap_or(""),
                fb.first().copied().unwrap_or("")
            );
            let kb = format!(
                "{} {}",
                fb.get(1).copied().unwrap_or(""),
                fa.first().copied().unwrap_or("")
            );
            ka.cmp(&kb)
        });

        self.errorf(format!("{}: diff {}:\n\t{}", dir, desc, diffs.join("\n\t")));
    }

    fn check_entry_mode(&mut self, dir: &str, entry: &dyn DirEntry) {
        if entry.is_dir() != (entry.type_() & MODE_DIR != FileMode(0)) {
            if entry.is_dir() {
                self.errorf(format!(
                    "{}: ReadDir returned {} with IsDir() = true, Type() & ModeDir = 0",
                    dir,
                    entry.name()
                ));
            } else {
                self.errorf(format!(
                    "{}: ReadDir returned {} with IsDir() = false, Type() & ModeDir = ModeDir",
                    dir,
                    entry.name()
                ));
            }
        }
    }

    /// checkFile checks that basic file reading works correctly.
    fn check_file(&mut self, file: &str) {
        self.files.push(file.to_string());

        // Read entire file.
        let f = match self.fsys.open(file) {
            Err(err) => {
                self.errorf(format!("{}: Open: {}", file, err));
                return;
            }
            Ok(f) => f,
        };

        let data = match fs::read_all(&*f) {
            Err(err) => {
                let _ = f.close();
                self.errorf(format!("{}: Open+ReadAll: {}", file, err));
                return;
            }
            Ok(data) => data,
        };

        if let Err(err) = f.close() {
            self.errorf(format!("{}: Close: {}", file, err));
        }

        // Check that closing twice doesn't crash.
        // The return value doesn't matter.
        let _ = f.close();

        // Check that ReadFile works if present.
        if let Some(rfs) = self.fsys.as_read_file_fs() {
            let mut data2 = match rfs.read_file(file) {
                Err(err) => {
                    self.errorf(format!("{}: fsys.ReadFile: {}", file, err));
                    return;
                }
                Ok(data2) => data2,
            };
            self.check_file_read(file, "ReadAll vs fsys.ReadFile", &data, &data2);

            // Modify the data and check it again. Modifying the
            // returned byte slice should not affect the next call.
            for b in data2.iter_mut() {
                *b = b.wrapping_add(1);
            }
            match rfs.read_file(file) {
                Err(err) => {
                    self.errorf(format!("{}: second call to fsys.ReadFile: {}", file, err));
                    return;
                }
                Ok(data2) => {
                    self.check_file_read(
                        file,
                        "Readall vs second fsys.ReadFile",
                        &data,
                        &data2,
                    );
                }
            }

            self.check_bad_path(file, "ReadFile", &mut |name| {
                rfs.read_file(name).map(|_| ())
            });
        }

        // Check that fs.ReadFile works with t.fsys.
        match fs::read_file(&**self.fsys, file) {
            Err(err) => {
                self.errorf(format!("{}: fs.ReadFile: {}", file, err));
                return;
            }
            Ok(data2) => {
                self.check_file_read(file, "ReadAll vs fs.ReadFile", &data, &data2);
            }
        }

        // Use iotest.TestReader to check small reads, Seek, ReadAt.
        let f = match self.fsys.open(file) {
            Err(err) => {
                self.errorf(format!("{}: second Open: {}", file, err));
                return;
            }
            Ok(f) => f,
        };
        let result = iotest_test_reader(&*f, &data);
        let _ = f.close();
        if let Err(err) = result {
            self.errorf(format!(
                "{}: failed TestReader:\n\t{}",
                file,
                err.replace('\n', "\n\t")
            ));
        }
    }

    fn check_file_read(&mut self, file: &str, desc: &str, data1: &[u8], data2: &[u8]) {
        if data1 != data2 {
            self.errorf(format!(
                "{}: {}: different data returned\n\t{:?}\n\t{:?}",
                file, desc, data1, data2
            ));
        }
    }

    /// checkOpen validates file opening behavior by attempting to open and
    /// then close the given file path.
    fn check_open(&mut self, file: &str) {
        let fsys = self.fsys;
        self.check_bad_path(file, "Open", &mut |file| match fsys.open(file) {
            Ok(f) => {
                let _ = f.close();
                Ok(())
            }
            Err(err) => Err(err),
        });
    }

    /// checkBadPath checks that various invalid forms of file's name cannot
    /// be opened using open.
    fn check_bad_path(
        &mut self,
        file: &str,
        desc: &str,
        open: &mut dyn FnMut(&str) -> Result<(), FsError>,
    ) {
        let mut bad = vec![format!("/{}", file), format!("{}/.", file)];
        if file == "." {
            bad.push("/".to_string());
        }
        if let Some(i) = file.find('/') {
            bad.push(format!("{}//{}", &file[..i], &file[i + 1..]));
            bad.push(format!("{}/./{}", &file[..i], &file[i + 1..]));
            bad.push(format!("{}\\{}", &file[..i], &file[i + 1..]));
            bad.push(format!("{}/../{}", &file[..i], file));
        }
        if let Some(i) = file.rfind('/') {
            bad.push(format!("{}//{}", &file[..i], &file[i + 1..]));
            bad.push(format!("{}/./{}", &file[..i], &file[i + 1..]));
            bad.push(format!("{}\\{}", &file[..i], &file[i + 1..]));
            bad.push(format!("{}/../{}", file, &file[i + 1..]));
        }

        for b in &bad {
            if open(b).is_ok() {
                self.errorf(format!("{}: {}({}) succeeded, want error", file, desc, b));
            }
        }
    }
}

/// formatEntry formats an fs.DirEntry into a string for error messages and comparison.
fn format_entry(entry: &dyn DirEntry) -> String {
    format!("{} IsDir={} Type={}", entry.name(), entry.is_dir(), entry.type_())
}

/// formatInfoEntry formats an fs.FileInfo into a string like the result of formatEntry, for error messages and comparison.
fn format_info_entry(info: &dyn FileInfo) -> String {
    format!(
        "{} IsDir={} Type={}",
        info.name(),
        info.is_dir(),
        info.mode().type_()
    )
}

/// formatInfo formats an fs.FileInfo into a string for error messages and comparison.
fn format_info(info: &dyn FileInfo) -> String {
    format!("{:?}", info)
}

// ---------------------------------------------------------------------------
// testing/iotest TestReader
// ---------------------------------------------------------------------------

/// smallByteReader is iotest.smallByteReader.
struct SmallByteReader<'a> {
    r: &'a dyn File,
    off: usize,
    n: usize,
}

impl SmallByteReader<'_> {
    fn read(&mut self, p: &mut [u8]) -> Result<usize, FsError> {
        if p.is_empty() {
            return Ok(0);
        }
        self.n = self.n % 3 + 1;
        let n = self.n.min(p.len());
        match self.r.read(&mut p[..n]) {
            Ok(n) => {
                self.off += n;
                Ok(n)
            }
            Err(e) if e.is_eof() => Err(e),
            Err(e) => Err(FsError::Message(format!(
                "Read({} bytes at offset {}): {}",
                n, self.off, e
            ))),
        }
    }
}

fn small_read_all(r: &dyn File) -> Result<Vec<u8>, FsError> {
    let mut sr = SmallByteReader { r, off: 0, n: 0 };
    let mut data = Vec::new();
    let mut buf = [0u8; 512];
    loop {
        match sr.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => data.extend_from_slice(&buf[..n]),
            Err(e) if e.is_eof() => break,
            Err(e) => return Err(e),
        }
    }
    Ok(data)
}

/// test_reader is iotest.TestReader: it tests that reading from r returns
/// the expected file content. It does reads of different sizes, until EOF.
/// If r implements ReaderAt or Seeker, it also checks that those operations
/// behave as they should.
///
/// PORT: io.Reader can report (n, err) pairs; our File::read returns only
/// Result<usize>, so checks on the n of a failing read are elided.
fn iotest_test_reader(r: &dyn File, content: &[u8]) -> Result<(), String> {
    if !content.is_empty() {
        match r.read(&mut []) {
            Ok(0) => {}
            Ok(n) => return Err(format!("Read(0) = {}, nil, want 0, nil", n)),
            Err(e) => return Err(format!("Read(0) = 0, {}, want 0, nil", e)),
        }
    }

    let data = match small_read_all(r) {
        Err(e) => return Err(e.to_string()),
        Ok(data) => data,
    };
    if data != content {
        return Err(format!(
            "ReadAll(small amounts) = {:?}\n\twant {:?}",
            data, content
        ));
    }
    let mut buf10 = [0u8; 10];
    match r.read(&mut buf10) {
        Err(e) if e.is_eof() => {}
        Ok(n) => return Err(format!("Read(10) at EOF = {}, nil, want 0, EOF", n)),
        Err(e) => return Err(format!("Read(10) at EOF = 0, {}, want 0, EOF", e)),
    }

    if let Some(seeker) = r.as_seeker() {
        let len = content.len() as i64;
        // Seek(0, Current) should report the current file position (EOF).
        match seeker.seek(0, SeekWhence::Current) {
            Ok(off) if off == len => {}
            Ok(off) => {
                return Err(format!(
                    "Seek(0, 1) from EOF = {}, nil, want {}, nil",
                    off, len
                ))
            }
            Err(e) => {
                return Err(format!("Seek(0, 1) from EOF = 0, {}, want {}, nil", e, len))
            }
        }

        // Seek backward partway through file, in two steps.
        // If middle == 0, len(content) == 0, can't use the -1 and +1 seeks.
        let middle = len - len / 3;
        if middle > 0 {
            match seeker.seek(-1, SeekWhence::Current) {
                Ok(off) if off == len - 1 => {}
                Ok(off) => {
                    return Err(format!(
                        "Seek(-1, 1) from EOF = {}, nil, want {}, nil",
                        off,
                        len - 1
                    ))
                }
                Err(e) => {
                    return Err(format!(
                        "Seek(-1, 1) from EOF = 0, {}, want {}, nil",
                        e,
                        len - 1
                    ))
                }
            }
            match seeker.seek(-(len / 3), SeekWhence::Current) {
                Ok(off) if off == middle - 1 => {}
                Ok(off) => {
                    return Err(format!(
                        "Seek({}, 1) from {} = {}, nil, want {}, nil",
                        -(len / 3),
                        len - 1,
                        off,
                        middle - 1
                    ))
                }
                Err(e) => {
                    return Err(format!(
                        "Seek({}, 1) from {} = 0, {}, want {}, nil",
                        -(len / 3),
                        len - 1,
                        e,
                        middle - 1
                    ))
                }
            }
            match seeker.seek(1, SeekWhence::Current) {
                Ok(off) if off == middle => {}
                Ok(off) => {
                    return Err(format!(
                        "Seek(+1, 1) from {} = {}, nil, want {}, nil",
                        middle - 1,
                        off,
                        middle
                    ))
                }
                Err(e) => {
                    return Err(format!(
                        "Seek(+1, 1) from {} = 0, {}, want {}, nil",
                        middle - 1,
                        e,
                        middle
                    ))
                }
            }
        }

        // Seek(0, Current) should report the current file position (middle).
        match seeker.seek(0, SeekWhence::Current) {
            Ok(off) if off == middle => {}
            Ok(off) => {
                return Err(format!(
                    "Seek(0, 1) from {} = {}, nil, want {}, nil",
                    middle, off, middle
                ))
            }
            Err(e) => {
                return Err(format!(
                    "Seek(0, 1) from {} = 0, {}, want {}, nil",
                    middle, e, middle
                ))
            }
        }

        // Reading forward should return the last part of the file.
        let data = match small_read_all(r) {
            Err(e) => return Err(format!("ReadAll from offset {}: {}", middle, e)),
            Ok(data) => data,
        };
        if data != content[middle as usize..] {
            return Err(format!(
                "ReadAll from offset {} = {:?}\n\twant {:?}",
                middle,
                data,
                &content[middle as usize..]
            ));
        }

        // Seek relative to end of file, but start elsewhere.
        match seeker.seek(middle / 2, SeekWhence::Start) {
            Ok(off) if off == middle / 2 => {}
            Ok(off) => {
                return Err(format!(
                    "Seek({}, 0) from EOF = {}, nil, want {}, nil",
                    middle / 2,
                    off,
                    middle / 2
                ))
            }
            Err(e) => {
                return Err(format!(
                    "Seek({}, 0) from EOF = 0, {}, want {}, nil",
                    middle / 2,
                    e,
                    middle / 2
                ))
            }
        }
        match seeker.seek(-(len / 3), SeekWhence::End) {
            Ok(off) if off == middle => {}
            Ok(off) => {
                return Err(format!(
                    "Seek({}, 2) from {} = {}, nil, want {}, nil",
                    -(len / 3),
                    middle / 2,
                    off,
                    middle
                ))
            }
            Err(e) => {
                return Err(format!(
                    "Seek({}, 2) from {} = 0, {}, want {}, nil",
                    -(len / 3),
                    middle / 2,
                    e,
                    middle
                ))
            }
        }

        // Reading forward should return the last part of the file (again).
        let data = match small_read_all(r) {
            Err(e) => return Err(format!("ReadAll from offset {}: {}", middle, e)),
            Ok(data) => data,
        };
        if data != content[middle as usize..] {
            return Err(format!(
                "ReadAll from offset {} = {:?}\n\twant {:?}",
                middle,
                data,
                &content[middle as usize..]
            ));
        }

        // Absolute seek & read forward.
        match seeker.seek(middle / 2, SeekWhence::Start) {
            Ok(off) if off == middle / 2 => {}
            Ok(off) => {
                return Err(format!(
                    "Seek({}, 0) from EOF = {}, nil, want {}, nil",
                    middle / 2,
                    off,
                    middle / 2
                ))
            }
            Err(e) => {
                return Err(format!(
                    "Seek({}, 0) from EOF = 0, {}, want {}, nil",
                    middle / 2,
                    e,
                    middle / 2
                ))
            }
        }
        let data = match fs::read_all(r) {
            Err(e) => return Err(format!("ReadAll from offset {}: {}", middle / 2, e)),
            Ok(data) => data,
        };
        if data != content[(middle / 2) as usize..] {
            return Err(format!(
                "ReadAll from offset {} = {:?}\n\twant {:?}",
                middle / 2,
                data,
                &content[(middle / 2) as usize..]
            ));
        }
    }

    if let Some(ra) = r.as_reader_at() {
        let mut data = vec![0xfeu8; content.len()];
        match ra.read_at(&mut data, 0) {
            Ok(n) if n == data.len() => {}
            Ok(n) => {
                return Err(format!(
                    "ReadAt({}, 0) = {}, nil, want {}, nil or EOF",
                    data.len(),
                    n,
                    data.len()
                ))
            }
            // At end of input, (len(data), EOF) is also acceptable.
            Err(e) if e.is_eof() => {}
            Err(e) => {
                return Err(format!(
                    "ReadAt({}, 0) = ?, {}, want {}, nil or EOF",
                    data.len(),
                    e,
                    data.len()
                ))
            }
        }
        if data != content {
            return Err(format!(
                "ReadAt({}, 0) = {:?}\n\twant {:?}",
                data.len(),
                data,
                content
            ));
        }

        let mut b1 = [0xfeu8; 1];
        match ra.read_at(&mut b1, content.len() as i64) {
            Err(e) if e.is_eof() => {}
            Ok(n) => {
                return Err(format!(
                    "ReadAt(1, {}) = {}, nil, want 0, EOF",
                    data.len(),
                    n
                ))
            }
            Err(e) => {
                return Err(format!(
                    "ReadAt(1, {}) = 0, {}, want 0, EOF",
                    data.len(),
                    e
                ))
            }
        }

        for b in data.iter_mut() {
            *b = 0xfe;
        }
        let mut over = vec![0xfeu8; content.len() + 1];
        match ra.read_at(&mut over, 0) {
            // PORT: Go expects (len(data), io.EOF); our read_at reports the
            // EOF without the count, so accept Err(EOF) and verify the bytes.
            Err(e) if e.is_eof() => {}
            Ok(n) => {
                return Err(format!(
                    "ReadAt({}, 0) = {}, nil, want {}, EOF",
                    over.len(),
                    n,
                    data.len()
                ))
            }
            Err(e) => {
                return Err(format!(
                    "ReadAt({}, 0) = ?, {}, want {}, EOF",
                    over.len(),
                    e,
                    data.len()
                ))
            }
        }
        if over[..data.len()] != data[..] {
            return Err(format!(
                "ReadAt({}, 0) = {:?}\n\twant {:?}",
                over.len(),
                &over[..data.len()],
                data
            ));
        }

        for b in data.iter_mut() {
            *b = 0xfe;
        }
        for i in 0..data.len() {
            let mut b1 = [0xfeu8; 1];
            match ra.read_at(&mut b1, i as i64) {
                Ok(1) => {}
                Ok(n) => {
                    return Err(format!("ReadAt(1, {}) = {}, nil, want 1, nil", i, n))
                }
                Err(e) if e.is_eof() && i == data.len() - 1 => {}
                Err(e) => {
                    let want = if i == data.len() - 1 { "nil or EOF" } else { "nil" };
                    return Err(format!("ReadAt(1, {}) = ?, {}, want 1, {}", i, e, want));
                }
            }
            if b1[0] != content[i] {
                return Err(format!("ReadAt(1, {}) bad byte", i));
            }
        }
    }
    Ok(())
}

// PORT: Go routes these through fsOnly{fsys}, an fs.FS wrapper that hides the
// optional interfaces so the helpers fall back to Open. We call the open-based
// fallbacks directly — same behavior without a wrapper type (a &MapFs wrapper
// could not satisfy the `Fs: 'static` bound anyway).
impl StatFs for MapFs {
    fn stat(&self, name: &str) -> Result<Arc<dyn FileInfo>, FsError> {
        let file = self.open(name)?;
        let result = file.stat();
        let _ = file.close();
        result
    }
}

impl ReadDirFs for MapFs {
    fn read_dir(&self, name: &str) -> Result<Vec<Arc<dyn DirEntry>>, FsError> {
        fs::read_dir_via_open(self, name)
    }
}

impl ReadFileFs for MapFs {
    fn read_file(&self, name: &str) -> Result<Vec<u8>, FsError> {
        fs::read_file_via_open(self, name)
    }
}
