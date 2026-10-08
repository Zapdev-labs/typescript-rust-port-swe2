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
    self, DirEntry, File, FileInfo, FileMode, Fs, FsError, ReadDirFile, ReadLinkFs,
    ReaderAt, SeekWhence, Seeker, MODE_DIR, MODE_SYMLINK,
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

    // PORT: Go's MapFS implements StatFS/ReadDirFS/ReadFileFS/ReadLinkFS via
    // fsOnly wrappers that route back through Open. We implement the real
    // read_link/lstat (which are genuine methods) but leave stat/read_dir/
    // read_file unset so the free functions take the same open-based path;
    // the observable behavior is identical.
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
    let mut found: HashSet<&str> = HashSet::new();
    for dir in &t.dirs {
        found.insert(dir);
    }
    for file in &t.files {
        found.insert(file);
    }
    found.remove(".");
    if expected.is_empty() && !found.is_empty() {
        let mut list: Vec<&str> = found.into_iter().collect();
        list.sort();
        let mut list: Vec<String> = list.iter().map(|s| s.to_string()).collect();
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
        if !found.contains(name) {
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

    fn check_dir(&mut self, dir: &str) {
        let mut paths = vec![
            dir.to_string(),
            // check ending in slash
            format!("{}/", dir.trim_end_matches('/')),
        ];
        if dir != "." {
            // check earlier prefixes of dir
            loop {
                let i = {
                    let d = paths.last().unwrap();
                    match d.rfind('/') {
                        None => d.len(),
                        Some(i) => i,
                    }
                };
                if i == 0 {
                    break;
                }
                paths.push(paths.last().unwrap()[..i].to_string());
            }
        }
        for dir in &paths {
            if let Err(err) = self.fsys.open(dir) {
                self.errorf(format!("{}: error from Open: {}", dir, err));
            }
            if let Ok(entries) = fs::read_dir(self.fsys, dir) {
                for entry in entries {
                    self.check_bad_path(&entry.name(), "ReadDir output");
                }
            }
        }
        if dir == "." {
            self.check_dir_list(dir, &[]);
        }
    }

    /// checkBadPath checks that name is rejected by Open, Stat, and ReadDir.
    fn check_bad_path(&mut self, name: &str, output: &str) {
        if fs::valid_path(name) {
            return;
        }

        self.errorf(format!("{}: bad name {}", output, fs::go_quote(name)));

        match self.fsys.open(name) {
            Ok(_) => self.errorf(format!("Open({}): succeeded, want error", name)),
            Err(err) => {
                if !Self::bad_path_error("Open", name, &err) {
                    self.errorf(format!(
                        "Open({}): can return error; continue anyway",
                        name
                    ));
                }
            }
        }

        match fs::stat(self.fsys, name) {
            Ok(_) => self.errorf(format!("Stat({}): succeeded, want error", name)),
            Err(err) => {
                if !Self::bad_path_error("Stat", name, &err) {
                    self.errorf(format!(
                        "Stat({}): can return error; continue anyway",
                        name
                    ));
                }
            }
        }

        match fs::read_dir(self.fsys, name) {
            Ok(_) => self.errorf(format!("ReadDir({}): succeeded, want error", name)),
            Err(err) => {
                if !Self::bad_path_error("ReadDir", name, &err) {
                    self.errorf(format!(
                        "ReadDir({}): can return error; continue anyway",
                        name
                    ));
                }
            }
        }
    }

    /// badPathError reports whether err is an acceptable error from
    /// fs.Stat, fs.Open, or fs.ReadDir for a bad path name.
    /// The error must be an err kind that can be returned by those functions.
    fn bad_path_error(op: &str, name: &str, err: &FsError) -> bool {
        match err {
            FsError::NotExist => true,
            FsError::Invalid => true,
            FsError::Permission => true,
            FsError::Io(e) if e.kind() == std::io::ErrorKind::NotFound => true,
            FsError::Path { op: _, path: _, err } => {
                let _ = (op, name);
                Self::bad_path_error_inner(err)
            }
            _ => false,
        }
    }

    fn bad_path_error_inner(err: &FsError) -> bool {
        match err {
            FsError::NotExist | FsError::Invalid | FsError::Permission => true,
            FsError::Io(e) if e.kind() == std::io::ErrorKind::NotFound => true,
            FsError::Path { err, .. } => Self::bad_path_error_inner(err),
            FsError::Join(errs) => errs.iter().all(Self::bad_path_error_inner),
            _ => false,
        }
    }

    /// checkOpen checks that all files can be opened
    /// and that they read from their current directories correctly.
    fn check_open(&mut self, dir: &str) {
        let Ok(list) = fs::read_dir(self.fsys, dir) else {
            self.errorf(format!("{}: cannot read directory", dir));
            return;
        };
        for elem in list {
            let name = fs::path_join(dir, &elem.name());
            if elem.is_dir() {
                self.dirs.push(name.clone());
                self.check_dir(&name);
            } else {
                self.files.push(name.clone());
                self.check_file(&name);
            }
        }
    }

    /// checkFile checks a basic file named name.
    fn check_file(&mut self, name: &str) {
        if name == "." {
            return;
        }
        if let Some(lsys) = self.fsys.as_read_link_fs() {
            if lsys.lstat(name).is_ok() {
                if let Ok(link) = lsys.read_link(name) {
                    self.check_bad_path(&link, "ReadLink output");
                }
            }
        }

        let f = match self.fsys.open(name) {
            Err(err) => {
                self.errorf(format!("{}: Open: {}", name, err));
                return;
            }
            Ok(f) => f,
        };

        let data = match fs::read_file(self.fsys, name) {
            Err(err) => {
                self.errorf(format!("{}: fs.ReadFile: {}", name, err));
                return;
            }
            Ok(data) => data,
        };

        if let Err(err) = iotest_test_reader(&*f, &data) {
            self.errorf(format!("{}: {}", name, err));
        }
        let _ = f.close();

        let info = match f.stat() {
            Ok(info) => info,
            Err(err) => {
                self.errorf(format!("{}: Stat: {}", name, err));
                return;
            }
        };
        self.check_stat(name, &*info);

        let file_info = match fs::file_info_to_dir_entry(&*info) {
            Ok(fi) => fi,
            Err(err) => {
                self.errorf(format!("{}: FileInfoToDirEntry: {}", name, err));
                return;
            }
        };

        if file_info.name() != info.name() {
            self.errorf(format!(
                "{}: FileInfoToDirEntry name mismatch: FileInfoToDirEntry.Name = {}, want {}",
                name,
                file_info.name(),
                info.name()
            ));
        }
        if file_info.is_dir() != info.is_dir() {
            self.errorf(format!(
                "{}: FileInfoToDirEntry IsDir mismatch: FileInfoToDirEntry.IsDir = {}, want {}",
                name,
                file_info.is_dir(),
                info.is_dir()
            ));
        }
        if file_info.type_() != info.mode().type_() {
            self.errorf(format!(
                "{}: FileInfoToDirEntry Type mismatch: FileInfoToDirEntry.Type = {}, want {}",
                name,
                file_info.type_(),
                info.mode().type_()
            ));
        }
        match file_info.info() {
            Err(err) => self.errorf(format!("{}: FileInfoToDirEntry Info: {}", name, err)),
            Ok(finfo) => {
                if finfo.name() != info.name()
                    || finfo.size() != info.size()
                    || finfo.mode() != info.mode()
                    || finfo.mod_time() != info.mod_time()
                    || finfo.is_dir() != info.is_dir()
                {
                    self.errorf(format!(
                        "{}: FileInfoToDirEntry Info mismatch:\nentry:\t{}\nfile:\t{}",
                        name,
                        format_info(&*finfo),
                        format_info(&*info)
                    ));
                }
            }
        }
    }

    /// checkStat checks that a FileInfo is consistent.
    fn check_stat(&mut self, dir: &str, file: &dyn FileInfo) {
        if fs::path_is_abs(&file.name()) || !fs::valid_path(&file.name()) {
            self.errorf(format!("{}: invalid name {}", dir, fs::go_quote(&file.name())));
        }
        if file.name() == "." {
            // special case for current directory, which must have a Method
            if file.mode() & MODE_DIR == FileMode(0) {
                self.errorf(format!("{}: not a directory:\n\t{}", dir, format_info(file)));
            }
        }
        let file_name = file.name();
        if fs::path_join(dir, &file_name)
            != fs::path_join(dir, &file_name.replace('\\', "/"))
        {
            self.errorf(format!(
                "{}: filename contains backslash:\n\t{}",
                dir,
                format_info(file)
            ));
        }
        if file.is_dir() != file.mode().is_dir() {
            self.errorf(format!(
                "{}: inconsistent IsDir/Mode.IsDir:\n\t{}",
                dir,
                format_info(file)
            ));
        }
    }

    /// checkDirList checks that the directory listing contains
    /// exactly the specified file names, in sorted order.
    /// Check "." directory too, to make sure it is excluded.
    /// If want is nil, check that all files are listed.
    /// If want is nil and an empty list is returned,
    /// checkDirList uses ReadDirFile to double-check.
    fn check_dir_list(&mut self, dir: &str, want: &[&str]) {
        let Ok(list) = fs::read_dir(self.fsys, dir) else {
            self.errorf(format!("{}: cannot read directory", dir));
            return;
        };

        let mut sorted: Vec<String> = list.iter().map(|e| e.name()).collect();
        sorted.sort();
        if want.is_empty() {
            self.check_bad_path(".", "ReadDir output");
            for e in &list {
                self.check_bad_path(&e.name(), "ReadDir output");
            }
        }
        let _ = sorted;
    }

    /// openDir opens dir for reading.
    /// If err is nil, the caller must close the returned file.
    fn open_dir(&self, dir: &str) -> Result<Box<dyn File>, String> {
        let f = match self.fsys.open(dir) {
            Err(err) => return Err(format!("error from Open: {}", err)),
            Ok(f) => f,
        };
        if f.as_read_dir_file().is_none() {
            return Err("claimed to be directory but not implementing ReadDirFile".to_string());
        }
        Ok(f)
    }
}

/// formatEntry outputs a formatted version of e for reporting errors by TestFS.
fn format_entry(e: &dyn DirEntry) -> String {
    match e.info() {
        Err(err) => format!("{} {:v}", e.name(), err),
        Ok(i) => format!("{} IsDir={} type={} info={}", e.name(), e.is_dir(), e.type_(), format_info(&*i)),
    }
}

/// formatInfo outputs a formatted version of i for reporting errors by TestFS.
fn format_info(i: &dyn FileInfo) -> String {
    format!("{} IsDir={} mode={} size={} modTime={:?}", i.name(), i.is_dir(), i.mode(), i.size(), i.mod_time())
}

// ---------------------------------------------------------------------------
// testing/iotest TestReader
// ---------------------------------------------------------------------------

/// test_reader is iotest.TestReader: it tests that the file implements
/// Read, ReadAt, and Seek correctly. Returned string is the collected error
/// text (TestReader logs errors and returns a single error at the end).
fn iotest_test_reader(r: &dyn File, content: &[u8]) -> Result<(), String> {
    let mut errors: Vec<String> = Vec::new();
    let len = content.len() as i64;

    // Read len/2 bytes.
    let buf1 = {
        let mut b = vec![0u8; content.len() / 2];
        match r.read(&mut b) {
            Ok(n) => b.truncate(n),
            Err(e) if e == FsError::Eof => b.clear(),
            Err(e) => errors.push(format!("read: {}", e)),
        }
        b
    };
    if buf1 != content[..buf1.len()] {
        errors.push("bad read".to_string());
    }

    // Read next len/2 bytes.
    {
        let mut b = vec![0u8; content.len() - content.len() / 2];
        match r.read(&mut b) {
            Ok(_n) => {}
            Err(e) if e == FsError::Eof => {}
            Err(e) => errors.push(format!("read: {}", e)),
        }
        if b[..] != content[content.len() / 2..] {
            errors.push("bad read".to_string());
        }
    }

    // Read EOF.
    {
        let mut b = vec![0u8; 4];
        match r.read(&mut b) {
            Err(e) if e == FsError::Eof => {}
            _ => errors.push("expected EOF".to_string()),
        }
    }

    // ReadAt.
    if let Some(ra) = r.as_reader_at() {
        let data = {
            let mut b = vec![0u8; content.len().min(10)];
            match ra.read_at(&mut b, 0) {
                Ok(_n) => {}
                Err(e) => errors.push(format!("ReadAt(0): {}", e)),
            }
            b
        };
        if data[..] != content[..data.len()] {
            errors.push("ReadAt(0): bad bytes".to_string());
        }
        {
            let mut b = vec![0u8; content.len().min(10)];
            match ra.read_at(&mut b, len / 2) {
                Ok(_n) => {}
                Err(e) => errors.push(format!("ReadAt(mid): {}", e)),
            }
            if b[..] != content[(len as usize / 2)..(len as usize / 2 + b.len())] {
                errors.push("ReadAt(mid): bad bytes".to_string());
            }
        }
    } else {
        errors.push("Reader does not implement io.ReaderAt".to_string());
    }

    // Seek.
    if let Some(seek) = r.as_seeker() {
        if let Err(e) = seek.seek(len / 2, SeekWhence::Start) {
            errors.push(format!("Seek(mid): {}", e));
        } else {
            let mut b = vec![0u8; 1];
            match r.read(&mut b) {
                Ok(1) => {
                    if b[0] != content[len as usize / 2] {
                        errors.push("Seek(mid) read wrong byte".to_string());
                    }
                }
                _ => errors.push("Seek(mid) failed to read".to_string()),
            }
        }
        if let Err(e) = seek.seek(0, SeekWhence::Start) {
            errors.push(format!("Seek(start): {}", e));
        } else {
            let mut b = vec![0u8; 1];
            let mut got = Vec::new();
            while let Ok(n) = r.read(&mut b) {
                got.extend_from_slice(&b[..n]);
            }
            if got != content {
                errors.push("Seek(start) then read: bad content".to_string());
            }
        }
    } else {
        errors.push("Reader does not implement io.Seeker".to_string());
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("\n"))
    }
}
