// Ported from tsc/internal/project/overlayfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::any::Any;
use std::sync::{Arc, OnceLock, RwLock};
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_ast::Uint128;
use tsc_core::core;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::textchange::TextChange;
use tsc_lsconv::{self, Converters, LspLineMap, Script, new_converters};
use tsc_lsproto::{DocumentUri, PositionEncodingKind};
use tsc_sourcemap::{EcmaLineInfo, create_ecma_line_info};
use tsc_spanmap::spanmap::Feature;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::fs::{FileInfo, FileMode, FsError, MODE_DIR};
use tsc_vfs::{Entries, Vfs};

use crate::filechange::{FileChange, FileChangeKind, FileChangeSummary};
use crate::parsecache::hash_string_128;

/// `FileContent`.
pub trait FileContent {
    fn content(&self) -> &str;
    fn hash(&self) -> Uint128;
}

/// `FileHandle`.
pub trait FileHandle: FileContent + Send + Sync {
    fn file_name(&self) -> &RootedFilePath;
    fn version(&self) -> i32;
    fn matches_disk_text(&self) -> bool;
    fn is_overlay(&self) -> bool;
    fn lsp_line_map(&self) -> &LspLineMap;
    fn ecma_line_info(&self) -> &EcmaLineInfo;
    fn kind(&self) -> ScriptKind;
}

/// `fileBase`.
///
/// PORT: `sync.Once` becomes `OnceLock`; line maps are computed lazily and
/// cached, matching Go.
pub struct FileBase {
    pub file_name: RootedFilePath,
    pub content: String,
    pub hash: Uint128,

    line_map: OnceLock<LspLineMap>,
    line_info: OnceLock<EcmaLineInfo>,
}

impl FileBase {
    /// `newFileBase` — the `newCachedFile`/`newOverlay` shared initializer.
    pub fn new(file_name: RootedFilePath, content: String, hash: Uint128) -> FileBase {
        FileBase {
            file_name,
            content,
            hash,
            line_map: OnceLock::new(),
            line_info: OnceLock::new(),
        }
    }

    /// `(f *fileBase) LSPLineMap`.
    pub fn lsp_line_map(&self) -> &LspLineMap {
        self.line_map
            .get_or_init(|| tsc_lsconv::compute_lsp_line_starts(self.content.as_bytes()))
    }

    /// `(f *fileBase) ECMALineInfo`.
    pub fn ecma_line_info(&self) -> &EcmaLineInfo {
        self.line_info.get_or_init(|| {
            let line_starts = core::compute_ecma_line_starts(&self.content);
            create_ecma_line_info(self.content.clone(), line_starts)
        })
    }
}

/// `cachedFile`.
pub struct CachedFile {
    pub base: FileBase,
    pub needs_reload: bool,
    pub realpath_path: PathKey,
}

/// `newCachedFile`.
pub fn new_cached_file(file_name: RootedFilePath, content: String) -> CachedFile {
    let hash = hash_string_128(&content);
    CachedFile {
        base: FileBase::new(file_name, content, hash),
        needs_reload: false,
        realpath_path: PathKey::default(),
    }
}

/// `NewCachedFileHandle`.
pub fn new_cached_file_handle(file_name: RootedFilePath, content: String) -> Arc<dyn FileHandle> {
    Arc::new(new_cached_file(file_name, content))
}

impl FileContent for CachedFile {
    fn content(&self) -> &str {
        &self.base.content
    }
    fn hash(&self) -> Uint128 {
        self.base.hash
    }
}

impl FileHandle for CachedFile {
    fn file_name(&self) -> &RootedFilePath {
        &self.base.file_name
    }
    fn version(&self) -> i32 {
        0
    }
    fn matches_disk_text(&self) -> bool {
        !self.needs_reload
    }
    fn is_overlay(&self) -> bool {
        false
    }
    fn lsp_line_map(&self) -> &LspLineMap {
        self.base.lsp_line_map()
    }
    fn ecma_line_info(&self) -> &EcmaLineInfo {
        self.base.ecma_line_info()
    }
    fn kind(&self) -> ScriptKind {
        core::get_script_kind_from_file_name(&self.base.file_name)
    }
}

/// `(f *cachedFile) Clone` — `dirty.Cloneable` for the snapshot's cache maps.
impl Clone for CachedFile {
    fn clone(&self) -> Self {
        // Go's Clone copies the mutable fields; the lazily computed line maps
        // are recomputed on demand (sync.Once zero value).
        CachedFile {
            base: FileBase::new(
                self.base.file_name.clone(),
                self.base.content.clone(),
                self.base.hash,
            ),
            needs_reload: self.needs_reload,
            realpath_path: self.realpath_path.clone(),
        }
    }
}

impl tsc_dirty::Cloneable for CachedFile {
    fn clone_value(&self) -> Self {
        self.clone()
    }
}

/// `Overlay`.
pub struct Overlay {
    pub base: FileBase,
    pub version: i32,
    pub kind: ScriptKind,
    pub matches_disk_text: bool,
}

/// `newOverlay`.
pub fn new_overlay(
    file_name: RootedFilePath,
    content: String,
    version: i32,
    kind: ScriptKind,
) -> Overlay {
    let hash = hash_string_128(&content);
    Overlay {
        base: FileBase::new(file_name, content, hash),
        version,
        kind,
        matches_disk_text: false,
    }
}

impl Overlay {
    /// `(o *Overlay) Text`.
    pub fn text(&self) -> &str {
        &self.base.content
    }

    /// `(o *Overlay) computeMatchesDiskText` — may return false negatives,
    /// but never false positives.
    ///
    /// TODO: !!! optimization: incorporate mtime
    pub fn compute_matches_disk_text(&self, fs: &dyn Vfs) -> (bool, bool) {
        if self.base.file_name.is_dynamic() {
            return (false, false);
        }
        let Some(disk_content) = fs.read_file(&self.base.file_name) else {
            return (false, false);
        };
        (hash_string_128(&disk_content) == self.base.hash, true)
    }
}

impl FileContent for Overlay {
    fn content(&self) -> &str {
        &self.base.content
    }
    fn hash(&self) -> Uint128 {
        self.base.hash
    }
}

impl FileHandle for Overlay {
    fn file_name(&self) -> &RootedFilePath {
        &self.base.file_name
    }
    fn version(&self) -> i32 {
        self.version
    }
    /// MatchesDiskText may return false negatives, but never false positives.
    fn matches_disk_text(&self) -> bool {
        self.matches_disk_text
    }
    fn is_overlay(&self) -> bool {
        true
    }
    fn lsp_line_map(&self) -> &LspLineMap {
        self.base.lsp_line_map()
    }
    fn ecma_line_info(&self) -> &EcmaLineInfo {
        self.base.ecma_line_info()
    }
    fn kind(&self) -> ScriptKind {
        self.kind
    }
}

/// `lsconv.Script` for `Overlay` — `SpanMap`/`OriginalText`: an overlay holds
/// the editor's raw text (for a content-mapped file, that is the original
/// foreign text, not the transformed output), so it never carries a span map
/// and its original text is its own text.
impl Script for Overlay {
    fn file_name(&self) -> &RootedFilePath {
        &self.base.file_name
    }
    fn original_file_name(&self) -> &RootedFilePath {
        &self.base.file_name
    }
    fn text(&self) -> &[u8] {
        self.base.content.as_bytes()
    }
    fn span_map(&self) -> Option<Arc<tsc_spanmap::spanmap::SpanMap>> {
        None
    }
    fn original_text(&self) -> &[u8] {
        self.base.content.as_bytes()
    }
}

/// `FileHandleSource`.
pub trait FileHandleSource: Send + Sync {
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>>;
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>>;
}

/// `LayeredFileSystem`.
///
/// PORT: `&dyn LayeredFileSystem` cannot be coerced to `&dyn Vfs`/`&dyn
/// FileHandleSource` on Rust 1.85, so the trait carries explicit adapter
/// methods plus downcast hooks for the Go interface assertions in
/// `layerOverlayFileSystem` and `cachedLayeredFileSystem.ExpandFileChanges`.
pub trait LayeredFileSystem: Vfs + FileHandleSource {
    fn overlays(&self) -> FxHashMap<PathKey, Arc<Overlay>>;
    /// `(fs.(*overlayFS))` — `None` unless `self` is an `OverlayFs`.
    fn as_overlay_fs(&self) -> Option<&OverlayFs> {
        None
    }
    /// `(fs.(RebasableFileSystem))` — `None` unless `self` is rebasable.
    fn as_rebasable(&self) -> Option<Arc<dyn RebasableFileSystem>> {
        None
    }
    /// `(fs.(FileChangeExpander))` — the default is no expansion.
    fn expand_file_changes(&self, change: FileChangeSummary) -> FileChangeSummary {
        change
    }
    /// `Any` handle for additional downcasts by sibling layers.
    fn as_any(&self) -> &dyn Any;
}

/// `RebasableFileSystem`.
pub trait RebasableFileSystem: Vfs {
    /// `BaseFileSystem` — PORT: returns [`LayeredFsInput`] so the
    /// `base.(*overlayFS)` assertion in `layerOverlayFileSystem` can detect a
    /// layered base without `Any` downcasting of `dyn Vfs`.
    fn base_file_system(&self) -> LayeredFsInput;
    /// `WithBaseFileSystem`.
    fn with_base_file_system(&self, base: Arc<dyn LayeredFileSystem>)
    -> Arc<dyn LayeredFileSystem>;
}

/// Input to [`layer_overlay_file_system`] — the Go parameter is `vfs.FS`
/// with interface assertions for `RebasableFileSystem` and `*overlayFS`;
/// Rust encodes the same three dynamic cases explicitly.
#[derive(Clone)]
pub enum LayeredFsInput {
    /// A plain `vfs.FS` (host disk file system etc.).
    Plain(Arc<dyn Vfs>),
    /// A `vfs.FS` that is also a `FileHandleSource` (e.g. `sourceFS`,
    /// `SnapshotFS`) but not layered.
    WithSource(Arc<dyn Vfs>, Arc<dyn FileHandleSource>),
    /// An existing `LayeredFileSystem` (`*overlayFS`,
    /// `cachedLayeredFileSystem`, or a rebased layer).
    Layered(Arc<dyn LayeredFileSystem>),
    /// A `RebasableFileSystem` (e.g. the request file system — asserted
    /// before `*overlayFS` in Go).
    Rebasable(Arc<dyn RebasableFileSystem>),
}

/// `overlayFS`.
pub struct OverlayFs {
    case_sensitivity: CaseSensitivity,
    host: Arc<dyn Vfs>,
    /// PORT: Go asserts `fs.host.(FileHandleSource)` inside
    /// `get_file_by_path`; Rust stores the optional source alongside the vfs
    /// handle (see [`layer_overlay_file_system`]).
    host_source: Option<Arc<dyn FileHandleSource>>,
    position_encoding: PositionEncodingKind,

    state: RwLock<OverlayFsState>,
}

struct OverlayFsState {
    overlays: FxHashMap<PathKey, Arc<Overlay>>,
    overlay_directories: FxHashMap<PathKey, FxHashMap<PathKey, String>>,
}

/// `newOverlayFS` — `host_source` is `Some` when `host` implements
/// `FileHandleSource` (Go's `fs.host.(FileHandleSource)` assertion).
pub fn new_overlay_fs(
    fs: Arc<dyn Vfs>,
    host_source: Option<Arc<dyn FileHandleSource>>,
    overlays: FxHashMap<PathKey, Arc<Overlay>>,
    position_encoding: PositionEncodingKind,
) -> OverlayFs {
    OverlayFs {
        case_sensitivity: fs.case_sensitivity(),
        host: fs,
        host_source,
        position_encoding,
        state: RwLock::new(OverlayFsState {
            overlay_directories: create_overlay_directories(&overlays),
            overlays,
        }),
    }
}

/// `layerOverlayFileSystem`.
pub fn layer_overlay_file_system(
    file_system: LayeredFsInput,
    overlays: FxHashMap<PathKey, Arc<Overlay>>,
    position_encoding: PositionEncodingKind,
) -> Arc<dyn LayeredFileSystem> {
    let mut layer: Option<Arc<dyn RebasableFileSystem>> = None;
    let mut base: LayeredFsInput = file_system;
    let rebasable = match &base {
        LayeredFsInput::Rebasable(r) => Some(r.clone()),
        LayeredFsInput::Layered(l) => l.as_rebasable(),
        _ => None,
    };
    if let Some(candidate) = rebasable {
        layer = Some(candidate.clone());
        base = candidate.base_file_system();
    }
    let (base_vfs, base_source): (Arc<dyn Vfs>, Option<Arc<dyn FileHandleSource>>) = match base {
        // if previous, ok := base.(*overlayFS); base = previous.host
        LayeredFsInput::Layered(l) => {
            if let Some(previous) = l.as_overlay_fs() {
                (previous.host.clone(), previous.host_source.clone())
            } else {
                (
                    Arc::new(LayeredFileSystemVfs(l.clone())),
                    Some(Arc::new(LayeredFileHandleSource(l.clone()))),
                )
            }
        }
        LayeredFsInput::WithSource(v, s) => (v, Some(s)),
        LayeredFsInput::Plain(v) => (v, None),
        // `Rebasable` can only appear as the input, which was already
        // decomposed above; `base_file_system` results never produce one.
        LayeredFsInput::Rebasable(r) => (Arc::new(RebasableFileSystemVfs(r)), None),
    };
    let overlay: Arc<dyn LayeredFileSystem> = Arc::new(new_overlay_fs(
        base_vfs,
        base_source,
        overlays,
        position_encoding,
    ));
    match layer {
        None => overlay,
        Some(layer) => layer.with_base_file_system(overlay),
    }
}

/// `vfs.FS` view over a `LayeredFileSystem` — used when a layered FS must be
/// passed where `Arc<dyn Vfs>` is required (PORT: Rust <1.86 lacks trait
/// upcasting).
struct LayeredFileSystemVfs(Arc<dyn LayeredFileSystem>);

/// `vfs.FS` view over a `RebasableFileSystem` — same adapter for the
/// `Rebasable` arm of [`LayeredFsInput`].
struct RebasableFileSystemVfs(Arc<dyn RebasableFileSystem>);

/// `FileHandleSource` view over a `LayeredFileSystem` — same trait-object
/// adapter as [`LayeredFileSystemVfs`], needed because trait upcasting is
/// unavailable.
struct LayeredFileHandleSource(Arc<dyn LayeredFileSystem>);

impl FileHandleSource for LayeredFileHandleSource {
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.0.get_file(file_name)
    }
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        self.0.get_file_by_path(file_name, path)
    }
}

macro_rules! forward_vfs {
    ($impler:ty, $field:tt) => {
        impl Vfs for $impler {
            fn case_sensitivity(&self) -> CaseSensitivity {
                self.$field.case_sensitivity()
            }
            fn file_exists(&self, path: &RootedFilePath) -> bool {
                self.$field.file_exists(path)
            }
            fn read_file(&self, path: &RootedFilePath) -> Option<String> {
                self.$field.read_file(path)
            }
            fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
                self.$field.write_file(path, data)
            }
            fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
                self.$field.append_file(path, data)
            }
            fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
                self.$field.remove(path)
            }
            fn chtimes(
                &self,
                path: &RootedPath,
                a_time: SystemTime,
                m_time: SystemTime,
            ) -> Result<(), FsError> {
                self.$field.chtimes(path, a_time, m_time)
            }
            fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
                self.$field.directory_exists(path)
            }
            fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
                self.$field.get_accessible_entries(path)
            }
            fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
                self.$field.stat(path)
            }
            fn realpath(&self, path: &RootedPath) -> RootedPath {
                self.$field.realpath(path)
            }
        }
    };
}

forward_vfs!(LayeredFileSystemVfs, 0);
forward_vfs!(RebasableFileSystemVfs, 0);

/// Public form of [`LayeredFileSystemVfs`] for sibling modules that need the
/// same adapter (e.g. passing the layered fs to `Arc<dyn Vfs>` parameters).
pub fn layered_as_vfs(layered: Arc<dyn LayeredFileSystem>) -> Arc<dyn Vfs> {
    Arc::new(LayeredFileSystemVfs(layered))
}

impl LayeredFileSystem for OverlayFs {
    /// `(fs *overlayFS) Overlays`.
    fn overlays(&self) -> FxHashMap<PathKey, Arc<Overlay>> {
        self.state.read().unwrap().overlays.clone()
    }
    fn as_overlay_fs(&self) -> Option<&OverlayFs> {
        Some(self)
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl FileHandleSource for OverlayFs {
    /// `(fs *overlayFS) GetFile`.
    fn get_file(&self, file_name: &RootedFilePath) -> Option<Arc<dyn FileHandle>> {
        self.get_file_by_path(
            file_name,
            &self.case_sensitivity.path_key(&file_name.as_path()),
        )
    }

    /// `(fs *overlayFS) GetFileByPath`.
    fn get_file_by_path(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<dyn FileHandle>> {
        let (overlay, directory) = {
            let state = self.state.read().unwrap();
            (
                state.overlays.get(path).cloned(),
                state.overlay_directories.contains_key(path),
            )
        };
        if let Some(overlay) = overlay {
            return Some(overlay);
        }
        if directory {
            return None;
        }

        if let Some(source) = &self.host_source {
            return source.get_file_by_path(file_name, path);
        }
        let content = self.host.read_file(file_name)?;
        Some(Arc::new(new_cached_file(file_name.clone(), content)))
    }
}

impl Vfs for OverlayFs {
    /// `(fs *overlayFS) CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    /// `(fs *overlayFS) FileExists`.
    fn file_exists(&self, file_name: &RootedFilePath) -> bool {
        let (file, directory) = {
            let state = self.state.read().unwrap();
            let path = self.case_sensitivity.path_key(&file_name.as_path());
            (
                state.overlays.contains_key(&path),
                state.overlay_directories.contains_key(&path),
            )
        };
        file || (!directory && self.host.file_exists(file_name))
    }

    /// `(fs *overlayFS) ReadFile`.
    fn read_file(&self, file_name: &RootedFilePath) -> Option<String> {
        let file = self.get_file(file_name)?;
        Some(file.content().to_string())
    }

    /// `(fs *overlayFS) WriteFile`.
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.host.write_file(path, data)
    }

    /// `(fs *overlayFS) AppendFile`.
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.host.append_file(path, data)
    }

    /// `(fs *overlayFS) Remove`.
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.host.remove(path)
    }

    /// `(fs *overlayFS) Chtimes`.
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.host.chtimes(path, a_time, m_time)
    }

    /// `(fs *overlayFS) DirectoryExists`.
    fn directory_exists(&self, directory_name: &RootedDirectoryPath) -> bool {
        let (file, directory) = {
            let state = self.state.read().unwrap();
            let path = self.case_sensitivity.path_key(&directory_name.as_path());
            (
                state.overlays.contains_key(&path),
                state.overlay_directories.contains_key(&path),
            )
        };
        directory || (!file && self.host.directory_exists(directory_name))
    }

    /// `(fs *overlayFS) GetAccessibleEntries`.
    fn get_accessible_entries(&self, directory_name: &RootedDirectoryPath) -> Entries {
        let (file, directory, overlays) = {
            let state = self.state.read().unwrap();
            let path = self.case_sensitivity.path_key(&directory_name.as_path());
            (
                state.overlays.contains_key(&path),
                state.overlay_directories.get(&path).cloned(),
                state.overlays.clone(),
            )
        };
        if file {
            return Entries::default();
        }
        let host_entries = self.host.get_accessible_entries(directory_name);
        let mut entries = Entries {
            files: host_entries.files.clone(),
            directories: host_entries.directories.clone(),
            symlinks: host_entries.symlinks.clone(),
        };
        let equal_name = |left: &str, right: &str| {
            (self.case_sensitivity.get_comparer())(left, right) == 0
        };
        if let Some(directory) = directory {
            for (child_path, child_name) in &directory {
                entries
                    .files
                    .retain(|name| !equal_name(name, child_name));
                entries
                    .directories
                    .retain(|name| !equal_name(name, child_name));
                if let Some(symlinks) = &mut entries.symlinks {
                    symlinks.retain(|name| !equal_name(name, child_name));
                }
                if overlays.contains_key(child_path) {
                    entries.files.push(child_name.clone());
                } else {
                    entries.directories.push(child_name.clone());
                }
            }
        }
        entries
    }

    /// `(fs *overlayFS) Stat`.
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        let (overlay, directory) = {
            let state = self.state.read().unwrap();
            let canonical_path = self.case_sensitivity.path_key(path);
            (
                state.overlays.get(&canonical_path).cloned(),
                state.overlay_directories.contains_key(&canonical_path),
            )
        };
        if let Some(overlay) = overlay {
            return Some(Arc::new(OverlayFileInfo { overlay }));
        }
        if directory {
            return Some(Arc::new(OverlayDirectoryInfo {
                name: path.base_name().to_string(),
            }));
        }
        self.host.stat(path)
    }

    /// `(fs *overlayFS) Realpath`.
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.host.realpath(path)
    }
}

/// `overlayFileInfo`.
struct OverlayFileInfo {
    overlay: Arc<Overlay>,
}

impl FileInfo for OverlayFileInfo {
    fn name(&self) -> String {
        self.overlay.base.file_name.base_name().to_string()
    }
    fn size(&self) -> i64 {
        self.overlay.base.content.len() as i64
    }
    fn mode(&self) -> FileMode {
        FileMode(0o444)
    }
    fn mod_time(&self) -> SystemTime {
        SystemTime::UNIX_EPOCH
    }
    fn is_dir(&self) -> bool {
        false
    }
    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>> {
        None
    }
}

/// `overlayDirectoryInfo`.
struct OverlayDirectoryInfo {
    name: String,
}

impl FileInfo for OverlayDirectoryInfo {
    fn name(&self) -> String {
        self.name.clone()
    }
    fn size(&self) -> i64 {
        0
    }
    fn mode(&self) -> FileMode {
        FileMode(MODE_DIR.0 | 0o555)
    }
    fn mod_time(&self) -> SystemTime {
        SystemTime::UNIX_EPOCH
    }
    fn is_dir(&self) -> bool {
        true
    }
    fn sys(&self) -> Option<Arc<dyn Any + Send + Sync>> {
        None
    }
}

/// `createOverlayDirectories`.
fn create_overlay_directories(
    overlays: &FxHashMap<PathKey, Arc<Overlay>>,
) -> FxHashMap<PathKey, FxHashMap<PathKey, String>> {
    let mut overlay_directories: FxHashMap<PathKey, FxHashMap<PathKey, String>> =
        FxHashMap::default();
    for (path, overlay) in overlays {
        let mut child_path = path.clone();
        let mut child = overlay.base.file_name.as_path();
        loop {
            let parent_path = child_path.parent();
            let parent = child.directory();
            if child_path == parent_path {
                break;
            }
            overlay_directories
                .entry(parent_path.clone())
                .or_default()
                .insert(child_path.clone(), child.base_name().to_string());
            child_path = parent_path;
            child = parent.as_path();
        }
    }
    overlay_directories
}

impl OverlayFs {
    /// `(fs *overlayFS) processChanges`.
    pub fn process_changes(
        &self,
        changes: Vec<FileChange>,
    ) -> (FileChangeSummary, FxHashMap<PathKey, Arc<Overlay>>) {
        let mut result = FileChangeSummary::default();

        let mut new_overlays = {
            let state = self.state.read().unwrap();
            state.overlays.clone()
        };

        // Reduced collection of changes that occurred on a single file
        #[derive(Default)]
        struct FileEvents {
            open_change: Option<FileChange>,
            close_change: Option<FileChange>,
            watch_changed: bool,
            changes: Vec<FileChange>,
            saved: bool,
            created: bool,
            deleted: bool,
        }

        let mut file_event_map: FxHashMap<DocumentUri, FileEvents> = FxHashMap::default();

        for change in changes {
            let uri = change.uri.clone();
            if let Some(events) = file_event_map.get(&uri) {
                if events.open_change.is_some() {
                    panic!("should see no changes after open");
                }
            }
            let events = file_event_map.entry(uri.clone()).or_default();

            if !result.includes_watch_change_outside_node_modules
                && change.kind.is_watch_kind()
                && !uri.as_str().contains("/node_modules/")
            {
                result.includes_watch_change_outside_node_modules = true;
            }

            match change.kind {
                FileChangeKind::Open => {
                    events.close_change = None;
                    events.open_change = Some(change);
                    events.watch_changed = false;
                    events.changes = Vec::new();
                    events.saved = false;
                    events.created = false;
                    events.deleted = false;
                }
                FileChangeKind::Close => {
                    events.close_change = Some(change);
                    events.changes = Vec::new();
                    events.saved = false;
                    events.watch_changed = false;
                }
                FileChangeKind::Change => {
                    if events.close_change.is_some() {
                        panic!("should see no changes after close");
                    }
                    events.changes.push(change);
                    events.saved = false;
                    events.watch_changed = false;
                }
                FileChangeKind::Save => {
                    events.saved = true;
                }
                FileChangeKind::WatchCreate => {
                    if events.deleted {
                        // Delete followed by create becomes a change
                        events.deleted = false;
                        events.watch_changed = true;
                    } else {
                        events.created = true;
                    }
                }
                FileChangeKind::WatchChange => {
                    if !events.created {
                        events.watch_changed = true;
                        events.saved = false;
                    }
                }
                FileChangeKind::WatchDelete => {
                    events.watch_changed = false;
                    events.saved = false;
                    // Delete after create cancels out
                    if events.created {
                        events.created = false;
                    } else {
                        events.deleted = true;
                    }
                }
            }
        }

        // Process deduplicated events per file
        for (uri, events) in &file_event_map {
            let path = uri.path_key(self.case_sensitivity);
            let mut o = new_overlays.get(&path).cloned();

            if let Some(open_change) = &events.open_change {
                if !result.opened.as_str().is_empty() || !result.reopened.as_str().is_empty() {
                    panic!("can only process one file open event at a time");
                }
                match &o {
                    Some(existing) if existing.content() != open_change.content => {
                        result.changed.add(uri.clone());
                    }
                    None => {
                        result.opened = uri.clone();
                    }
                    _ => {
                        result.reopened = uri.clone();
                    }
                }
                let mut script_kind =
                    tsc_lsconv::language_kind_to_script_kind(&open_change.language_kind);
                if script_kind == ScriptKind::Unknown {
                    script_kind = core::get_script_kind_from_file_name(&uri.file_name());
                }
                new_overlays.insert(
                    path,
                    Arc::new(new_overlay(
                        uri.file_name(),
                        open_change.content.clone(),
                        open_change.version,
                        script_kind,
                    )),
                );
                continue;
            }

            if events.close_change.is_some() && o.is_some() {
                result.closed.add(uri.clone());
                new_overlays.remove(&path);
                o = None;
            }

            if events.watch_changed {
                if o.is_none() {
                    result.changed.add(uri.clone());
                } else if !events.saved {
                    let overlay = o.as_ref().unwrap();
                    let (matches_disk_text, _exists) =
                        overlay.compute_matches_disk_text(&*self.host);
                    if matches_disk_text != overlay.matches_disk_text {
                        let mut new_o = new_overlay(
                            overlay.base.file_name.clone(),
                            overlay.base.content.clone(),
                            overlay.version,
                            overlay.kind,
                        );
                        new_o.matches_disk_text = matches_disk_text;
                        o = Some(Arc::new(new_o));
                        new_overlays.insert(path.clone(), o.clone().unwrap());
                    }
                }
            }

            if !events.changes.is_empty() && o.is_some() {
                result.changed.add(uri.clone());
                let mut cur = o.clone().unwrap();
                for change in &events.changes {
                    for text_change in &change.changes {
                        if let Some(partial_change) = &text_change.partial {
                            // PORT: Go's getLineMap closure reads the mutable
                            // `o` variable lazily, so each FromLSPRange call
                            // sees the latest overlay. The Rust Converters
                            // borrows `&'a` line maps, so build it fresh for
                            // each partial change — the borrow ends before
                            // `cur` is reassigned.
                            let ranges = {
                                let cur_fh: &Arc<Overlay> = &cur;
                                let converters: Converters = new_converters(
                                    self.position_encoding.clone(),
                                    move |_: &RootedFilePath| cur_fh.lsp_line_map(),
                                );
                                converters.from_lsp_range(
                                    &*cur,
                                    partial_change.range.clone(),
                                    Feature::All,
                                )
                            };
                            tsc_debug::assert_!(
                                ranges.len() == 1,
                                "expected exactly one range for partial change"
                            );
                            let text_change = TextChange {
                                text_range: ranges[0].span,
                                new_text: partial_change.text.clone(),
                            };
                            let new_content = text_change.apply_to(&cur.base.content);
                            cur = Arc::new(new_overlay(
                                cur.base.file_name.clone(),
                                new_content,
                                change.version,
                                cur.kind,
                            ));
                        } else if let Some(whole_change) = &text_change.whole_document {
                            cur = Arc::new(new_overlay(
                                cur.base.file_name.clone(),
                                whole_change.text.clone(),
                                change.version,
                                cur.kind,
                            ));
                        }
                    }
                    if !change.changes.is_empty() {
                        let mut o_mut = cur.clone_shallow();
                        o_mut.version = change.version;
                        o_mut.base.hash = hash_string_128(&cur.base.content);
                        o_mut.matches_disk_text = false;
                        cur = Arc::new(o_mut);
                        new_overlays.insert(path.clone(), cur.clone());
                    }
                }
                o = Some(cur);
            }

            if events.saved {
                if let Some(overlay) = &o {
                    let mut new_o = new_overlay(
                        overlay.base.file_name.clone(),
                        overlay.base.content.clone(),
                        overlay.version,
                        overlay.kind,
                    );
                    new_o.matches_disk_text = true;
                    o = Some(Arc::new(new_o));
                    new_overlays.insert(path.clone(), o.clone().unwrap());
                } else if !events.watch_changed {
                    // File was saved but never opened via didOpen; treat as a
                    // disk change.
                    result.changed.add(uri.clone());
                }
            }

            if events.created && o.is_none() {
                result.created.add(uri.clone());
            }

            if events.deleted && o.is_none() {
                result.deleted.add(uri.clone());
            }
        }

        let overlay_directories = create_overlay_directories(&new_overlays);
        {
            let mut state = self.state.write().unwrap();
            state.overlays = new_overlays.clone();
            state.overlay_directories = overlay_directories;
        }
        (result, new_overlays)
    }
}

impl Overlay {
    /// Helper: the change loop replaces `o` with a copy that keeps lazily
    /// computed state uncomputed (matching `newOverlay` + field writes in
    /// Go, where the fresh overlay does not inherit `fileBase` once state).
    fn clone_shallow(&self) -> Overlay {
        Overlay {
            base: FileBase::new(
                self.base.file_name.clone(),
                self.base.content.clone(),
                self.base.hash,
            ),
            version: self.version,
            kind: self.kind,
            matches_disk_text: self.matches_disk_text,
        }
    }
}
