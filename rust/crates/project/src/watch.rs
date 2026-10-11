// Ported from tsc/internal/project/watch.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, RwLock};

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_collections::{Set, SyncMap};
use tsc_lsconv;
use tsc_lsproto::{
    FileSystemWatcher, PatternOrRelativePattern, RelativePattern, URI, WatchKind,
    WorkspaceFolderOrURI,
};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath,
};

/// `minWatchLocationDepth`.
pub const MIN_WATCH_LOCATION_DEPTH: usize = 2;

/// `WatcherID`.
pub type WatcherId = String;

/// `fileSystemWatcherKey`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct FileSystemWatcherKey {
    pattern: String,
    kind: WatchKind,
}

/// `fileSystemWatcherValue`.
struct FileSystemWatcherValue {
    count: i32,
    id: WatcherId,
}

/// `watchRegistry` tracks the current watch globs and how many individual
/// `WatchedFiles` reference each glob. It provides ref-count helpers so
/// callers don't manipulate the map directly.
///
/// All methods are safe for concurrent use; locking is handled internally.
pub struct WatchRegistry {
    entries: Mutex<FxHashMap<FileSystemWatcherKey, FileSystemWatcherValue>>,
    pending: Mutex<FxHashSet<WatcherId>>,
}

/// `newWatchRegistry`.
pub fn new_watch_registry() -> WatchRegistry {
    WatchRegistry {
        entries: Mutex::new(FxHashMap::default()),
        pending: Mutex::new(FxHashSet::default()),
    }
}

impl WatchRegistry {
    /// `Acquire` increments the ref count for a watcher. If this is the first
    /// reference (count goes from 0 to 1), it returns true so the caller
    /// knows to register the watcher with the client.
    pub fn acquire(&self, watcher: &FileSystemWatcher, id: WatcherId) -> bool {
        let mut entries = self.entries.lock().unwrap();
        let key = to_file_system_watcher_key(watcher);
        let value = entries.entry(key).or_insert_with(|| FileSystemWatcherValue {
            count: 0,
            id: id.clone(),
        });
        value.count += 1;
        value.count == 1
    }

    /// `Release` decrements the ref count for a watcher. If no references
    /// remain, the entry is removed and the function returns the WatcherID
    /// and true so the caller knows to unregister the watcher from the
    /// client.
    pub fn release(&self, watcher: &FileSystemWatcher) -> Option<WatcherId> {
        let mut entries = self.entries.lock().unwrap();
        let key = to_file_system_watcher_key(watcher);
        let value = entries.get_mut(&key)?;
        if value.count <= 1 {
            let id = value.id.clone();
            entries.remove(&key);
            return Some(id);
        }
        value.count -= 1;
        None
    }

    /// `MarkPending` records that a watcher's registration failed and needs
    /// retry.
    pub fn mark_pending(&self, id: &WatcherId) {
        self.pending.lock().unwrap().insert(id.clone());
    }

    /// `ClearPending` removes a watcher from the pending set after successful
    /// registration.
    pub fn clear_pending(&self, id: &WatcherId) {
        self.pending.lock().unwrap().remove(id);
    }

    /// `IsPending` returns true if the watcher needs retry due to a previous
    /// failure.
    pub fn is_pending(&self, id: &WatcherId) -> bool {
        self.pending.lock().unwrap().contains(id)
    }
}

/// `PatternsAndIgnored`.
#[derive(Clone, Default)]
pub struct PatternsAndIgnored {
    pub directories_outside_workspace: Vec<RootedDirectoryPath>,
    pub patterns_inside_workspace: Vec<String>,
    pub ignored: FxHashSet<RootedDirectoryPath>,
}

/// `toFileSystemWatcherKey` produces a deduplication key for a file system
/// watcher.
///
/// Note: this key is a simple string concatenation of the base and pattern,
/// so structurally different watchers (Pattern vs RelativePattern, URI vs
/// WorkspaceFolder) could theoretically collide. In practice, workspace
/// watchers use plain Pattern with filesystem paths while outside-workspace
/// watchers use RelativePattern with file:// URIs, so collisions don't occur.
fn to_file_system_watcher_key(w: &FileSystemWatcher) -> FileSystemWatcherKey {
    let kind = w
        .kind
        .unwrap_or(WatchKind(WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0));
    FileSystemWatcherKey {
        pattern: file_system_watcher_glob_string(w),
        kind,
    }
}

/// `fileSystemWatcherGlobString`.
fn file_system_watcher_glob_string(w: &FileSystemWatcher) -> String {
    if let Some(pattern) = &w.glob_pattern.pattern {
        return pattern.clone();
    }
    if let Some(relative_pattern) = &w.glob_pattern.relative_pattern {
        let mut base = String::new();
        if let Some(uri) = &relative_pattern.base_uri.uri {
            base = uri.as_str().to_string();
        } else if relative_pattern.base_uri.workspace_folder.is_some() {
            panic!("workspace folder-based relative patterns not implemented");
        }
        return format!("{}/{}", base, relative_pattern.pattern);
    }
    String::new()
}

static WATCHER_ID: AtomicU64 = AtomicU64::new(0);

/// `WatchedFiles[T]`.
pub struct WatchedFiles<T> {
    name: String,
    watch_kind: WatchKind,
    has_relative_pattern_capability: bool,
    compute_glob_patterns: std::sync::Arc<dyn Fn(&T) -> PatternsAndIgnored + Send + Sync>,

    state: RwLock<WatchedFilesState>,
    input: RwLock<T>,
    id: AtomicU64,
}

struct WatchedFilesState {
    workspace_watchers: Vec<Arc<FileSystemWatcher>>,
    outside_workspace_watchers: Vec<Arc<FileSystemWatcher>>,
    ignored: FxHashSet<RootedDirectoryPath>,
    /// `computeWatchersOnce` — `None` until `watchers()` has been computed.
    computed: bool,
}

/// `NewWatchedFiles`.
pub fn new_watched_files<T>(
    name: &str,
    watch_kind: WatchKind,
    has_relative_pattern_capability: bool,
    input: T,
    compute_glob_patterns: impl Fn(&T) -> PatternsAndIgnored + Send + Sync + 'static,
) -> Arc<WatchedFiles<T>> {
    Arc::new(WatchedFiles {
        id: AtomicU64::new(WATCHER_ID.fetch_add(1, Ordering::SeqCst) + 1),
        name: name.to_string(),
        watch_kind,
        has_relative_pattern_capability,
        compute_glob_patterns: std::sync::Arc::new(compute_glob_patterns),
        state: RwLock::new(WatchedFilesState {
            workspace_watchers: Vec::new(),
            outside_workspace_watchers: Vec::new(),
            ignored: FxHashSet::default(),
            computed: false,
        }),
        input: RwLock::new(input),
    })
}

/// `NewWatchedFilesForPaths` creates a watcher for exact file paths, routing
/// files outside the workspace through directory-based external watchers so
/// clients can use URI-based RelativePatterns when supported.
pub fn new_watched_files_for_paths(
    name: &str,
    watch_kind: WatchKind,
    has_relative_pattern_capability: bool,
    workspace_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    files: Vec<RootedFilePath>,
) -> Arc<WatchedFiles<Vec<RootedFilePath>>> {
    new_watched_files(
        name,
        watch_kind,
        has_relative_pattern_capability,
        files,
        move |files: &Vec<RootedFilePath>| {
            let mut result = PatternsAndIgnored::default();
            for file_name in files {
                if case_sensitivity
                    .path_key(&workspace_directory.as_path())
                    .contains_path(&case_sensitivity.path_key(&file_name.as_path()))
                {
                    result
                        .patterns_inside_workspace
                        .push(file_name.as_string().to_string());
                } else {
                    result
                        .directories_outside_workspace
                        .push(file_name.directory());
                }
            }
            result
        },
    )
}

/// `Watchers`.
pub struct Watchers {
    pub watcher_id: WatcherId,
    pub workspace_watchers: Vec<Arc<FileSystemWatcher>>,
    pub outside_workspace_watchers: Vec<Arc<FileSystemWatcher>>,
    pub ignored_paths: FxHashSet<RootedDirectoryPath>,
}

impl<T> WatchedFiles<T> {
    /// `(w *WatchedFiles[T]) Watchers`.
    pub fn watchers(&self) -> Watchers {
        {
            let mut state = self.state.write().unwrap();
            if !state.computed {
                let result = {
                    let input = self.input.read().unwrap();
                    (self.compute_glob_patterns)(&input)
                };
                let mut globs = result.patterns_inside_workspace.clone();
                globs.sort();
                globs.dedup();

                // ignored is only used for logging and doesn't affect watcher
                // identity
                state.ignored = result.ignored;
                let mut changed = false;
                if !state
                    .workspace_watchers
                    .iter()
                    .map(|w| w.glob_pattern.pattern.clone().unwrap_or_default())
                    .eq(globs.iter().cloned())
                {
                    let watch_kind = self.watch_kind;
                    state.workspace_watchers = globs
                        .iter()
                        .map(|glob| {
                            Arc::new(FileSystemWatcher {
                                glob_pattern: PatternOrRelativePattern {
                                    pattern: Some(glob.clone()),
                                    relative_pattern: None,
                                },
                                kind: Some(watch_kind),
                            })
                        })
                        .collect();
                    changed = true;
                }
                let mut dirs_outside = result.directories_outside_workspace.clone();
                dirs_outside.sort_by(|a, b| a.compare(b).cmp(&0));
                dirs_outside.dedup();
                if !state
                    .outside_workspace_watchers
                    .iter()
                    .map(|w| file_system_watcher_glob_string(w))
                    .eq(dirs_outside.iter().map(|b| {
                        recursive_directory_glob_pattern(b, self.has_relative_pattern_capability)
                    }))
                {
                    let watch_kind = self.watch_kind;
                    let has_relative = self.has_relative_pattern_capability;
                    state.outside_workspace_watchers = dirs_outside
                        .iter()
                        .map(|dir| {
                            Arc::new(new_recursive_directory_watcher(
                                dir.clone(),
                                watch_kind,
                                has_relative,
                            ))
                        })
                        .collect();
                    changed = true;
                }
                if changed {
                    self.id
                        .store(WATCHER_ID.fetch_add(1, Ordering::SeqCst) + 1, Ordering::SeqCst);
                }
                state.computed = true;
            }
        }

        let state = self.state.read().unwrap();
        Watchers {
            watcher_id: format!(
                "{} watcher {}",
                self.name,
                self.id.load(Ordering::SeqCst)
            ),
            workspace_watchers: state.workspace_watchers.clone(),
            outside_workspace_watchers: state.outside_workspace_watchers.clone(),
            ignored_paths: state.ignored.clone(),
        }
    }

    /// `(w *WatchedFiles[T]) ID`.
    pub fn id(&self) -> WatcherId {
        self.watchers().watcher_id
    }

    /// `(w *WatchedFiles[T]) Name`.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// `(w *WatchedFiles[T]) WatchKind`.
    pub fn watch_kind(&self) -> WatchKind {
        self.watch_kind
    }

    /// `(w *WatchedFiles[T]) Clone` — clones the watcher shell with new input;
    /// the previously computed watchers are carried over (and recomputed on
    /// first `watchers()` call if they differ), matching Go.
    pub fn clone_with(&self, input: T) -> Arc<WatchedFiles<T>> {
        let state = self.state.read().unwrap();
        Arc::new(WatchedFiles {
            name: self.name.clone(),
            watch_kind: self.watch_kind,
            has_relative_pattern_capability: self.has_relative_pattern_capability,
            compute_glob_patterns: self.compute_glob_patterns.clone(),
            state: RwLock::new(WatchedFilesState {
                workspace_watchers: state.workspace_watchers.clone(),
                outside_workspace_watchers: state.outside_workspace_watchers.clone(),
                ignored: state.ignored.clone(),
                // PORT: Go's `computeWatchersOnce` is per-WatchedFiles; the
                // clone starts uncomputed so the new input is processed.
                computed: false,
            }),
            input: RwLock::new(input),
            id: AtomicU64::new(self.id.load(Ordering::SeqCst)),
        })
    }
}

/// `createResolutionLookupGlobMapper`.
pub fn create_resolution_lookup_glob_mapper(
    workspace_directory: RootedDirectoryPath,
    lib_directory: RootedDirectoryPath,
    project_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> impl Fn(Option<&SyncMap<PathKey, RootedFilePath>>) -> PatternsAndIgnored + Send + Sync {
    let workspace_directory_path = case_sensitivity.path_key(&workspace_directory.as_path());
    let project_directory_path = case_sensitivity.path_key(&project_directory.as_path());
    let lib_directory_path = case_sensitivity.path_key(&lib_directory.as_path());

    move |data: Option<&SyncMap<PathKey, RootedFilePath>>| {
        let mut ignored = FxHashSet::default();
        let mut seen_dirs = Set::<PathKey>::new();
        let mut include_workspace = false;
        let mut include_root = false;
        let mut include_lib = false;
        let mut node_modules_directories: FxHashMap<PathKey, RootedDirectoryPath> =
            FxHashMap::default();
        let mut external_directories: FxHashMap<PathKey, RootedDirectoryPath> =
            FxHashMap::default();

        if let Some(data) = data {
            data.range(|path: PathKey, file_name: RootedFilePath| {
                if path.is_dynamic() {
                    return true;
                }
                // Assuming all of the input paths are file paths, we can avoid
                // duplicate work by only taking one file per dir, since their
                // outputs will always be the same.
                if !seen_dirs.add_if_absent(path.parent()) {
                    return true;
                }

                if workspace_directory_path.contains_path(&path) {
                    include_workspace = true;
                } else if project_directory_path.contains_path(&path) {
                    include_root = true;
                } else if lib_directory_path.contains_path(&path) {
                    include_lib = true;
                } else if let Some((_before, node_modules_directory)) =
                    path.split_at_canonical_component("node_modules")
                {
                    let Some((_base, presentation_directory)) = case_sensitivity
                        .split_file_path_at_component(&file_name, "node_modules")
                    else {
                        panic!("canonical node_modules path did not have a presentation component")
                    };
                    node_modules_directories
                        .insert(node_modules_directory, presentation_directory);
                } else {
                    external_directories.insert(path.parent(), file_name.directory());
                }
                true
            });
        }

        let mut globs: Vec<String> = Vec::new();
        if include_workspace {
            globs.push(get_recursive_glob_pattern(&workspace_directory));
        }
        if include_root {
            globs.push(get_recursive_glob_pattern(&project_directory));
        }
        if include_lib {
            globs.push(get_recursive_glob_pattern(&lib_directory));
        }
        if !node_modules_directories.is_empty() {
            let mut node_modules_globs: Vec<String> = node_modules_directories
                .values()
                .map(get_recursive_glob_pattern)
                .collect();
            node_modules_globs.sort();
            globs.extend(node_modules_globs);
        }
        let mut outside_dirs: Vec<RootedDirectoryPath> = Vec::new();
        if !external_directories.is_empty() {
            let dirs: Vec<RootedDirectoryPath> =
                external_directories.values().cloned().collect();
            let (mut external_directory_parents, ignored_external_dirs) =
                tsc_tspath::get_common_parent_directories(
                    &dirs,
                    MIN_WATCH_LOCATION_DEPTH,
                    get_path_components_for_watching,
                    case_sensitivity,
                );
            external_directory_parents.sort();
            ignored = ignored_external_dirs;
            outside_dirs = external_directory_parents;
        }

        PatternsAndIgnored {
            directories_outside_workspace: outside_dirs,
            patterns_inside_workspace: globs,
            ignored,
        }
    }
}

/// `getTypingsLocationsGlobs`.
pub fn get_typings_locations_globs(
    typings_files: &[RootedPath],
    typings_location: &RootedDirectoryPath,
    workspace_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> PatternsAndIgnored {
    let mut include_typings_location = false;
    let mut include_workspace = false;
    let mut external_directories: FxHashMap<PathKey, RootedDirectoryPath> = FxHashMap::default();
    let mut globs: FxHashMap<PathKey, String> = FxHashMap::default();
    for file_name in typings_files {
        if case_sensitivity.contains_path(typings_location, file_name) {
            include_typings_location = true;
        } else if !case_sensitivity.contains_path(workspace_directory, file_name) {
            let directory = file_name.directory();
            external_directories
                .insert(case_sensitivity.path_key(&directory.as_path()), directory);
        } else {
            include_workspace = true;
        }
    }
    let dirs: Vec<RootedDirectoryPath> = external_directories.values().cloned().collect();
    let (mut external_directory_parents, ignored) = tsc_tspath::get_common_parent_directories(
        &dirs,
        MIN_WATCH_LOCATION_DEPTH,
        get_path_components_for_watching,
        case_sensitivity,
    );

    external_directory_parents.sort();
    if include_workspace {
        globs.insert(
            case_sensitivity.path_key(&workspace_directory.as_path()),
            get_recursive_glob_pattern(workspace_directory),
        );
    }
    if include_typings_location {
        globs.insert(
            case_sensitivity.path_key(&typings_location.as_path()),
            get_recursive_glob_pattern(typings_location),
        );
    }
    PatternsAndIgnored {
        directories_outside_workspace: external_directory_parents,
        patterns_inside_workspace: globs.into_values().collect(),
        ignored,
    }
}

/// `getPathComponentsForWatching`.
pub fn get_path_components_for_watching(path: &RootedDirectoryPath) -> Vec<String> {
    let components = path.components();
    let root_length = perceived_os_root_length_for_watching(&components);
    if root_length <= 1 {
        return components;
    }
    let new_root = tsc_tspath::combine_paths(
        &components[0],
        &components[1..root_length]
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
    );
    let mut result = vec![new_root];
    result.extend(components[root_length..].iter().cloned());
    result
}

/// `perceivedOsRootLengthForWatching`.
fn perceived_os_root_length_for_watching(path_components: &[String]) -> usize {
    let length = path_components.len();
    if length <= 1 {
        return length;
    }
    if path_components[0].starts_with("//") {
        // Group UNC roots (//server/share) into a single component
        return 2;
    }
    let bytes = path_components[0].as_bytes();
    if path_components[0].len() == 3
        && tsc_tspath::is_volume_character(bytes[0])
        && bytes[1] == b':'
        && bytes[2] == b'/'
    {
        // Windows-style volume
        if path_components[1].eq_ignore_ascii_case("users") {
            // Group C:/Users/username into a single component
            return 3.min(length);
        }
        return 1;
    }
    if path_components[1] == "home" {
        // Group /home/username into a single component
        return 3.min(length);
    }
    1
}

/// `getRecursiveGlobPattern`.
pub fn get_recursive_glob_pattern(directory: &RootedDirectoryPath) -> String {
    format!(
        "{}/**/*",
        tsc_tspath::remove_trailing_directory_separator(directory.as_string())
    )
}

/// `recursiveDirectoryGlobPattern` returns the string form of a recursive
/// watcher for the given directory that would be produced by
/// `newRecursiveDirectoryWatcher`.
fn recursive_directory_glob_pattern(
    directory: &RootedDirectoryPath,
    use_relative_pattern: bool,
) -> String {
    if use_relative_pattern {
        return format!(
            "{}/**/*",
            tsc_lsconv::file_name_to_document_uri(&tsc_tspath::rooted_file_path_from_path(
                directory.as_path()
            ))
            .as_str()
        );
    }
    get_recursive_glob_pattern(directory)
}

/// `newRecursiveDirectoryWatcher` creates a FileSystemWatcher for
/// recursively watching a directory. When useRelativePattern is true, a
/// RelativePattern with a file:// base URI is used; otherwise a plain glob
/// Pattern is used.
pub fn new_recursive_directory_watcher(
    directory: RootedDirectoryPath,
    kind: WatchKind,
    use_relative_pattern: bool,
) -> FileSystemWatcher {
    if use_relative_pattern {
        let base_uri = URI(
            tsc_lsconv::file_name_to_document_uri(&tsc_tspath::rooted_file_path_from_path(
                directory.as_path(),
            ))
            .as_str()
            .to_string(),
        );
        return FileSystemWatcher {
            glob_pattern: PatternOrRelativePattern {
                pattern: None,
                relative_pattern: Some(RelativePattern {
                    base_uri: WorkspaceFolderOrURI {
                        workspace_folder: None,
                        uri: Some(base_uri),
                    },
                    pattern: "**/*".to_string(),
                }),
            },
            kind: Some(kind),
        };
    }
    FileSystemWatcher {
        glob_pattern: PatternOrRelativePattern {
            pattern: Some(get_recursive_glob_pattern(&directory)),
            relative_pattern: None,
        },
        kind: Some(kind),
    }
}
