// Ported from tsc/internal/execute/tsctests/mock_watch_backend.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go's `sync.Mutex` + `Dirs` map become `Mutex<FxHashMap>`; `MockWatch`
//   is `Arc`-shared between the map and the returned closers (`closed` is
//   `AtomicBool`), and the `io.Closer` slot is a [`MockWatchHandle`]
//   (`watchmanager::WatchHandle`).
// - `DirectoryExists`/`CaseSensitivity` are pub fields assigned after
//   construction in Go; the port makes them setters on `Mutex`/plain fields
//   set inside `new_test_sys` (still before any `WatchDirectories` call).
// - `fmt.Errorf` on a missing directory becomes `fswatch::Error::Message`.
// - `path.Dir` is `path_dir` — inputs are canonical rooted slash paths, so
//   the last-slash prefix (already clean) suffices; root collapses to "/".

use std::fmt::Write as _;
use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;
use tsc_fswatch as fswatch;
use tsc_testutil::fsbaselineutil::FileChange;
use tsc_tspath::{self as tspath, CaseSensitivity, RootedDirectoryPath, RootedPath};
use tsc_watchmanager::{
    WatchBackend, WatchCallback, WatchDirectoryRequest, WatchEvent, WatchHandle, WatchIgnore,
};

/// `func(tspath.RootedDirectoryPath) bool` — `DirectoryExists` field.
pub type DirectoryExistsFn = Box<dyn Fn(&RootedDirectoryPath) -> bool + Send + Sync>;

/// `MockWatchBackend` implements `watchmanager.WatchBackend` for testing. It
/// records all `watch_directories` calls so tests can verify that the correct
/// watches are registered. Events can be delivered through `send_events`,
/// which routes them only through watches whose paths match, enforcing that
/// tests fail if the wrong watches are set up.
pub struct MockWatchBackend {
    dirs: Mutex<FxHashMap<RootedDirectoryPath, Arc<MockWatch>>>,
    /// `DirectoryExists` — if set, `watch_directories` fails for
    /// non-existent dirs.
    directory_exists: Mutex<Option<DirectoryExistsFn>>,
    case_sensitivity: Mutex<CaseSensitivity>,
}

/// `NewMockWatchBackend` creates a ready-to-use mock backend.
pub fn new_mock_watch_backend() -> Arc<MockWatchBackend> {
    Arc::new(MockWatchBackend {
        dirs: Mutex::new(FxHashMap::default()),
        directory_exists: Mutex::new(None),
        case_sensitivity: Mutex::new(CaseSensitivity::default()),
    })
}

impl MockWatchBackend {
    /// `NewMockWatchBackend` — inherent alias for [`new_mock_watch_backend`].
    pub fn new() -> Arc<MockWatchBackend> {
        new_mock_watch_backend()
    }

    /// `m.DirectoryExists = f` (set during `new_test_sys` construction).
    pub fn set_directory_exists(
        &self,
        f: impl Fn(&RootedDirectoryPath) -> bool + Send + Sync + 'static,
    ) {
        *self.directory_exists.lock().unwrap_or_else(|e| e.into_inner()) = Some(Box::new(f));
    }

    /// `m.CaseSensitivity = c`.
    pub fn set_case_sensitivity(&self, case_sensitivity: CaseSensitivity) {
        *self.case_sensitivity.lock().unwrap_or_else(|e| e.into_inner()) = case_sensitivity;
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        *self.case_sensitivity.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// `HasWatches` reports whether any watches have been registered.
    pub fn has_watches(&self) -> bool {
        !self.dirs.lock().unwrap_or_else(|e| e.into_inner()).is_empty()
    }

    /// `SendEvents` routes events through the registered watch callbacks
    /// that match each event's path. Directory watches match if the event
    /// path is a child (or recursive descendant) of the watched directory.
    /// Events that match no watch are silently dropped — this is by design
    /// so that tests fail when the production code doesn't register the
    /// needed watches.
    pub fn send_events(&self, events: Vec<fswatch::Event>) {
        // Snapshot callbacks under the lock, then invoke outside the lock
        // to avoid deadlock if the callback re-enters the mock.
        let case_sensitivity = self.case_sensitivity();
        let mut targets: FxHashMap<*const MockWatch, (WatchCallback, Vec<WatchEvent>)> =
            FxHashMap::default();
        {
            let dirs = self.dirs.lock().unwrap_or_else(|e| e.into_inner());
            for e in &events {
                // Check directory watches.
                for w in dirs.values() {
                    if w.closed.load(Ordering::SeqCst) {
                        continue;
                    }
                    let event_path = tspath::to_rooted_path(&e.path, &w.path);
                    if let Some(ignore) = &w.ignore {
                        if ignore(&event_path) {
                            continue;
                        }
                    }
                    if !path_is_under(&event_path, &w.path, w.recursive, case_sensitivity) {
                        continue;
                    }
                    targets
                        .entry(Arc::as_ptr(w))
                        .or_insert_with(|| (w.callback.clone(), Vec::new()))
                        .1
                        .push(WatchEvent {
                            path: event_path,
                            kind: e.kind,
                        });
                }
            }
        }

        for (_, (cb, events)) in targets {
            cb(events, None);
        }
    }

    /// `SendOverflow` simulates a kernel event-queue overflow by invoking
    /// every active watch callback with `fswatch::ERR_OVERFLOW`. The watch
    /// manager treats this as a signal that events were dropped and a full
    /// rebuild is required.
    pub fn send_overflow(&self) {
        let cbs: Vec<WatchCallback> = self
            .dirs
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .values()
            .filter(|w| !w.closed.load(Ordering::SeqCst))
            .map(|w| w.callback.clone())
            .collect();
        for cb in cbs {
            cb(Vec::new(), Some(fswatch::ERR_OVERFLOW));
        }
    }

    /// `SendChangedPaths` converts a list of file changes into fswatch
    /// events with appropriate event kinds and routes them through
    /// registered watches via `send_events`. For new/modified files, it also
    /// emits update events for their parent directories, simulating how
    /// real filesystem watchers report directory events.
    pub fn send_changed_paths(&self, changes: Vec<FileChange>) {
        let mut events = Vec::with_capacity(changes.len() * 2);
        let mut seen_dirs: FxHashMap<String, ()> = FxHashMap::default();
        for c in &changes {
            let kind = if c.deleted {
                fswatch::EventKind::Delete
            } else {
                fswatch::EventKind::Update
            };
            events.push(fswatch::Event::new(kind, c.path.clone()));
            // Emit update events for parent directories of changed files.
            // Real filesystem watchers deliver events to non-recursive watches
            // when a child directory is created, which the mock must replicate.
            let mut dir = path_dir(&c.path);
            while !dir.is_empty() && dir != "/" && dir != "." {
                if seen_dirs.insert(dir.to_string(), ()).is_some() {
                    break;
                }
                events.push(fswatch::Event::new(fswatch::EventKind::Update, dir.to_string()));
                let parent = path_dir(dir);
                if parent == dir {
                    break;
                }
                dir = parent;
            }
        }
        self.send_events(events);
    }

    /// `WatchState` returns a deterministic, human-readable summary of all
    /// active watches. This is intended to be included in test baselines
    /// so that watch registration correctness is verified via snapshot diffs.
    pub fn watch_state(&self) -> String {
        let dirs = self.dirs.lock().unwrap_or_else(|e| e.into_inner());

        let mut b = String::from("Watch Registrations::\n");

        // Directory watches, sorted by path.
        let mut sorted_dirs: Vec<RootedDirectoryPath> = dirs
            .iter()
            .filter(|(_, w)| !w.closed.load(Ordering::SeqCst))
            .map(|(d, _)| d.clone())
            .collect();
        sorted_dirs.sort_by(|a, b| a.compare(b).cmp(&0));

        b.push_str("Directory watches::\n");
        if sorted_dirs.is_empty() {
            b.push_str("  (none)\n");
        }
        for d in &sorted_dirs {
            let w = &dirs[d];
            if w.recursive {
                let _ = writeln!(b, "  {} (recursive)", d.as_string());
            } else {
                let _ = writeln!(b, "  {}", d.as_string());
            }
        }

        b
    }
}

impl WatchBackend for MockWatchBackend {
    /// `WatchDirectories`.
    fn watch_directories(
        &self,
        requests: Vec<WatchDirectoryRequest>,
    ) -> Result<Vec<Box<dyn WatchHandle>>, fswatch::Error> {
        let mut dirs = self.dirs.lock().unwrap_or_else(|e| e.into_inner());
        let directory_exists = self.directory_exists.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(directory_exists) = directory_exists.as_ref() {
            for request in &requests {
                if !directory_exists(&request.dir) {
                    return Err(fswatch::Error::Message(format!(
                        "directory does not exist: {}",
                        request.dir.as_string()
                    )));
                }
            }
        }
        let mut closers: Vec<Box<dyn WatchHandle>> = Vec::with_capacity(requests.len());
        for request in requests {
            let w = Arc::new(MockWatch {
                path: request.dir.clone(),
                callback: request.callback,
                recursive: request.recursive,
                ignore: request.ignore,
                closed: AtomicBool::new(false),
            });
            dirs.insert(request.dir, w.clone());
            closers.push(Box::new(MockWatchHandle(w)));
        }
        Ok(closers)
    }
}

/// `MockWatch` records a single registered watch.
pub struct MockWatch {
    /// `Path`.
    pub path: RootedDirectoryPath,
    /// `Callback`.
    pub callback: WatchCallback,
    /// `Recursive`.
    pub recursive: bool,
    /// `Ignore`.
    pub ignore: Option<WatchIgnore>,
    /// `Closed`.
    pub closed: AtomicBool,
}

/// `MockWatchHandle` — the `io.Closer` returned for a [`MockWatch`]; closing
/// marks the shared watch closed.
pub struct MockWatchHandle(Arc<MockWatch>);

impl WatchHandle for MockWatchHandle {
    /// `(*MockWatch) Close`.
    fn close(&self) {
        self.0.closed.store(true, Ordering::SeqCst);
    }
}

impl MockWatch {
    /// `(*MockWatch) Close` — kept for direct handle-free callers.
    pub fn close(&self) -> io::Result<()> {
        self.closed.store(true, Ordering::SeqCst);
        Ok(())
    }
}

/// `pathIsUnder` reports whether `event_path` is inside `dir`. If
/// `recursive` is false, only direct children match.
fn path_is_under(
    event_path: &RootedPath,
    dir: &RootedDirectoryPath,
    recursive: bool,
    case_sensitivity: CaseSensitivity,
) -> bool {
    let dir_key = case_sensitivity.path_key(&dir.as_path());
    let event_key = case_sensitivity.path_key(event_path);
    if dir_key == event_key || !dir_key.contains_path(&event_key) {
        return false;
    }
    if recursive {
        return true;
    }
    case_sensitivity.path_key(&event_path.directory().as_path()) == dir_key
}

/// `path.Dir` — for canonical rooted slash paths the last-slash prefix is
/// already clean; "/x" → "/" and "" → ".".
fn path_dir(path: &str) -> &str {
    match path.rfind('/') {
        Some(0) => "/",
        Some(i) => &path[..i],
        None => ".",
    }
}
