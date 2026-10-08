// Ported from tsc/internal/fswatch/inotify_linux.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! The `watcherImpl` backend, implemented on the `notify` crate's
//! `RecommendedWatcher` (inotify on Linux).
//!
//! PORT: Go hand-rolls an inotify fd + poll loop (`inotify_linux.go`). Here
//! `notify::RecommendedWatcher` owns the OS watch set and its own event-loop
//! thread; its `EventHandler` is an `mpsc::Sender` feeding a dispatch thread
//! that routes kernel events into each `DirWatch`'s `EventList`. The event
//! mapping mirrors `handleSubscription`:
//!   - `Create` / `Modify(Name(To))`          → `events.create`
//!   - `Modify(Data)`                         → `events.update`
//!   - `Remove` / `Modify(Name(From))`        → `events.remove`
//!   - `Modify(Name(Both))` (paired rename)   → remove + create
//!   - `EventKind::Other` + `Flag::Rescan`    → `ErrOverflow` (IN_Q_OVERFLOW)
//!   - self-delete/move of a watch root       → remove + `ErrWatchTerminated`
//! `Access` and `Modify(Metadata)` events are dropped: Go's inotify mask has
//! no `IN_ATTRIB`/`IN_OPEN`/`IN_CLOSE_*`, so it never produced them.

use std::path::Path;
use std::sync::Arc;
use std::sync::mpsc::{Receiver, channel};

use notify::event::{ModifyKind, RenameMode};
use notify::{EventKind as NotifyEventKind, RecursiveMode, Watcher as _};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::error::{ERR_OVERFLOW, ERR_WATCH_TERMINATED, Error};
use crate::watcher::{DirWatch, Shared, is_direct_child, is_in_directory_or_self};

/// `Backend` wraps `notify::RecommendedWatcher`. It owns the OS watch set;
/// dropping it stops watching (which never happens — the backend lives in
/// `Shared` for the process lifetime, like Go's lazily-started impl).
pub(crate) struct Backend {
    inner: notify::RecommendedWatcher,
}

impl Backend {
    /// `watcherImpl` construction + `watcherBase.run`: create the notify
    /// watcher and spawn the dispatch thread (Go's `start` goroutine).
    pub(crate) fn start(shared: &Arc<Shared>) -> Result<Backend, Error> {
        // `std::sync::mpsc::Sender` implements `notify::EventHandler`.
        let (tx, rx) = channel::<notify::Result<notify::Event>>();
        let inner = notify::recommended_watcher(tx).map_err(|e| Error::Notify(Arc::new(e)))?;
        let dispatch_shared = Arc::clone(shared);
        std::thread::Builder::new()
            .name("tsc-fswatch dispatch".to_owned())
            .spawn(move || dispatch_loop(dispatch_shared, rx))
            .map_err(|e| Error::Io(Arc::new(e)))?;
        Ok(Backend { inner })
    }

    /// `subscribe`/`closeWatch` equivalents.
    pub(crate) fn watch(&mut self, path: &Path, mode: RecursiveMode) -> Result<(), Error> {
        self.inner
            .watch(path, mode)
            .map_err(|e| Error::Notify(Arc::new(e)))
    }

    pub(crate) fn unwatch(&mut self, path: &Path) -> Result<(), Error> {
        self.inner
            .unwatch(path)
            .map_err(|e| Error::Notify(Arc::new(e)))
    }
}

/// The dispatch thread body — Go's `handleEvents`/`handleEvent` loop.
fn dispatch_loop(shared: Arc<Shared>, rx: Receiver<notify::Result<notify::Event>>) {
    while let Ok(result) = rx.recv() {
        match result {
            Ok(event) => handle_notify_event(&shared, event),
            Err(err) => handle_notify_error(&shared, err),
        }
    }
}

/// The dirWatches whose subscriptions cover `physical_path`: any ancestor
/// (or self) for recursive watches, self or parent for non-recursive ones.
fn covering_dir_watches(shared: &Shared, physical_path: &str) -> Vec<Arc<DirWatch>> {
    shared
        .state
        .lock()
        .unwrap()
        .dir_watches
        .values()
        .filter(|dw| {
            is_in_directory_or_self(&dw.physical_dir, physical_path)
                && (dw.recursive
                    || physical_path == dw.physical_dir
                    || is_direct_child(&dw.physical_dir, physical_path))
        })
        .cloned()
        .collect()
}

/// All live dirWatches — the equivalent of Go iterating `b.subscriptions`.
fn all_dir_watches(shared: &Shared) -> Vec<Arc<DirWatch>> {
    shared
        .state
        .lock()
        .unwrap()
        .dir_watches
        .values()
        .cloned()
        .collect()
}

/// Record `f` for every dirWatch covering `path`, returning the touched set.
fn for_each_covering(
    shared: &Shared,
    path: &Path,
    mut f: impl FnMut(&DirWatch, &str),
    touched: &mut FxHashMap<String, Arc<DirWatch>>,
) {
    let physical = path.to_string_lossy();
    for dw in covering_dir_watches(shared, &physical) {
        let display = dw.display_path(&physical);
        f(&dw, &display);
        touched.entry(dw.debounce_key.clone()).or_insert(dw);
    }
}

/// After walking event paths, wake each touched dirWatch once (`w.notify()`
/// per touched watcher at the end of `handleEvents`).
fn notify_touched(touched: FxHashMap<String, Arc<DirWatch>>) {
    for dw in touched.into_values() {
        dw.notify();
    }
}

/// `ErrWatchTerminated` as produced by Go's inotify self-delete path:
/// `fmt.Errorf("%w: watched directory removed", ErrWatchTerminated)`.
fn watch_terminated_removed() -> Error {
    Error::wrapped(
        "fswatch: watch terminated: watched directory removed",
        ERR_WATCH_TERMINATED,
    )
}

/// Drop `watched_paths` entries at or under `physical` — mirrors
/// `remove_watch_by_event`/`closeWatch` dropping subscriptions for removed
/// subtrees (notify removes the inotify watches itself).
fn prune_watched_paths(shared: &Shared, physical: &str) {
    shared
        .state
        .lock()
        .unwrap()
        .watched_paths
        .retain(|p| !is_in_directory_or_self(physical, &p.to_string_lossy()));
}

/// If `path` is a directory inside a recursive watch, ensure notify is
/// watching it (`IN_CREATE|IN_ISDIR` → `walkDir` + `watchDir` in Go). This
/// also covers the case where `notify`'s own auto-add is disabled because
/// the same inotify path is shared between a recursive and a non-recursive
/// subscription (`notify` records one `is_recursive` flag per path).
fn ensure_recursive_watch(
    shared: &Shared,
    path: &Path,
    touched: &mut FxHashMap<String, Arc<DirWatch>>,
) {
    let needs_watch = {
        let state = shared.state.lock().unwrap();
        !state.watched_paths.contains(path)
            && state.dir_watches.values().any(|dw| {
                dw.recursive && is_in_directory_or_self(&dw.physical_dir, &path.to_string_lossy())
            })
    };
    if !needs_watch {
        return;
    }
    let is_dir = std::fs::metadata(path).map(|m| m.is_dir()).unwrap_or(false);
    if !is_dir {
        return;
    }
    let armed = {
        let mut state = shared.state.lock().unwrap();
        // Re-check under the lock.
        if state.watched_paths.contains(path) {
            false
        } else if let Some(backend) = state.backend.as_mut() {
            // Errors are swallowed like Go's `_ = walkDir(...)` / `_, _ =
            // b.watchDir(...)` on the runtime create path; a dropped watch
            // shows up as missed events only, same as in Go.
            if backend.watch(path, RecursiveMode::Recursive).is_ok() {
                state.watched_paths.insert(path.to_path_buf());
                true
            } else {
                false
            }
        } else {
            false
        }
    };
    if armed {
        scan_subtree_creates(shared, path, touched);
    }
}

/// PORT: `notify` arms watches for a newly-created/moved-in directory's
/// subtree without synthesizing events for content already inside it —
/// `add_watch`'s `WalkDir` only installs inotify watches. Anything written
/// between the directory's create event and the watch landing would be
/// silently dropped. Go's inotify backend has the same gap (it arms
/// watches inline from its event loop, so the window is just narrower).
/// Scan the subtree after arming and emit `create` for every existing
/// entry; entries created after the watch lands arrive as real inotify
/// events, and the overlap is coalesced by the `EventList`.
fn scan_subtree_creates(
    shared: &Shared,
    root: &Path,
    touched: &mut FxHashMap<String, Arc<DirWatch>>,
) {
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            for_each_covering(
                shared,
                &path,
                |dw, display| dw.events.create(display),
                touched,
            );
            // `file_type` is the entry's own type (no symlink traversal),
            // like Go's `godirwalk` Lstat-based `walkDir`.
            if entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
                stack.push(path);
            }
        }
    }
}

/// `handleEvents`/`handleSubscription` — route one `notify` event.
fn handle_notify_event(shared: &Arc<Shared>, event: notify::Event) {
    // IN_Q_OVERFLOW → `EventKind::Other` + `Flag::Rescan` (notify maps the
    // kernel's queue overflow to a rescan flag rather than an error).
    if event.need_rescan() {
        for dw in all_dir_watches(shared) {
            dw.events.set_error(ERR_OVERFLOW);
            dw.notify();
        }
        return;
    }

    let mut touched: FxHashMap<String, Arc<DirWatch>> = FxHashMap::default();

    match event.kind {
        NotifyEventKind::Create(_) => {
            for path in &event.paths {
                for_each_covering(
                    shared,
                    path,
                    |dw, display| dw.events.create(display),
                    &mut touched,
                );
                // IN_CREATE|IN_ISDIR → recursive walk+watch.
                ensure_recursive_watch(shared, path, &mut touched);
            }
        }
        NotifyEventKind::Remove(_) => {
            for path in &event.paths {
                let physical = path.to_string_lossy().into_owned();
                for_each_covering(
                    shared,
                    path,
                    |dw, display| {
                        dw.events.remove(display);
                        // IN_DELETE_SELF on the watch root.
                        if physical == dw.physical_dir {
                            dw.events.set_error(watch_terminated_removed());
                        }
                    },
                    &mut touched,
                );
                prune_watched_paths(shared, &physical);
            }
        }
        NotifyEventKind::Modify(kind) => match kind {
            ModifyKind::Data(_) | ModifyKind::Any | ModifyKind::Other => {
                // IN_MODIFY. (notify's inotify backend only ever emits
                // `Data(Any)`; `Any`/`Other` are defensive mappings — no Go
                // inotify mask produces them.)
                for path in &event.paths {
                    for_each_covering(
                        shared,
                        path,
                        |dw, display| dw.events.update(display),
                        &mut touched,
                    );
                }
            }
            // IN_ATTRIB has no Go counterpart — the Go inotify mask does not
            // subscribe to it.
            ModifyKind::Metadata(_) => {}
            ModifyKind::Name(mode) => match mode {
                // IN_MOVED_FROM (and IN_MOVE_SELF on a watch root).
                RenameMode::From => {
                    for path in &event.paths {
                        let physical = path.to_string_lossy().into_owned();
                        for_each_covering(
                            shared,
                            path,
                            |dw, display| {
                                dw.events.remove(display);
                                if physical == dw.physical_dir {
                                    dw.events.set_error(watch_terminated_removed());
                                }
                            },
                            &mut touched,
                        );
                        prune_watched_paths(shared, &physical);
                    }
                }
                // IN_MOVED_TO.
                RenameMode::To => {
                    for path in &event.paths {
                        for_each_covering(
                            shared,
                            path,
                            |dw, display| dw.events.create(display),
                            &mut touched,
                        );
                        ensure_recursive_watch(shared, path, &mut touched);
                    }
                }
                // A paired rename: paths are [from, to]. notify emits the
                // `From`/`To` events in addition to `Both`, and the event
                // list's coalescing makes the double application harmless —
                // handling Both covers the cross-watch-move case too.
                RenameMode::Both => {
                    if let Some(from) = event.paths.first() {
                        let physical = from.to_string_lossy().into_owned();
                        for_each_covering(
                            shared,
                            from,
                            |dw, display| {
                                dw.events.remove(display);
                                if physical == dw.physical_dir {
                                    dw.events.set_error(watch_terminated_removed());
                                }
                            },
                            &mut touched,
                        );
                        prune_watched_paths(shared, &physical);
                    }
                    if let Some(to) = event.paths.get(1) {
                        for_each_covering(
                            shared,
                            to,
                            |dw, display| dw.events.create(display),
                            &mut touched,
                        );
                        ensure_recursive_watch(shared, to, &mut touched);
                    }
                }
                RenameMode::Any | RenameMode::Other => {}
            },
        },
        // IN_OPEN/IN_CLOSE_* have no Go counterpart — not subscribed.
        NotifyEventKind::Access(_) | NotifyEventKind::Any | NotifyEventKind::Other => {}
    }

    notify_touched(touched);
}

/// Errors arriving on the event stream: inotify read failures and
/// `MaxFilesWatch` (ENOSPC) from `notify`'s runtime auto-watch.
/// PORT: Go's inotify backend returns subscribe errors synchronously and
/// swallows runtime add failures; read-loop failure kills `start` and reaches
/// subscribers via `notifyError`. Here the error is routed into the pending
/// batch of every dirWatch covering the error's paths (or every dirWatch
/// when the error is pathless), surfaced like `ErrOverflow`.
fn handle_notify_error(shared: &Shared, err: notify::Error) {
    let targets: Vec<Arc<DirWatch>> = {
        if err.paths.is_empty() {
            all_dir_watches(shared)
        } else {
            let mut seen: FxHashSet<String> = FxHashSet::default();
            let mut out = Vec::new();
            for path in &err.paths {
                for dw in covering_dir_watches(shared, &path.to_string_lossy()) {
                    if seen.insert(dw.debounce_key.clone()) {
                        out.push(dw);
                    }
                }
            }
            out
        }
    };
    let err = Arc::new(err);
    for dw in targets {
        dw.events.set_error(Error::Notify(Arc::clone(&err)));
        dw.notify();
    }
}
