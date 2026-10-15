// Ported from tsc/internal/lsp/lspwatcher/lspwatcher.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `lspwatcher` implements an in-process file watcher used as a drop-in
// replacement for LSP-based file watching when the client does not support
// dynamic registration of file watchers.
//
// PORT notes:
// - `watcherBackend` interface → [`WatcherBackend`] trait; `io.Closer`
//   subscriptions → `fswatch::Watch` (`close`, Drop == Close).
// - Go's `*Watcher`/`*watch` back-references captured by backend callbacks
//   become `Weak` — Go's GC collects those cycles (watcher → watch →
//   subscription → callback → watcher); here a dead watcher/watch simply
//   drops late events.
// - `sync.Mutex` fields → `Mutex<...Inner>` structs; `time.AfterFunc` →
//   [`after_func`], a timer thread with an `AtomicBool` stop flag.
// - `error` returns → `fswatch::Error` (`Error::Message` stands in for
//   `errors.New`/`fmt.Errorf` strings; backend errors propagate verbatim).
// - `[]*lsproto.FileEvent` → `&[FileEvent]`; `%q`/`%v` log verbs → `{:?}`/`{}`
//   (log output is diagnostic, not spec-constrained).

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, Weak};
use std::time::Duration;

use tsc_fswatch as fswatch;
use tsc_lsconv as lsconv;
use tsc_lsproto::{DocumentUri, FileChangeType, FileEvent, FileSystemWatcher, WatchKind};
use tsc_project_logging::Logger;
use tsc_tspath as tspath;
use tsc_tspath::{RootedDirectoryPath, RootedPath};
use tsc_vfs as vfs;
use tsc_vfs::Vfs;

/// `throttleWindow` mirrors VS Code's parcel watcher integration: give the
/// first batch a short grace window so adjacent filesystem bursts coalesce.
const THROTTLE_WINDOW: Duration = Duration::from_millis(75);

/// `watcherBackend` — the seam between [`Watcher`] and an `fswatch`
/// implementation.
trait WatcherBackend: Send + Sync {
    /// `WatchDirectory`.
    fn watch_directory(
        &self,
        dir: &RootedDirectoryPath,
        f: WatchCallback,
        opts: Vec<fswatch::WatchOption>,
    ) -> Result<fswatch::Watch, fswatch::Error>;
}

/// `watchEvent`.
struct WatchEvent {
    path: RootedPath,
    kind: fswatch::EventKind,
}

/// `watchCallback`.
type WatchCallback = Arc<dyn Fn(Vec<WatchEvent>, Option<fswatch::Error>) + Send + Sync>;

/// `defaultWatcherBackend`.
struct DefaultWatcherBackend {
    watcher: Arc<dyn fswatch::Watcher>,
}

impl WatcherBackend for DefaultWatcherBackend {
    fn watch_directory(
        &self,
        dir: &RootedDirectoryPath,
        f: WatchCallback,
        opts: Vec<fswatch::WatchOption>,
    ) -> Result<fswatch::Watch, fswatch::Error> {
        let callback: fswatch::WatchCallback = Arc::new(move |events, err| {
            let typed_events: Vec<WatchEvent> = events
                .into_iter()
                .map(|event| WatchEvent {
                    path: tspath::rooted_path_from_absolute(&event.path),
                    kind: event.kind,
                })
                .collect();
            f(typed_events, err);
        });
        self.watcher
            .watch_directory(dir.as_string(), callback, opts)
    }
}

/// `func(changes []*lsproto.FileEvent)`.
type OnChangesFn = Arc<dyn Fn(&[FileEvent]) + Send + Sync>;

/// `Watcher` manages a set of file system subscriptions identified by
/// WatcherID strings (matching the LSP server's `project.WatcherID` type).
/// Events are delivered to `on_changes` in batches as `FileEvent`s, shaped
/// exactly like a `workspace/didChangeWatchedFiles` notification.
pub struct Watcher {
    fs: Arc<dyn Vfs>,
    backend: Arc<dyn WatcherBackend>,
    on_changes: OnChangesFn,
    logger: Arc<dyn Logger>,

    /// Weak self-reference captured by backend callbacks and the flush
    /// timer — Go's closures hold `*Watcher` strongly, but that would be an
    /// Arc cycle here; a dead watcher drops late events.
    me: Weak<Watcher>,

    /// `mu` — guards [`WatcherInner`].
    mu: Mutex<WatcherInner>,
}

/// The `mu`-guarded fields of [`Watcher`].
struct WatcherInner {
    /// `watches` holds the watches associated with each LSP WatcherID. A
    /// single id may map to more than one watch because each
    /// FileSystemWatcher in the registration becomes its own watch
    /// (different roots and kinds).
    watches: HashMap<String, Vec<Arc<Watch>>>,
    closed: bool,

    /// Pending batch state, protected by `mu`. `None` is Go's nil map.
    pending: Option<HashMap<String, FileEvent>>,
    /// `flushTimer`.
    flush_timer: Option<FlushTimer>,
}

/// `watch` represents one FileSystemWatcher from the LSP registration.
///
/// The directory the session asks to watch may not exist yet (common in
/// granular mode, where each probed-but-missing package directory becomes a
/// watch) or may be deleted while watched. To honor the watch across those
/// transitions, a watch maintains either:
///
///   - a "target" subscription rooted directly at the requested directory,
///     once it exists, or
///   - an "ancestor" subscription on the nearest existing ancestor
///     (non-recursive), used to detect the requested directory — or an
///     intermediate path component — being created, after which the watch
///     descends toward and eventually promotes to the target.
///
/// When the target materializes, synthetic create events are emitted for it
/// (and, depending on whether the watch is recursive, its immediate children
/// or its whole subtree) so the session re-resolves files that appeared in
/// the gap before the real subscription was installed.
///
/// All path fields are tspath-style (forward-slash) absolute paths.
struct Watch {
    /// `watcher` — back-reference to the owning `Watcher` (weak for the
    /// same cycle reason as [`Watcher::me`]).
    watcher: Weak<Watcher>,
    /// `requestedDirectory` — directory requested by the LSP layer
    /// (possibly a symlink).
    requested_directory: RootedDirectoryPath,
    kind: WatchKind,
    /// `recursive` — whether the target subscription should be recursive.
    recursive: bool,

    /// `mu` — guards [`WatchInner`].
    inner: Mutex<WatchInner>,
}

/// The `mu`-guarded fields of [`Watch`].
#[derive(Default)]
struct WatchInner {
    /// `subscription` — current subscription (target or ancestor); `None`
    /// if none.
    subscription: Option<fswatch::Watch>,
    /// `watchedDirectory` — canonicalized directory `subscription` is
    /// rooted at. `""` when there is no subscription.
    watched_directory: RootedDirectoryPath,
    /// `watchingTarget` — whether `subscription` is rooted at the target
    /// directory.
    watching_target: bool,
    closed: bool,
}

impl Watcher {
    /// `New` constructs a `Watcher` backed by fswatch's platform-default
    /// watcher implementation.
    pub fn new(fs: Arc<dyn Vfs>, on_changes: OnChangesFn, logger: Arc<dyn Logger>) -> Arc<Watcher> {
        Self::new_with_fs_watcher(fs, fswatch::default(), on_changes, logger)
    }

    /// `NewWithFSWatcher` constructs a `Watcher` backed by the provided
    /// `fswatch::Watcher`. Use this to select a specific backend (e.g.
    /// `fswatch::kqueue()`) instead of the platform default.
    pub fn new_with_fs_watcher(
        fs: Arc<dyn Vfs>,
        watcher: Arc<dyn fswatch::Watcher>,
        on_changes: OnChangesFn,
        logger: Arc<dyn Logger>,
    ) -> Arc<Watcher> {
        Self::new_with_backend(
            fs,
            Arc::new(DefaultWatcherBackend { watcher }),
            on_changes,
            logger,
        )
    }

    /// `newWithBackend`.
    fn new_with_backend(
        fs: Arc<dyn Vfs>,
        backend: Arc<dyn WatcherBackend>,
        on_changes: OnChangesFn,
        logger: Arc<dyn Logger>,
    ) -> Arc<Watcher> {
        Arc::new_cyclic(|me| Watcher {
            fs,
            backend,
            on_changes,
            logger,
            me: me.clone(),
            mu: Mutex::new(WatcherInner {
                watches: HashMap::new(),
                closed: false,
                pending: None,
                flush_timer: None,
            }),
        })
    }

    /// `WatchFiles` subscribes to each FileSystemWatcher under the given id.
    ///
    /// A watcher whose directory does not exist yet is not an error: an
    /// ancestor watch is installed on the nearest existing ancestor and the
    /// subscription is reported as successful, so the session's notion of
    /// "this watcher is alive" stays true for the subscription's whole
    /// lifetime. Only a genuine backend failure (e.g. resource exhaustion
    /// while watching an existing directory) causes `watch_files` to roll
    /// back the whole id and return an error, so the session's
    /// pending/retry path re-registers it on the next reevaluation.
    pub fn watch_files(
        &self,
        id: &str,
        file_system_watchers: &[FileSystemWatcher],
    ) -> Result<(), fswatch::Error> {
        {
            let mut inner = self.mu.lock().unwrap();
            if inner.closed {
                return Err(fswatch::Error::Message("lspwatcher: closed".to_string()));
            }
            if inner.watches.contains_key(id) {
                return Err(fswatch::Error::Message(format!(
                    "lspwatcher: watcher {id:?} already exists"
                )));
            }
            // Mark the id as existing before installing any watches so a
            // concurrent watch_files for the same id is rejected above.
            inner.watches.insert(id.to_string(), Vec::new());
        }

        let mut failed = false;
        for file_system_watcher in file_system_watchers {
            let (directory, ok) = watch_root(file_system_watcher);
            if !ok || directory.as_string().is_empty() {
                self.logger.logf(format_args!(
                    "lspwatcher: skipping watcher {id:?}: unrecognized pattern {:?}",
                    watch_pattern_string(file_system_watcher)
                ));
                continue;
            }
            let new_watch = Arc::new(Watch {
                watcher: self.me.clone(),
                requested_directory: directory.clone(),
                kind: effective_kind(file_system_watcher),
                recursive: is_recursive_glob(file_system_watcher),
                inner: Mutex::new(WatchInner::default()),
            });
            if let Err(err) = new_watch.reconcile(false /* emit_synthetic */) {
                self.logger.logf(format_args!(
                    "lspwatcher: failed to register watcher {id:?} for {:?}: {err}",
                    directory.as_string()
                ));
                new_watch.close();
                failed = true;
                break;
            }
            let mut inner = self.mu.lock().unwrap();
            if inner.closed {
                drop(inner);
                new_watch.close();
                return Err(fswatch::Error::Message("lspwatcher: closed".to_string()));
            }
            // `w.watches[id] = append(w.watches[id], newWatch)` — `entry`
            // also covers a concurrent unwatch_files having removed the id.
            inner
                .watches
                .entry(id.to_string())
                .or_default()
                .push(new_watch);
        }

        if failed {
            // Roll back the whole id so the session's retry (MarkPending) can
            // cleanly re-register it. The session treats an id as a single
            // unit.
            let _ = self.unwatch_files(id);
            return Err(fswatch::Error::Message(format!(
                "lspwatcher: failed to register one or more watchers for {id:?}"
            )));
        }
        Ok(())
    }

    /// `UnwatchFiles` tears down all subscriptions associated with id.
    pub fn unwatch_files(&self, id: &str) -> Result<(), fswatch::Error> {
        let watches = {
            let mut inner = self.mu.lock().unwrap();
            let Some(watches) = inner.watches.remove(id) else {
                return Err(fswatch::Error::Message(format!(
                    "lspwatcher: no watcher with id {id:?}"
                )));
            };
            watches
        };
        for watch in watches {
            watch.close();
        }
        Ok(())
    }

    /// `Close` removes every subscription. Safe to call multiple times.
    pub fn close(&self) {
        let watches_by_id = {
            let mut inner = self.mu.lock().unwrap();
            if inner.closed {
                return;
            }
            inner.closed = true;
            let watches_by_id = std::mem::take(&mut inner.watches);
            if let Some(flush_timer) = inner.flush_timer.take() {
                flush_timer.stop();
            }
            inner.pending = None;
            watches_by_id
        };
        for watches in watches_by_id.into_values() {
            for watch in watches {
                watch.close();
            }
        }
    }

    /// `forwardEvents` translates fswatch events into LSP file events and
    /// enqueues them for the next debounced flush.
    fn forward_events(&self, kind: WatchKind, events: Vec<WatchEvent>) {
        let mut inner = self.mu.lock().unwrap();
        if inner.closed {
            return;
        }
        if inner.pending.is_none() {
            inner.pending = Some(HashMap::with_capacity(events.len()));
        }
        {
            let pending = inner.pending.as_mut().unwrap();
            for event in events {
                let change_type = match event.kind {
                    fswatch::EventKind::Update => {
                        // fswatch intentionally doesn't distinguish create vs
                        // update. For LSP consumers this is fine: callers
                        // infer create/update from their own cache and both
                        // should invalidate stale state.
                        if kind.0 & (WatchKind::Create.0 | WatchKind::Change.0) == 0 {
                            continue;
                        }
                        FileChangeType::Changed
                    }
                    fswatch::EventKind::Delete => {
                        if kind.0 & WatchKind::Delete.0 == 0 {
                            continue;
                        }
                        FileChangeType::Deleted
                    }
                };

                let uri = lsconv::path_to_document_uri(&event.path);
                pending.insert(
                    uri.0.clone(),
                    FileEvent {
                        uri,
                        type_: change_type,
                    },
                );
            }
        }
        self.schedule_flush_locked(&mut inner);
        drop(inner);
    }

    /// `emitSyntheticCreates` enqueues synthetic create events after a
    /// target watch is (re)installed following a missing→present
    /// transition, so the session re-resolves files that appeared before
    /// the real watch existed. The target directory itself is always
    /// included; for a non-recursive watch its immediate children are
    /// added, and for a recursive watch its whole subtree is walked.
    /// Nothing is emitted if the watch doesn't request create
    /// notifications.
    fn emit_synthetic_creates(
        &self,
        directory: &RootedDirectoryPath,
        kind: WatchKind,
        recursive: bool,
    ) {
        if kind.0 & WatchKind::Create.0 == 0 {
            return;
        }
        let mut paths: Vec<RootedPath> = vec![directory.as_path()];
        if recursive {
            let mut walk_fn = |path: &RootedPath,
                               _entry: Option<&dyn vfs::fs::DirEntry>,
                               err: Option<&vfs::fs::FsError>|
             -> Result<(), vfs::fs::FsError> {
                if err.is_some() {
                    return Ok(());
                }
                if *path == directory.as_path() {
                    return Ok(());
                }
                paths.push(path.clone());
                Ok(())
            };
            let _ = vfs::walk_dir(&self.fs, &directory.as_path(), &mut walk_fn);
        } else {
            let entries = self.fs.get_accessible_entries(directory);
            for name in &entries.files {
                paths.push(directory.resolve_file(name).as_path());
            }
            for name in &entries.directories {
                paths.push(directory.resolve_directory(name).as_path());
            }
        }
        self.enqueue_synthetic_creates(&paths);
    }

    /// `enqueueSyntheticCreates` adds synthetic create events for paths,
    /// without clobbering a more specific event already pending for the
    /// same path (e.g. a real delete).
    fn enqueue_synthetic_creates(&self, paths: &[RootedPath]) {
        let mut inner = self.mu.lock().unwrap();
        if inner.closed {
            return;
        }
        {
            let pending = inner
                .pending
                .get_or_insert_with(|| HashMap::with_capacity(paths.len()));
            for path in paths {
                let uri = lsconv::path_to_document_uri(path);
                if pending.contains_key(uri.as_str()) {
                    continue;
                }
                pending.insert(
                    uri.0.clone(),
                    FileEvent {
                        uri,
                        type_: FileChangeType::Created,
                    },
                );
            }
        }
        self.schedule_flush_locked(&mut inner);
        drop(inner);
    }

    /// `scheduleFlushLocked` arms the debounce flush timer if it isn't
    /// already armed. Callers must hold `mu`.
    fn schedule_flush_locked(&self, inner: &mut WatcherInner) {
        if inner.flush_timer.is_none() {
            let me = self.me.clone();
            inner.flush_timer = Some(after_func(THROTTLE_WINDOW, move || {
                if let Some(watcher) = me.upgrade() {
                    watcher.flush();
                }
            }));
        }
    }

    /// `flush`.
    fn flush(&self) {
        let pending = {
            let mut inner = self.mu.lock().unwrap();
            if inner.closed {
                return;
            }
            inner.flush_timer = None;
            inner.pending.take()
        };

        let Some(pending) = pending else {
            return;
        };
        if pending.is_empty() {
            return;
        }
        let changes: Vec<FileEvent> = pending.into_values().collect();
        (self.on_changes)(&changes);
    }
}

impl Watch {
    /// `close` tears down the watch's current subscription and prevents any
    /// in-flight reconcile from reinstalling one.
    fn close(&self) {
        let subscription = {
            let mut inner = self.inner.lock().unwrap();
            inner.closed = true;
            inner.watched_directory = RootedDirectoryPath::default();
            inner.subscription.take()
        };
        if let Some(subscription) = subscription {
            let _ = subscription.close();
        }
    }

    /// `reconcile` installs or advances this watch toward the target
    /// directory based on the current filesystem state. It is called at
    /// registration, whenever an ancestor watch observes activity, and
    /// after a target watch is terminated by deletion.
    ///
    /// `emit_synthetic_creates` controls whether promoting to the target
    /// emits synthetic create events: false for the initial install when
    /// the target already exists (the session already knows about those
    /// files), true for any missing→present recovery.
    ///
    /// It returns an error only on a genuine backend failure to install a
    /// watch; a missing target directory is handled by installing an
    /// ancestor watch and returns `Ok`.
    fn reconcile(self: &Arc<Self>, mut emit_synthetic_creates: bool) -> Result<(), fswatch::Error> {
        let mut inner = self.inner.lock().unwrap();
        let Some(watcher) = self.watcher.upgrade() else {
            return Ok(());
        };
        loop {
            if inner.closed {
                return Ok(());
            }
            if watcher.fs.directory_exists(&self.requested_directory) {
                if inner.watching_target && inner.subscription.is_some() {
                    return Ok(()); // already watching the target
                }
                let target_directory = self.requested_directory.clone();
                let mut options: Vec<fswatch::WatchOption> = Vec::new();
                if self.recursive {
                    options.push(fswatch::with_recursive());
                }
                let subscription = watcher.backend.watch_directory(
                    &target_directory,
                    self.target_callback(target_directory.clone()),
                    options,
                )?;
                let previous = inner.subscription.replace(subscription);
                inner.watched_directory = target_directory.clone();
                inner.watching_target = true;
                if let Some(previous) = previous {
                    let _ = previous.close();
                }
                if emit_synthetic_creates {
                    watcher.emit_synthetic_creates(&target_directory, self.kind, self.recursive);
                }
                return Ok(());
            }

            let Some(ancestor) = nearest_existing_ancestor(&watcher.fs, &self.requested_directory)
            else {
                // Nothing exists to watch (even the root is gone); drop any
                // subscription.
                if let Some(previous) = inner.subscription.take() {
                    inner.watched_directory = RootedDirectoryPath::default();
                    inner.watching_target = false;
                    let _ = previous.close();
                }
                return Ok(());
            };
            let ancestor_directory = ancestor;
            if !inner.watching_target
                && inner.subscription.is_some()
                && inner.watched_directory == ancestor_directory
            {
                return Ok(()); // already watching the correct ancestor
            }
            let subscription = watcher.backend.watch_directory(
                &ancestor_directory,
                self.ancestor_callback(),
                Vec::new(),
            )?;
            let previous = inner.subscription.replace(subscription);
            inner.watched_directory = ancestor_directory;
            inner.watching_target = false;
            if let Some(previous) = previous {
                let _ = previous.close();
            }
            // The target may have appeared between the DirectoryExists check
            // above and installing this ancestor subscription (e.g. an atomic
            // tree creation), so loop to descend further or promote
            // immediately. Any promotion from here on is a missing→present
            // transition, so synthesize creates.
            emit_synthetic_creates = true;
        }
    }

    /// `targetCallback` returns the fswatch callback for a target watch
    /// rooted at `watched_directory`. It forwards events to the session
    /// and, on [`fswatch::ERR_WATCH_TERMINATED`] (the watched directory was
    /// deleted), falls back to watching the nearest existing ancestor so
    /// the watch re-attaches when the directory is recreated.
    fn target_callback(self: &Arc<Self>, watched_directory: RootedDirectoryPath) -> WatchCallback {
        let watcher = self.watcher.clone();
        let me = Arc::downgrade(self);
        let kind = self.kind;
        Arc::new(
            move |events: Vec<WatchEvent>, err: Option<fswatch::Error>| {
                let mut terminated = false;
                if let Some(err) = &err {
                    if err.is(&fswatch::ERR_OVERFLOW) {
                        if let Some(watcher) = watcher.upgrade() {
                            watcher.logger.logf(format_args!(
                            "lspwatcher: watch overflow in {:?} (some events may have been dropped): {err}",
                            watched_directory.as_string()
                        ));
                        }
                    } else if err.is(&fswatch::ERR_WATCH_TERMINATED) {
                        terminated = true;
                        if let Some(watcher) = watcher.upgrade() {
                            watcher.logger.logf(format_args!(
                                "lspwatcher: watch terminated in {:?} (directory removed): {err}",
                                watched_directory.as_string()
                            ));
                        }
                    } else if let Some(watcher) = watcher.upgrade() {
                        watcher.logger.logf(format_args!(
                            "lspwatcher: watch error in {:?}: {err}",
                            watched_directory.as_string()
                        ));
                    }
                }
                if !events.is_empty()
                    && let Some(watcher) = watcher.upgrade()
                {
                    watcher.forward_events(kind, events);
                }
                if terminated {
                    // The delete event for the directory was forwarded above;
                    // now re-attach to the nearest existing ancestor.
                    if let Some(me) = me.upgrade() {
                        me.handle_terminated();
                    }
                }
            },
        )
    }

    /// `handleTerminated` clears the dead target watch (the backend has
    /// already removed it) and re-evaluates, falling back to an ancestor
    /// watch on the nearest existing ancestor so the watch re-attaches when
    /// the directory reappears. Clearing the state first is essential:
    /// reconcile would otherwise see `watching_target && subscription !=
    /// nil` and conclude the target is already watched, even though the
    /// subscription is dead — losing recovery if the directory is recreated
    /// before reconcile runs.
    fn handle_terminated(self: &Arc<Self>) {
        let previous = {
            let mut inner = self.inner.lock().unwrap();
            if inner.closed {
                return;
            }
            inner.watched_directory = RootedDirectoryPath::default();
            inner.watching_target = false;
            inner.subscription.take()
        };
        if let Some(previous) = previous {
            let _ = previous.close();
        }
        let _ = self.reconcile(true /* emit_synthetic_creates */);
    }

    /// `ancestorCallback` returns the fswatch callback for an ancestor
    /// watch. Ancestor watches exist only to detect the target — or an
    /// intermediate path component — being created; their events are about
    /// ancestor directories the session doesn't track, so they are ignored
    /// and the watch is simply re-evaluated.
    fn ancestor_callback(self: &Arc<Self>) -> WatchCallback {
        let me = Arc::downgrade(self);
        Arc::new(
            move |_events: Vec<WatchEvent>, _err: Option<fswatch::Error>| {
                if let Some(me) = me.upgrade() {
                    let _ = me.reconcile(true /* emit_synthetic_creates */);
                }
            },
        )
    }
}

/// `nearestExistingAncestor` returns the deepest existing directory that is
/// `dir` or an ancestor of `dir`, walking upward. `None` only if nothing in
/// the chain (including the root) exists.
fn nearest_existing_ancestor(
    fs: &Arc<dyn Vfs>,
    dir: &RootedDirectoryPath,
) -> Option<RootedDirectoryPath> {
    let mut dir = dir.clone();
    loop {
        if fs.directory_exists(&dir) {
            return Some(dir);
        }
        let parent = dir.as_path().directory();
        if parent == dir {
            return None;
        }
        dir = parent;
    }
}

/// `*time.Timer` as returned by `time.AfterFunc` — `stop` prevents the
/// callback from running if it has not started; a callback already running
/// is not interrupted.
struct FlushTimer {
    stopped: Arc<AtomicBool>,
}

impl FlushTimer {
    /// `Stop`.
    fn stop(&self) {
        self.stopped.store(true, Ordering::Release);
    }
}

/// `time.AfterFunc(d, f)` — runs `f` on a timer thread once `d` elapses,
/// unless stopped first.
fn after_func(d: Duration, f: impl FnOnce() + Send + 'static) -> FlushTimer {
    let stopped = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&stopped);
    std::thread::spawn(move || {
        std::thread::sleep(d);
        if !flag.load(Ordering::Acquire) {
            f();
        }
    });
    FlushTimer { stopped }
}

/// `watchRoot` extracts the directory the fswatch subscription should be
/// rooted at from a FileSystemWatcher. The patterns the project layer
/// produces are of the form `<dir>/**/*` (recursive) or `<dir>/*`
/// (non-recursive, used by granular watch mode), either as a Pattern
/// with a fully-qualified directory or as a RelativePattern with a
/// file:// BaseUri, so the heuristic of "everything before the first
/// glob meta character" is reliable. Use [`is_recursive_glob`] to
/// determine whether the subscription should be recursive.
///
/// Returned roots are tspath-normalized (forward-slash) absolute paths.
fn watch_root(file_system_watcher: &FileSystemWatcher) -> (RootedDirectoryPath, bool) {
    if let Some(pattern) = &file_system_watcher.glob_pattern.pattern {
        return to_watch_root(&root_from_glob(pattern));
    }
    if let Some(relative_pattern) = &file_system_watcher.glob_pattern.relative_pattern {
        if let Some(uri) = &relative_pattern.base_uri.uri {
            let base = DocumentUri(uri.0.clone()).file_name();
            if !base.as_string().is_empty() {
                let root = root_from_glob(&relative_pattern.pattern);
                return (
                    tspath::rooted_directory_path_from_path(base.as_path())
                        .resolve_directory(&root),
                    true,
                );
            }
        }
        return (RootedDirectoryPath::default(), false);
    }
    (RootedDirectoryPath::default(), false)
}

/// `toWatchRoot`.
fn to_watch_root(root: &str) -> (RootedDirectoryPath, bool) {
    if root.is_empty() || !tspath::path_is_absolute(root) {
        return (RootedDirectoryPath::default(), false);
    }
    (tspath::rooted_directory_path_from_normalized(root), true)
}

/// `rootFromGlob`.
fn root_from_glob(pattern: &str) -> String {
    let pattern = tspath::normalize_slashes(pattern);
    let mut meta_index = None;
    for (i, b) in pattern.bytes().enumerate() {
        match b {
            b'*' | b'?' | b'[' | b'{' => meta_index = Some(i),
            _ => {}
        }
        if meta_index.is_some() {
            break;
        }
    }
    let Some(meta_index) = meta_index else {
        return tspath::normalize_path(pattern.trim_end_matches('/')).into_owned();
    };
    let directory = pattern[..meta_index].trim_end_matches('/');
    if directory.is_empty() {
        return String::new();
    }
    tspath::normalize_path(directory).into_owned()
}

/// `watchPatternString`.
fn watch_pattern_string(file_system_watcher: &FileSystemWatcher) -> String {
    if let Some(pattern) = &file_system_watcher.glob_pattern.pattern {
        return pattern.clone();
    }
    if let Some(relative_pattern) = &file_system_watcher.glob_pattern.relative_pattern {
        let mut base = String::new();
        if let Some(uri) = &relative_pattern.base_uri.uri {
            base = uri.0.clone();
        }
        return format!("{base}/{}", relative_pattern.pattern);
    }
    String::new()
}

/// `isRecursiveGlob` reports whether a FileSystemWatcher's pattern requests
/// recursive watching (contains a `**` segment). Granular watch mode emits
/// non-recursive `<dir>/*` patterns, which watch only the immediate
/// directory.
fn is_recursive_glob(file_system_watcher: &FileSystemWatcher) -> bool {
    watch_pattern_string(file_system_watcher).contains("**")
}

/// `effectiveKind`.
fn effective_kind(file_system_watcher: &FileSystemWatcher) -> WatchKind {
    file_system_watcher.kind.unwrap_or(WatchKind(
        WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0,
    ))
}
