// Ported from tsc/internal/execute/watchmanager/watchmanager.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::io;
use std::io::Write as _;
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender};
use std::sync::{Arc, Mutex, MutexGuard, Weak};
use std::time::Duration;

use rustc_hash::FxHashMap;
use tsc_core::context::Context;
use tsc_core::core::diff_maps_func;
use tsc_fswatch::{self as fswatch, EventKind};
use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RootedDirectoryPath, RootedPath};

use crate::watchbackend::{
    FsWatchBackend, WatchBackend, WatchCallback, WatchDirectoryRequest, WatchHandle,
    should_ignore_watch_path,
};

/// `ctx.Done()` is polled with this interval inside `run_loop`'s channel
/// receive — cancel latency is bounded by it instead of select-instant
/// (same pattern as `tsc-ipc`'s `CALL_POLL_INTERVAL`).
const RUN_LOOP_POLL_INTERVAL: Duration = Duration::from_millis(10);

/// `WatchEvent` — one filesystem change rooted at the watched directory.
#[derive(Debug, Clone)]
pub struct WatchEvent {
    /// `Path`.
    pub path: RootedPath,
    /// `Kind`.
    pub kind: EventKind,
}

/// `watchedDir`.
struct WatchedDir {
    dir: RootedDirectoryPath,
    /// `closer` — `None` until `create_dir_watches` installs the handle (Go
    /// assigns `entry.closer` after `WatchDirectories` returns), and after
    /// `close`.
    closer: Mutex<Option<Box<dyn WatchHandle>>>,
    recursive: bool,
}

impl WatchedDir {
    /// `wd.closer.Close()` — idempotent; Go's `io.Closer` may be nil until
    /// the batch returns, `Option` mirrors that.
    fn close(&self) {
        if let Some(closer) = self.closer.lock().unwrap().take() {
            closer.close();
        }
    }
}

/// `dirWatchUpdate`.
#[derive(Debug, Clone)]
struct DirWatchUpdate {
    key: PathKey,
    dir: RootedDirectoryPath,
    recursive: bool,
}

struct Inner {
    backend: Option<Arc<dyn WatchBackend>>,
    watched_dirs: FxHashMap<PathKey, Arc<WatchedDir>>,
}

struct ChangedState {
    /// `changedPaths` — `None` is Go's nil map.
    paths: Option<FxHashMap<RootedPath, EventKind>>,
    overflow: bool,
}

/// `WatchManager` manages fswatch directory watches, event accumulation,
/// and `DoCycle` signaling. It is shared by the CLI watcher and the build
/// mode orchestrator.
///
/// Locking contract (as Go):
///   - Call [`WatchManager::lock`] around the entire `DoCycle` body; the
///     returned [`WatchManagerLock`] exposes the operations that must run
///     under the lock (`reconcile_watches`, `ensure_default_backend`,
///     `set_backend`, `is_path_under_watch`).
///   - `close_all_watches` and `handle_watch_terminated` manage their own
///     locking.
pub struct WatchManager {
    inner: Mutex<Inner>,
    /// Watch callbacks capture this `Weak` — Go's closures hold the
    /// `*WatchManager` strongly, but that would create an
    /// Arc cycle here (wm → watched dir → callback → wm), so a dead manager
    /// simply drops late events instead.
    me: Weak<WatchManager>,
    do_cycle_tx: SyncSender<()>,
    /// `Receiver` is `!Sync`; the `Mutex` is always uncontended (only
    /// `run_loop`/`DoCycleCh` consumers receive).
    do_cycle_rx: Mutex<Receiver<()>>,
    case_sensitivity: CaseSensitivity,

    /// `DebugLog` receives verbose watch diagnostics when non-`None`.
    pub debug_log: Mutex<Option<Box<dyn io::Write + Send>>>,

    warn_writer: Mutex<Box<dyn io::Write + Send>>,
    /// `dirExists` — `Box<dyn Fn>` is directly callable.
    dir_exists: Box<dyn Fn(&RootedDirectoryPath) -> bool + Send + Sync>,

    changed: Mutex<ChangedState>,
}

/// `NewWatchManager(warnWriter, dirExists, caseSensitivity)` — Go returns
/// `*WatchManager`; the `Arc` here mirrors that shared ownership (watch
/// callbacks run on watcher threads).
pub fn new_watch_manager(
    warn_writer: Box<dyn io::Write + Send>,
    dir_exists: impl Fn(&RootedDirectoryPath) -> bool + Send + Sync + 'static,
    case_sensitivity: CaseSensitivity,
) -> Arc<WatchManager> {
    let (do_cycle_tx, do_cycle_rx) = std::sync::mpsc::sync_channel(1);
    Arc::new_cyclic(|me| WatchManager {
        inner: Mutex::new(Inner {
            backend: None,
            watched_dirs: FxHashMap::default(),
        }),
        me: me.clone(),
        do_cycle_tx,
        do_cycle_rx: Mutex::new(do_cycle_rx),
        case_sensitivity,
        debug_log: Mutex::new(None),
        warn_writer: Mutex::new(warn_writer),
        dir_exists: Box::new(dir_exists),
        changed: Mutex::new(ChangedState {
            paths: None,
            overflow: false,
        }),
    })
}

/// `wm.mu` — the guard returned by [`WatchManager::lock`]; `Drop` is Go's
/// `Unlock`.
pub struct WatchManagerLock<'a> {
    wm: &'a WatchManager,
    inner: MutexGuard<'a, Inner>,
}

impl WatchManager {
    /// `wm.Lock()`/`wm.Unlock()` — hold the guard for the duration.
    pub fn lock(&self) -> WatchManagerLock<'_> {
        WatchManagerLock {
            wm: self,
            inner: self.inner.lock().unwrap(),
        }
    }

    /// `wm.SetBackend(b)` — for use before/without the lock (Go's unlocked
    /// init call); inside a locked region use the guard's
    /// [`WatchManagerLock::set_backend`].
    pub fn set_backend(&self, b: Arc<dyn WatchBackend>) {
        self.inner.lock().unwrap().backend = Some(b);
    }

    /// `wm.Backend()`.
    pub fn backend(&self) -> Option<Arc<dyn WatchBackend>> {
        self.inner.lock().unwrap().backend.clone()
    }

    /// `wm.DoCycleCh()` — the receive side; lock to `recv`/`recv_timeout`.
    pub fn do_cycle_ch(&self) -> &Mutex<Receiver<()>> {
        &self.do_cycle_rx
    }

    /// `wm.DrainEvents()` — `(changed, overflow)`; `None` is Go's nil map.
    pub fn drain_events(&self) -> (Option<FxHashMap<RootedPath, EventKind>>, bool) {
        let mut changed = self.changed.lock().unwrap();
        (
            changed.paths.take(),
            std::mem::replace(&mut changed.overflow, false),
        )
    }

    /// `wm.ForceOverflow()`.
    pub fn force_overflow(&self) {
        self.changed.lock().unwrap().overflow = true;
    }

    /// `wm.signalDoCycle()` — non-blocking send; coalesces with a pending
    /// signal like Go's `select`/`default`.
    fn signal_do_cycle(&self) {
        let _ = self.do_cycle_tx.try_send(());
    }

    fn dlog(&self, args: fmt::Arguments) {
        if let Some(w) = self.debug_log.lock().unwrap().as_mut() {
            let _ = w.write_fmt(args);
        }
    }

    /// `wm.onWatchEvents(events, err)`.
    fn on_watch_events(&self, events: Vec<WatchEvent>, err: Option<fswatch::Error>) {
        if let Some(err) = err {
            if err.is(&fswatch::ERR_OVERFLOW) {
                self.dlog(format_args!("[watch] event overflow, triggering rebuild\n"));
                self.changed.lock().unwrap().overflow = true;
                self.signal_do_cycle();
                return;
            }
            let _ = writeln!(
                self.warn_writer.lock().unwrap(),
                "Warning: File watch error: {err}"
            );
            return;
        }

        if !events.is_empty() {
            {
                let mut msg = format!("[watch] {} event(s): ", events.len());
                for (i, e) in events.iter().enumerate() {
                    if i > 0 {
                        msg.push_str(", ");
                    }
                    if i >= 5 {
                        msg.push_str(&format!("... and {} more", events.len() - i));
                        break;
                    }
                    msg.push_str(&format!("{} {}", e.kind, e.path.as_string()));
                }
                msg.push('\n');
                self.dlog(format_args!("{msg}"));
            }
            let mut changed = self.changed.lock().unwrap();
            let paths = changed.paths.get_or_insert_with(|| {
                FxHashMap::with_capacity_and_hasher(events.len(), Default::default())
            });
            for e in events {
                paths.insert(e.path, e.kind);
            }
            drop(changed);
            self.signal_do_cycle();
        }
    }

    /// `wm.handleWatchTerminated(key, identity)`.
    fn handle_watch_terminated(&self, key: &PathKey, identity: &Arc<WatchedDir>) {
        self.dlog(format_args!(
            "[watch] watch terminated: {}\n",
            identity.dir.as_string()
        ));
        let stale_closer = {
            let mut inner = self.inner.lock().unwrap();
            match inner.watched_dirs.get(key) {
                Some(wd) if Arc::ptr_eq(wd, identity) => {
                    let stale = wd.closer.lock().unwrap().take();
                    inner.watched_dirs.remove(key);
                    stale
                }
                _ => None,
            }
        };
        if let Some(closer) = stale_closer {
            closer.close();
        }
        self.changed.lock().unwrap().overflow = true;
        self.signal_do_cycle();
    }

    /// `wm.CloseAllWatches()`.
    pub fn close_all_watches(&self) {
        let closers: Vec<Arc<WatchedDir>> = {
            let mut inner = self.inner.lock().unwrap();
            inner.watched_dirs.drain().map(|(_, wd)| wd).collect()
        };
        for wd in closers {
            wd.close();
        }
    }

    /// `wm.createDirWatchRequest(update, entry)`.
    fn create_dir_watch_request(
        &self,
        update: &DirWatchUpdate,
        entry: &Arc<WatchedDir>,
    ) -> WatchDirectoryRequest {
        let me = self.me.clone();
        let key = update.key.clone();
        let identity = Arc::clone(entry);
        let callback: WatchCallback = Arc::new(move |events, err| {
            let Some(wm) = me.upgrade() else {
                return;
            };
            if err
                .as_ref()
                .is_some_and(|e| e.is(&fswatch::ERR_WATCH_TERMINATED))
            {
                wm.handle_watch_terminated(&key, &identity);
                return;
            }
            wm.on_watch_events(events, err);
        });
        WatchDirectoryRequest {
            dir: update.dir.clone(),
            recursive: entry.recursive,
            ignore: Some(Arc::new(should_ignore_watch_path)),
            callback,
        }
    }

    /// `wm.ResolveDesiredDirs(desiredDirs)`.
    pub fn resolve_desired_dirs(
        &self,
        desired_dirs: FxHashMap<RootedDirectoryPath, bool>,
    ) -> FxHashMap<RootedDirectoryPath, bool> {
        let mut resolved_by_path: FxHashMap<PathKey, DirWatchUpdate> =
            FxHashMap::with_capacity_and_hasher(desired_dirs.len(), Default::default());
        for (dir, recursive) in &desired_dirs {
            // Only directories on disk can be watched. The embedded libs
            // (bundled:///libs) exist in the FS but not on disk.
            if !tspath::is_rooted_disk_path(dir.as_string()) {
                self.dlog(format_args!(
                    "[watch] not a disk path: {}\n",
                    dir.as_string()
                ));
                continue;
            }
            let mut watch_dir = dir.clone();
            let mut watch_recursive = *recursive;
            while !(self.dir_exists)(&watch_dir) {
                let parent = watch_dir.as_path().directory();
                if parent == watch_dir {
                    break;
                }
                watch_dir = parent;
                watch_recursive = false; // ancestor fallbacks are always non-recursive
            }
            // CanWatchDirectory only guards against falling back to an ancestor that is too generic to watch
            // (/, /home, ...). A directory that exists and was asked for is watched at any depth, otherwise a
            // project that lives near the filesystem root (say /app or /srv/app) would never be watched.
            if !(self.dir_exists)(&watch_dir)
                || (watch_dir != *dir && !crate::watchbackend::can_watch_directory(&watch_dir))
            {
                self.dlog(format_args!(
                    "[watch] no watchable ancestor for {}\n",
                    dir.as_string()
                ));
                continue;
            }
            if watch_dir != *dir {
                self.dlog(format_args!(
                    "[watch] resolved {} to ancestor {}\n",
                    dir.as_string(),
                    watch_dir.as_string()
                ));
            }
            let key = self.case_sensitivity.path_key(&watch_dir.as_path());
            resolved_by_path
                .entry(key.clone())
                .and_modify(|existing| existing.recursive |= watch_recursive)
                .or_insert(DirWatchUpdate {
                    key,
                    dir: watch_dir,
                    recursive: watch_recursive,
                });
        }
        resolved_by_path
            .into_values()
            .map(|watch| (watch.dir, watch.recursive))
            .collect()
    }

    /// `wm.createDirWatches(updates)` — must be called under the lock.
    fn create_dir_watches(
        &self,
        inner: &mut Inner,
        updates: Vec<DirWatchUpdate>,
    ) -> Result<(), fswatch::Error> {
        if updates.is_empty() {
            return Ok(());
        }
        let mut requests = Vec::with_capacity(updates.len());
        let mut entries = Vec::with_capacity(updates.len());
        for update in &updates {
            let entry = Arc::new(WatchedDir {
                dir: update.dir.clone(),
                closer: Mutex::new(None),
                recursive: update.recursive,
            });
            requests.push(self.create_dir_watch_request(update, &entry));
            entries.push(entry);
        }
        let backend = inner
            .backend
            .clone()
            .expect("create_dir_watches called without a backend");
        match backend.watch_directories(requests) {
            Ok(closers) => {
                for ((update, entry), closer) in
                    updates.into_iter().zip(entries.iter()).zip(closers)
                {
                    *entry.closer.lock().unwrap() = Some(closer);
                    inner
                        .watched_dirs
                        .insert(update.key.clone(), Arc::clone(entry));
                }
                Ok(())
            }
            Err(err) => {
                for update in &updates {
                    self.dlog(format_args!(
                        "[watch] failed to watch directory {}: {err}\n",
                        update.dir.as_string()
                    ));
                }
                Err(err)
            }
        }
    }

    /// `wm.IsPathUnderWatch(path)` — reads `watchedDirs` under the lock.
    pub fn is_path_under_watch(&self, path: &RootedPath) -> bool {
        let inner = self.inner.lock().unwrap();
        inner
            .watched_dirs
            .values()
            .any(|watch| self.case_sensitivity.contains_path(&watch.dir, path))
    }

    /// `wm.RunLoop(ctx, doCycle)`.
    ///
    /// PORT: Go's `select` on `ctx.Done()` + `doCycleCh` becomes a
    /// `recv_timeout` poll on the channel — cancellation latency is bounded
    /// by [`RUN_LOOP_POLL_INTERVAL`].
    pub fn run_loop(&self, ctx: &Context, mut do_cycle: impl FnMut()) {
        let rx = self.do_cycle_rx.lock().unwrap();
        loop {
            if ctx.is_cancelled() {
                // rx guard is only held by this loop; safe to hold through close.
                self.close_all_watches();
                return;
            }
            match rx.recv_timeout(RUN_LOOP_POLL_INTERVAL) {
                Ok(()) => do_cycle(),
                Err(RecvTimeoutError::Timeout) => {}
                // `do_cycle_tx` is owned by `self` and can never disconnect.
                Err(RecvTimeoutError::Disconnected) => unreachable!(),
            }
        }
    }
}

impl WatchManagerLock<'_> {
    /// `wm.SetBackend(b)` under the lock.
    pub fn set_backend(&mut self, b: Arc<dyn WatchBackend>) {
        self.inner.backend = Some(b);
    }

    /// `wm.Backend()` under the lock.
    pub fn backend(&self) -> Option<Arc<dyn WatchBackend>> {
        self.inner.backend.clone()
    }

    /// `wm.EnsureDefaultBackend()` under the lock.
    pub fn ensure_default_backend(&mut self) {
        if self.inner.backend.is_none() {
            let fsw = fswatch::default();
            let name = fsw.name();
            self.inner.backend = Some(Arc::new(FsWatchBackend { inner: fsw }));
            self.wm.dlog(format_args!("[watch] using {name} backend\n"));
        }
    }

    /// `wm.IsPathUnderWatch(path)` under the lock (Go reads `watchedDirs`
    /// without locking during `DoCycle`; call sites hold the lock).
    pub fn is_path_under_watch(&self, path: &RootedPath) -> bool {
        self.inner
            .watched_dirs
            .values()
            .any(|watch| self.wm.case_sensitivity.contains_path(&watch.dir, path))
    }

    /// `wm.ReconcileWatches(desiredDirs)` — must be called under the lock.
    ///
    /// PORT: Go deletes `watchedDirs` entries inside `DiffMapsFunc`
    /// callbacks (legal under Go's range-during-delete); here keys are
    /// collected and removed after the diff — the diff only visits each key
    /// once, so the result is identical.
    pub fn reconcile_watches(
        &mut self,
        desired_dirs: FxHashMap<RootedDirectoryPath, bool>,
    ) -> Result<(), fswatch::Error> {
        if self.inner.backend.is_none() {
            return Ok(());
        }

        let mut desired_by_path: FxHashMap<PathKey, DirWatchUpdate> =
            FxHashMap::with_capacity_and_hasher(desired_dirs.len(), Default::default());
        for (dir, recursive) in desired_dirs {
            let key = self.wm.case_sensitivity.path_key(&dir.as_path());
            desired_by_path
                .entry(key.clone())
                .and_modify(|existing: &mut DirWatchUpdate| existing.recursive |= recursive)
                .or_insert(DirWatchUpdate {
                    key,
                    dir,
                    recursive,
                });
        }

        let mut additions: Vec<DirWatchUpdate> = Vec::new();
        let mut changes: Vec<DirWatchUpdate> = Vec::new();
        // `RefCell`: both `FnMut` callbacks below push to `removals`.
        let removals = std::cell::RefCell::new(Vec::<PathKey>::new());

        let wm = self.wm;
        diff_maps_func(
            &self.inner.watched_dirs,
            &desired_by_path,
            |wd: &Arc<WatchedDir>, desired: &DirWatchUpdate| wd.recursive == desired.recursive,
            Some(&mut |_key: &PathKey, desired: &DirWatchUpdate| {
                wm.dlog(format_args!(
                    "[watch] watching directory {} (recursive={})\n",
                    desired.dir.as_string(),
                    desired.recursive
                ));
                additions.push(desired.clone());
            }),
            Some(&mut |key: &PathKey, wd: &Arc<WatchedDir>| {
                wm.dlog(format_args!(
                    "[watch] closing stale dir watch: {}\n",
                    wd.dir.as_string()
                ));
                wd.close();
                removals.borrow_mut().push(key.clone());
            }),
            Some(
                &mut |key: &PathKey, wd: &Arc<WatchedDir>, desired: &DirWatchUpdate| {
                    wm.dlog(format_args!(
                        "[watch] recreating dir watch {} (recursive {}→{})\n",
                        wd.dir.as_string(),
                        wd.recursive,
                        desired.recursive
                    ));
                    wd.close();
                    removals.borrow_mut().push(key.clone());
                    changes.push(desired.clone());
                },
            ),
        );
        for key in removals.into_inner() {
            self.inner.watched_dirs.remove(&key);
        }
        additions.append(&mut changes);
        self.wm.create_dir_watches(&mut self.inner, additions)
    }
}

/// `DirWatchSet` accumulates the set of directories that should be watched
/// while answering coverage queries efficiently. A directory is "covered"
/// when it is already present in the set, or when it is contained within a
/// recursive watch directory already in the set.
pub struct DirWatchSet {
    case_sensitivity: CaseSensitivity,
    dirs: FxHashMap<PathKey, DirWatchUpdate>,
}

/// `NewDirWatchSet(caseSensitivity)`.
pub fn new_dir_watch_set(case_sensitivity: CaseSensitivity) -> DirWatchSet {
    DirWatchSet {
        case_sensitivity,
        dirs: FxHashMap::default(),
    }
}

impl DirWatchSet {
    /// `s.Set(dir, recursive)` — a recursive watch is never downgraded by a
    /// later non-recursive `Set`.
    pub fn set(&mut self, dir: RootedDirectoryPath, recursive: bool) {
        let key = self.case_sensitivity.path_key(&dir.as_path());
        self.dirs
            .entry(key.clone())
            .and_modify(|existing: &mut DirWatchUpdate| existing.recursive |= recursive)
            .or_insert(DirWatchUpdate {
                key,
                dir,
                recursive,
            });
    }

    /// `s.Covered(dir)`.
    pub fn covered(&self, dir: &RootedDirectoryPath) -> bool {
        let mut path = self.case_sensitivity.path_key(&dir.as_path());
        if self.dirs.contains_key(&path) {
            return true;
        }
        loop {
            let parent = path.parent();
            if parent == path {
                return false;
            }
            path = parent;
            if self.dirs.get(&path).is_some_and(|watch| watch.recursive) {
                return true;
            }
        }
    }

    /// `s.Dirs()`.
    pub fn dirs(&self) -> FxHashMap<RootedDirectoryPath, bool> {
        self.dirs
            .values()
            .map(|watch| (watch.dir.clone(), watch.recursive))
            .collect()
    }
}
