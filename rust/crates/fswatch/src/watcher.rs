// Ported from tsc/internal/fswatch/watcher.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! Watcher-facing API surface: `Watcher` trait, `Watch` handle, watch
//! options, `WatchDirectoryRequest`, and the shared `DirWatch`/`callback`
//! bookkeeping that Go keeps in `watcher.go`.
//!
//! PORT: Go's `watcher` resolves to a per-platform `watcherImpl` factory
//! (inotify/fanotify/fsevents/kqueue/windows). This port implements exactly
//! one backend, [`crate::notify_backend`], backed by the `notify` crate's
//! `RecommendedWatcher` (inotify on Linux). Recursive-watch sharing and
//! consolidation (`canShareRecursiveDirWatches`,
//! `findCoveringRecursiveWatchLocked`, `findConsolidationDirLocked`) are
//! FSEvents-only in Go and are not ported; `cb.dir == dw.dir` always holds.
//! The volume-aware `pathComparer` (`pathcompare.go`, `pathkey.go`) collapses
//! to exact-byte comparison — `pathComparer{}` is what every non-Darwin
//! backend uses in Go.

use std::path::Path;
use std::sync::{Arc, Mutex, OnceLock};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::debounce::Debounce;
use crate::error::{ERR_UNAVAILABLE, Error};
use crate::event::{Event, EventKind, EventList};
use crate::notify_backend::{self, Backend};

/// `IgnoreFn` — Go's `func(path string) bool` filter for [`with_ignore`].
/// Returning true for a path silently drops events for that path.
pub type IgnoreFn = Arc<dyn Fn(&str) -> bool + Send + Sync>;

/// `WatchCallback` receives batched filesystem events. Rapid changes are
/// coalesced before delivery.
///
/// For a given [`Watch`], the callback is never invoked concurrently with
/// itself. It runs on a library thread, not the caller's.
///
/// When `err` is `Some`, use [`Error::is`] to check for
/// [`crate::ERR_OVERFLOW`] (recoverable) or [`crate::ERR_WATCH_TERMINATED`]
/// (terminal).
pub type WatchCallback = Arc<dyn Fn(Vec<Event>, Option<Error>) + Send + Sync>;

/// `WatchOption` configures a watch.
///
/// PORT: Go's `WatchOption` interface (`applyWatchOption`) becomes a closed
/// enum; consumers only ever use [`with_recursive`] and [`with_ignore`].
/// `File` is the internal `fileOption` used by `watch_file`.
#[derive(Clone)]
pub enum WatchOption {
    /// `WithRecursive()` — watch the entire directory tree.
    Recursive,
    /// `WithIgnore(fn)` — drop events for paths where the function is true.
    Ignore(IgnoreFn),
    /// `fileOption{path}` — restrict delivery to a single file. Emitted by
    /// `watch_file`; not part of the public Go API surface.
    #[doc(hidden)]
    File(String),
}

/// `WithRecursive` returns a [`WatchOption`] that enables recursive watching
/// of the entire directory tree. Without this option, `watch_directory`
/// watches only direct children of `dir`.
pub fn with_recursive() -> WatchOption {
    WatchOption::Recursive
}

/// `WithIgnore` returns a [`WatchOption`] that filters events before
/// delivery. If the function returns true for a path, events for that path
/// are silently dropped. The filtering is per-subscriber; multiple watches
/// on the same directory may have different ignore functions.
pub fn with_ignore(f: impl Fn(&str) -> bool + Send + Sync + 'static) -> WatchOption {
    WatchOption::Ignore(Arc::new(f))
}

/// `watchOptions` — the accumulated option values.
#[derive(Default)]
struct WatchOptions {
    ignore: Option<IgnoreFn>,
    recursive: bool,
    file: String,
}

impl WatchOptions {
    fn apply(&mut self, option: &WatchOption) {
        match option {
            WatchOption::Recursive => self.recursive = true,
            WatchOption::Ignore(f) => self.ignore = Some(Arc::clone(f)),
            WatchOption::File(p) => self.file = p.clone(),
        }
    }
}

/// `WatchDirectoryRequest` describes one directory subscription in a
/// `watch_directories` batch.
pub struct WatchDirectoryRequest {
    /// `Dir` — absolute path of the directory to watch.
    pub dir: String,
    /// `Callback` — batch receiver. Go permits a nil callback (rejected with
    /// `errNilCallback`); here the field is `Option`, and `None` maps to
    /// [`Error::NilCallback`].
    pub callback: Option<WatchCallback>,
    /// `Options` — watch modifiers.
    pub options: Vec<WatchOption>,
}

/// `Watcher` represents a filesystem watching implementation. Use
/// [`default`] to obtain the platform-default instance (or [`kqueue`] to
/// select a specific backend — see its `PORT` note).
///
/// Sealed like Go's `unexported()` interface method: external crates cannot
/// implement `Watcher`.
pub trait Watcher: sealed::Sealed + Send + Sync {
    /// `Name` returns a stable identifier ("inotify", "fsevents", "kqueue",
    /// "windows").
    fn name(&self) -> &'static str;
    /// `Available` reports whether this watcher works on the current OS.
    fn available(&self) -> bool;
    /// `HasFastRecursiveBackend` reports whether this watcher supports
    /// efficient recursive watching without requiring a full userspace tree
    /// walk (Windows ReadDirectoryChangesW subtree mode and macOS FSEvents).
    fn has_fast_recursive_backend(&self) -> bool;
    /// `WatchDirectories` watches multiple directories as a batch. It has
    /// the same semantics as calling `watch_directory` for each request, but
    /// lets the backend arm the underlying OS watches once for the whole
    /// batch. Returned watches are in the same order as requests.
    fn watch_directories(&self, requests: Vec<WatchDirectoryRequest>) -> Result<Vec<Watch>, Error>;
    /// `WatchDirectory` watches `dir` for changes, calling `callback` with
    /// batched events. By default, only direct children are watched. Use
    /// [`with_recursive`] to watch the entire directory tree. `dir` must be
    /// an absolute path to an existing directory.
    fn watch_directory(
        &self,
        dir: &str,
        callback: WatchCallback,
        options: Vec<WatchOption>,
    ) -> Result<Watch, Error> {
        let watches = self.watch_directories(vec![WatchDirectoryRequest {
            dir: dir.to_owned(),
            callback: Some(callback),
            options,
        }])?;
        Ok(watches.into_iter().next().unwrap())
    }
    /// `WatchFile` watches a single file for changes, calling `callback`
    /// with batched events. `path` must be absolute. The file does not need
    /// to exist at subscribe time; its creation will be reported. The parent
    /// directory must exist.
    ///
    /// Unlike TypeScript's `watchFile` (which falls back to polling for
    /// missing entries), there is no automatic recovery if the parent
    /// directory is deleted: [`crate::ERR_WATCH_TERMINATED`] is delivered and
    /// the watch is dead.
    fn watch_file(&self, path: &str, callback: WatchCallback) -> Result<Watch, Error> {
        if !self.available() {
            return Err(ERR_UNAVAILABLE);
        }
        let path = canonicalize_path(&clean_path(path));
        if !path_is_absolute(&path) {
            return Err(Error::NotAbsolute);
        }
        let dir = dir_name(&path);
        if dir == path {
            return Err(Error::RootPath);
        }
        self.watch_directory(&dir, callback, vec![WatchOption::File(path)])
    }
}

mod sealed {
    pub trait Sealed {}
}

/// `Watch` represents a live watch. `close` stops watching and releases
/// resources. It is idempotent; dropping the `Watch` also closes it.
///
/// PORT: Go returns an `io.Closer`-shaped interface; here `Watch` is a
/// concrete handle that unregisters on `close`/`drop`.
pub struct Watch {
    shared: Arc<Shared>,
    dw: Arc<DirWatch>,
    id: u64,
    cancelled: Mutex<bool>,
}

impl Watch {
    /// `Close` stops watching. Idempotent; a second call is a no-op.
    pub fn close(&self) -> Result<(), Error> {
        {
            let mut cancelled = self.cancelled.lock().unwrap();
            if *cancelled {
                return Ok(());
            }
            *cancelled = true;
        }
        if self.dw.unwatch(self.id) {
            self.shared.watch_remove(&self.dw);
            self.dw.unref(&self.shared);
        }
        Ok(())
    }
}

impl Drop for Watch {
    fn drop(&mut self) {
        let _ = self.close();
    }
}

impl std::fmt::Debug for Watch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Watch")
            .field("dir", &self.dw.dir)
            .field("recursive", &self.dw.recursive)
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

/// `NotifyWatcher` is the single concrete `Watcher` implementation. Go has
/// one `*watcher` per named backend driven by a platform `watcherImpl`
/// factory; this port has one watcher over `notify::RecommendedWatcher`.
pub(crate) struct NotifyWatcher {
    name: &'static str,
    shared: Arc<Shared>,
}

impl NotifyWatcher {
    fn new() -> NotifyWatcher {
        // `Name()` — the same identifier the equivalent Go backend reports.
        // PORT: Go's `Default()` prefers fanotify on Linux (kernel >= 5.13);
        // `notify` has no fanotify backend, so Linux always reports
        // "inotify".
        let name = if cfg!(target_os = "linux") || cfg!(target_os = "android") {
            "inotify"
        } else if cfg!(target_os = "macos") {
            "fsevents"
        } else if cfg!(target_os = "windows") {
            "windows"
        } else if cfg!(any(
            target_os = "freebsd",
            target_os = "openbsd",
            target_os = "netbsd",
            target_os = "dragonfly"
        )) {
            "kqueue"
        } else {
            // notify falls back to the polling watcher elsewhere.
            "poll"
        };
        NotifyWatcher {
            name,
            shared: Arc::new(Shared::new()),
        }
    }
}

impl sealed::Sealed for NotifyWatcher {}

impl Watcher for NotifyWatcher {
    fn name(&self) -> &'static str {
        self.name
    }

    fn available(&self) -> bool {
        // `notify::recommended_watcher` works on every platform this crate
        // compiles for; instantiation failures surface as watch errors,
        // matching Go where `ErrUnavailable` is a platform property.
        true
    }

    fn has_fast_recursive_backend(&self) -> bool {
        // Same predicate as Go: true for Windows (ReadDirectoryChangesW
        // subtree mode) and macOS FSEvents (inherently recursive).
        cfg!(target_os = "windows") || cfg!(target_os = "macos")
    }

    fn watch_directories(&self, requests: Vec<WatchDirectoryRequest>) -> Result<Vec<Watch>, Error> {
        if !self.available() {
            return Err(ERR_UNAVAILABLE);
        }
        if requests.is_empty() {
            return Ok(Vec::new());
        }

        let mut prepared: Vec<(Arc<DirWatch>, u64)> = Vec::with_capacity(requests.len());
        let mut unique: Vec<Arc<DirWatch>> = Vec::with_capacity(requests.len());
        let mut seen: FxHashSet<String> = FxHashSet::default();

        macro_rules! rollback {
            () => {
                for (dw, id) in prepared.iter().rev() {
                    dw.unwatch(*id);
                    dw.unref(&self.shared);
                }
            };
        }

        for request in requests {
            let Some(callback) = request.callback else {
                rollback!();
                return Err(Error::NilCallback);
            };
            let dir = canonicalize_path(&clean_path(&request.dir));
            if !path_is_absolute(&dir) {
                rollback!();
                return Err(Error::NotAbsolute);
            }
            let physical_dir = physical_dir_for(&dir);

            let mut sopts = WatchOptions::default();
            for option in &request.options {
                sopts.apply(option);
            }

            let dw = self
                .shared
                .get_or_create_dir_watch(&dir, &physical_dir, sopts.recursive);
            let id = dw.add_callback(
                dir,
                physical_dir,
                sopts.recursive,
                callback,
                sopts.ignore,
                sopts.file,
            );
            prepared.push((Arc::clone(&dw), id));
            if seen.insert(dw.debounce_key.clone()) {
                unique.push(dw);
            }
        }

        if let Err(err) = self.shared.ensure_backend() {
            rollback!();
            return Err(err);
        }

        // Arm each unique dirWatch once (`watcherBase.watchAddMany`).
        {
            let mut guard = self.shared.state.lock().unwrap();
            let state = &mut *guard;
            let mut armed: Vec<Arc<DirWatch>> = Vec::new();
            let mut arm_err: Option<Error> = None;
            for dw in &unique {
                if state.subscriptions.contains(&dw.debounce_key) {
                    continue;
                }
                // Go does not stat non-FSEvents watch directories up front;
                // inotify's IN_ONLYDIR surfaces ENOTDIR and inotify_add_watch
                // surfaces ENOENT. `notify` happily watches files, so the
                // is-dir check is replicated here for parity.
                match validate_watch_directory(&dw.physical_dir) {
                    Ok(()) => {}
                    Err(err) => {
                        arm_err = Some(err);
                        break;
                    }
                }
                let backend = state.backend.as_mut().unwrap();
                let mode = if dw.recursive {
                    notify::RecursiveMode::Recursive
                } else {
                    notify::RecursiveMode::NonRecursive
                };
                match backend.watch(Path::new(&dw.physical_dir), mode) {
                    Ok(()) => {
                        state.subscriptions.insert(dw.debounce_key.clone());
                        state
                            .watched_paths
                            .insert(Path::new(&dw.physical_dir).to_path_buf());
                        armed.push(Arc::clone(dw));
                    }
                    Err(err) => {
                        arm_err = Some(err);
                        break;
                    }
                }
            }
            if let Some(err) = arm_err {
                // `watchAddMany` internal rollback: tear down the watches
                // armed by this call before releasing prepared callbacks.
                let backend = state.backend.as_mut().unwrap();
                for dw in &armed {
                    state.subscriptions.remove(&dw.debounce_key);
                    let _ = backend.unwatch(Path::new(&dw.physical_dir));
                    state.watched_paths.remove(Path::new(&dw.physical_dir));
                }
                drop(guard);
                rollback!();
                return Err(err);
            }
        }

        Ok(prepared
            .into_iter()
            .map(|(dw, id)| Watch {
                shared: Arc::clone(&self.shared),
                dw,
                id,
                cancelled: Mutex::new(false),
            })
            .collect())
    }
}

/// `validateWatchDirectory` — exists in Go only for consolidating backends,
/// but `IN_ONLYDIR` in the inotify mask produces the same observable
/// rejection on Linux, so the check is kept.
fn validate_watch_directory(dir: &str) -> Result<(), Error> {
    let info = std::fs::metadata(dir).map_err(|e| Error::Io(Arc::new(e)))?;
    if !info.is_dir() {
        // syscall.ENOTDIR
        return Err(Error::Io(Arc::new(std::io::Error::from_raw_os_error(
            ENOTDIR,
        ))));
    }
    Ok(())
}

/// `syscall.ENOTDIR` (20 on unix, ERROR_DIRECTORY on Windows).
#[cfg(unix)]
const ENOTDIR: i32 = 20;
#[cfg(windows)]
const ENOTDIR: i32 = 267; // ERROR_DIRECTORY
#[cfg(not(any(unix, windows)))]
const ENOTDIR: i32 = 20;

/// `Shared` holds the state Go splits between `watcher` (dirWatches map,
/// debounce) and `watcherBase`/`watcherImpl` (subscriptions, backend).
pub(crate) struct Shared {
    pub(crate) state: Mutex<SharedState>,
    // `debounce` is created lazily on first subscribe, like Go's
    // `w.debounce`.
    debounce: OnceLock<Arc<Debounce>>,
}

pub(crate) struct SharedState {
    pub(crate) backend: Option<Backend>,
    /// `watcher.dirWatches` — watch key → shared per-directory state.
    pub(crate) dir_watches: FxHashMap<String, Arc<DirWatch>>,
    /// `watcherBase.subscriptions` — keys of dirWatches with an armed OS
    /// watch.
    pub(crate) subscriptions: FxHashSet<String>,
    /// Physical paths this backend has asked `notify` to watch: requested
    /// roots plus subdirectories armed for recursive watches. `notify`'s
    /// internal set is keyed by path; this mirrors it for dedup, since
    /// calling `watch` on an already-watched recursive root re-walks the
    /// tree.
    pub(crate) watched_paths: FxHashSet<std::path::PathBuf>,
}

impl Shared {
    fn new() -> Shared {
        Shared {
            state: Mutex::new(SharedState {
                backend: None,
                dir_watches: FxHashMap::default(),
                subscriptions: FxHashSet::default(),
                watched_paths: FxHashSet::default(),
            }),
            debounce: OnceLock::new(),
        }
    }

    pub(crate) fn debounce(&self) -> &Arc<Debounce> {
        self.debounce.get_or_init(Debounce::new)
    }

    /// `w.keyForDirWatch`.
    fn key_for_dir_watch(dir: &str, recursive: bool) -> String {
        if recursive {
            return format!("{dir}\x00recursive");
        }
        dir.to_owned()
    }

    /// `watcher.getOrCreateDirWatch`, minus the FSEvents-only recursive-watch
    /// sharing/consolidation path (`canShareRecursiveDirWatches`).
    fn get_or_create_dir_watch(
        &self,
        dir: &str,
        physical_dir: &str,
        recursive: bool,
    ) -> Arc<DirWatch> {
        let mut state = self.state.lock().unwrap();
        let key = Self::key_for_dir_watch(dir, recursive);
        if let Some(dw) = state.dir_watches.get(&key) {
            return Arc::clone(dw);
        }
        let dw = DirWatch::new(
            dir.to_owned(),
            physical_dir.to_owned(),
            recursive,
            key,
            Arc::clone(self.debounce()),
        );
        state
            .dir_watches
            .insert(dw.debounce_key.clone(), Arc::clone(&dw));
        dw
    }

    /// `watcher.removeDirWatch`.
    fn remove_dir_watch(&self, dw: &Arc<DirWatch>) {
        let mut state = self.state.lock().unwrap();
        let remove = state
            .dir_watches
            .get(&dw.debounce_key)
            .is_some_and(|existing| Arc::ptr_eq(existing, dw));
        if remove {
            state.dir_watches.remove(&dw.debounce_key);
            dw.destroy_debounce();
        }
    }

    /// `watcherImpl` startup — `watcher.getImpl`/`watcherBase.run`. The
    /// `notify` watcher and its dispatch thread live for the process
    /// lifetime once created.
    fn ensure_backend(self: &Arc<Self>) -> Result<(), Error> {
        let mut state = self.state.lock().unwrap();
        if state.backend.is_some() {
            return Ok(());
        }
        let backend = notify_backend::Backend::start(self)?;
        state.backend = Some(backend);
        Ok(())
    }

    /// `watcherBase.watchRemove` — drop the OS subscription for `dw`.
    fn watch_remove(&self, dw: &Arc<DirWatch>) {
        let mut guard = self.state.lock().unwrap();
        let state = &mut *guard;
        if !state.subscriptions.remove(&dw.debounce_key) {
            return;
        }
        let Some(backend) = state.backend.as_mut() else {
            return;
        };
        let physical = dw.physical_dir.clone();
        let _ = backend.unwatch(Path::new(&physical));
        // PORT: `notify`'s `unwatch` removes the inotify watches under the
        // path's whole subtree when its internally recorded flag is
        // recursive, and an `inotify_rm_watch` of the root also kills the
        // descriptors of every auto-added child — watches sibling dirWatches
        // may still need (Go's per-wd subscription multimap survives this).
        // Re-arm every remaining subscription whose coverage overlaps the
        // removed tree; `watch` is idempotent (inotify MASK_ADD).
        let rearm: Vec<(String, bool)> = state
            .dir_watches
            .values()
            .filter(|other| {
                !Arc::ptr_eq(other, dw)
                    && state.subscriptions.contains(&other.debounce_key)
                    && (is_in_directory_or_self(&physical, &other.physical_dir)
                        || is_in_directory_or_self(&other.physical_dir, &physical))
            })
            .map(|other| (other.physical_dir.clone(), other.recursive))
            .collect();
        for (path, recursive) in rearm {
            let mode = if recursive {
                notify::RecursiveMode::Recursive
            } else {
                notify::RecursiveMode::NonRecursive
            };
            let _ = backend.watch(Path::new(&path), mode);
        }
        state
            .watched_paths
            .retain(|p| !is_in_directory_or_self(&physical, &p.to_string_lossy()));
    }
}

// ----- dirWatch: per-directory watch state ---------------------------------

/// `WatchCallback` for `DirWatch` internals.
type DebounceFn = Arc<dyn Fn() + Send + Sync>;

/// `callback` — one subscriber's registration on a `DirWatch`.
///
/// PORT: `dirComparison`/`physicalComparison`/`fileComparison` are folded
/// into plain strings — the non-Darwin `pathComparer` is exact, so no folded
/// forms are tracked. `watchDir`/`watchPhysicalDir` exist in Go only for
/// consolidated watches, which are never created here.
#[derive(Clone)]
struct Callback {
    id: u64,
    /// `dir` — the caller-visible watch root for this subscription.
    dir: String,
    /// `physicalDir` — the realpath the OS watch was armed on.
    physical_dir: String,
    recursive: bool,
    f: WatchCallback,
    ignore: Option<IgnoreFn>,
    since_seq: u64,
    terminal: Option<Error>,
    delivered: bool,
    /// `fileComparison.path` — non-empty restricts delivery to this exact
    /// file (WatchFile).
    file: String,
}

impl Callback {
    /// `mapEvent`/`mapEventCached` — rebase an event path recorded under the
    /// physical root back under the caller-visible `dir`.
    fn map_event(&self, mut e: Event) -> Event {
        // PORT: exact-comparer `rebasePrepared`; event paths are recorded as
        // display paths by the notify dispatch, so this only fires when a
        // recorded path was still physical (defensive; matches Go's flow).
        if !self.physical_dir.is_empty()
            && self.physical_dir != self.dir
            && is_in_directory_or_self(&self.physical_dir, &e.path)
        {
            e.path = rebase_path(&e.path, &self.physical_dir, &self.dir);
        }
        e
    }
}

/// `dirWatch` holds per-directory state: pending events, registered
/// callbacks, and a reference to the shared debouncer. Each watched
/// directory has one.
pub(crate) struct DirWatch {
    /// `dir` is the caller-visible watch root used in delivered event paths.
    pub(crate) dir: String,
    /// `physicalDir` is the path passed to OS watcher APIs. It differs from
    /// `dir` when `dir` or an ancestor is a symlink or reparse point to a
    /// directory.
    pub(crate) physical_dir: String,
    pub(crate) recursive: bool,
    /// Identity of this dirWatch: `watcher.keyForDirWatch`. Used as the
    /// debounce callback key (Go keys by the dirWatch pointer).
    pub(crate) debounce_key: String,
    pub(crate) events: EventList,
    inner: Mutex<DirWatchInner>,
}

struct DirWatchInner {
    callbacks: Vec<Callback>,
    debounce: Option<Arc<Debounce>>,
    next_cb_id: u64,
}

impl DirWatch {
    /// `newDirWatch`.
    fn new(
        dir: String,
        physical_dir: String,
        recursive: bool,
        debounce_key: String,
        debounce: Arc<Debounce>,
    ) -> Arc<DirWatch> {
        let dw = Arc::new(DirWatch {
            dir,
            physical_dir,
            recursive,
            debounce_key: debounce_key.clone(),
            events: EventList::default(),
            inner: Mutex::new(DirWatchInner {
                callbacks: Vec::new(),
                debounce: Some(debounce),
                next_cb_id: 0,
            }),
        });
        let weak = Arc::downgrade(&dw);
        let cb: DebounceFn = Arc::new(move || {
            if let Some(dw) = weak.upgrade() {
                dw.trigger_callbacks();
            }
        });
        dw.inner
            .lock()
            .unwrap()
            .debounce
            .as_ref()
            .unwrap()
            .add(&debounce_key, cb);
        dw
    }

    /// `dw.displayPath` — map a physical event path back under the
    /// caller-visible watch root.
    pub(crate) fn display_path(&self, watch_path: &str) -> String {
        rebase_path(watch_path, &self.physical_dir, &self.dir)
    }

    /// `dw.destroyDebounce`.
    fn destroy_debounce(&self) {
        let db = self.inner.lock().unwrap().debounce.take();
        if let Some(db) = db {
            db.remove(&self.debounce_key);
        }
    }

    /// `dw.notify` — wake the debouncer when there are undelivered
    /// subscriptions and something to deliver.
    pub(crate) fn notify(&self) {
        let (fire, db) = {
            let inner = self.inner.lock().unwrap();
            let has_pending_cbs = inner.callbacks.iter().any(|cb| !cb.delivered);
            let has_terminal = inner
                .callbacks
                .iter()
                .any(|cb| cb.terminal.is_some() && !cb.delivered);
            let has_events = self.events.size() > 0;
            let has_error = self.events.has_error();
            (
                has_pending_cbs && (has_events || has_error || has_terminal),
                inner.debounce.clone(),
            )
        };
        if fire {
            if let Some(db) = db {
                db.trigger();
            }
        }
    }

    /// `dw.addCallback` — register a subscription. Returns the callback id.
    #[allow(clippy::too_many_arguments)]
    fn add_callback(
        &self,
        dir: String,
        physical_dir: String,
        recursive: bool,
        f: WatchCallback,
        ignore: Option<IgnoreFn>,
        file: String,
    ) -> u64 {
        let mut inner = self.inner.lock().unwrap();
        inner.next_cb_id += 1;
        let id = inner.next_cb_id;
        // PORT: Go's `dw.sequence` supplies a backend event-sequence cutoff
        // for new callbacks; only the FSEvents backend sets it. The event
        // list's own sequence is the cutoff here.
        let since_seq = self.events.sequence();
        inner.callbacks.push(Callback {
            id,
            dir,
            physical_dir,
            recursive,
            f,
            ignore,
            since_seq,
            terminal: None,
            delivered: false,
            file,
        });
        id
    }

    /// `dw.unwatch` — remove a subscription; returns true when it was the
    /// last one.
    fn unwatch(&self, id: u64) -> bool {
        let mut inner = self.inner.lock().unwrap();
        if let Some(i) = inner.callbacks.iter().position(|cb| cb.id == id) {
            inner.callbacks.remove(i);
            return inner.callbacks.is_empty();
        }
        false
    }

    /// `dw.unref` — release the dirWatch back to the watcher when empty.
    fn unref(self: &Arc<Self>, shared: &Shared) {
        let empty = self.inner.lock().unwrap().callbacks.is_empty();
        if empty {
            shared.remove_dir_watch(self);
        }
    }

    /// `dw.triggerCallbacks` — the debounced fan-out: drain pending events,
    /// apply per-subscriber filtering, invoke callbacks.
    fn trigger_callbacks(&self) {
        let pending = {
            let mut inner = self.inner.lock().unwrap();
            let has_error = self.events.has_error();
            let has_events = self.events.size() > 0;
            let mut cbs: Vec<Callback> = Vec::with_capacity(inner.callbacks.len());
            let mut has_terminal = false;
            for cb in &inner.callbacks {
                if cb.delivered {
                    continue;
                }
                if cb.terminal.is_some() {
                    has_terminal = true;
                }
                cbs.push(cb.clone());
            }
            if cbs.is_empty() {
                if has_events || has_error {
                    let _ = self.events.drain();
                }
                None
            } else if !has_events && !has_error && !has_terminal {
                None
            } else {
                let start_seqs: Vec<u64> = cbs.iter().map(|cb| cb.since_seq).collect();
                let (events_by_callback, err) = self.events.drain_for_sequences(&start_seqs);
                for cb in &cbs {
                    if cb.terminal.is_none() {
                        continue;
                    }
                    for existing in inner.callbacks.iter_mut() {
                        if existing.id == cb.id {
                            existing.delivered = true;
                            break;
                        }
                    }
                }
                Some((cbs, events_by_callback, err))
            }
        };
        let Some((cbs, events_by_callback, err)) = pending else {
            return;
        };

        for (cb, cb_events) in cbs.iter().zip(events_by_callback) {
            let mut cb_events = cb_events;
            if cb.ignore.is_some() || !cb.recursive || cb.dir != self.dir || !cb.file.is_empty() {
                let mut filtered = Vec::with_capacity(cb_events.len());
                for e in cb_events {
                    let mut e = cb.map_event(e);
                    if !cb.file.is_empty() {
                        // `fileComparison` — exact-comparer `suffixPrepared`:
                        // keep only the file itself (empty suffix), then
                        // restore the caller's spelling.
                        let Some(suffix) = suffix_of(&cb.file, &e.path) else {
                            continue;
                        };
                        if !suffix.is_empty() {
                            continue;
                        }
                        e.path = cb.file.clone();
                    }
                    if let Some(ignore) = &cb.ignore {
                        if ignore(&e.path) {
                            continue;
                        }
                    }
                    if cb.dir != self.dir
                        && !e.included_watch_root
                        && e.path == cb.dir
                        && e.kind == EventKind::Update
                    {
                        continue;
                    }
                    if cb.recursive {
                        if cb.dir != self.dir && !is_in_directory_or_self(&cb.dir, &e.path) {
                            continue;
                        }
                    } else if !is_direct_child(&cb.dir, &e.path)
                        && !(cb.dir != self.dir && e.path == cb.dir)
                    {
                        continue;
                    }
                    filtered.push(e);
                }
                cb_events = filtered;
            }
            let cb_err = cb.terminal.clone().or_else(|| err.clone());
            if !cb_events.is_empty() || cb_err.is_some() {
                (cb.f)(cb_events, cb_err);
            }
        }
    }
}

// ----- package-level constructors -------------------------------------------

/// `Default` returns the recommended watcher for the current OS.
///
/// PORT: Go selects per-OS hand-rolled backends (fanotify/inotify, FSEvents,
/// ReadDirectoryChangesW, kqueue); here the single `notify`-backed watcher is
/// returned — `notify::RecommendedWatcher` picks the platform backend
/// internally (inotify on Linux).
pub fn default() -> Arc<dyn Watcher> {
    default_watcher()
}

/// `Kqueue` returns the kqueue watcher in Go.
///
/// PORT: there is no selectable backend; `kqueue` returns the same
/// `notify`-backed watcher as [`default`]. `notify` chooses the platform
/// backend itself (it never selects kqueue on macOS by default).
pub fn kqueue() -> Arc<dyn Watcher> {
    default()
}

static DEFAULT_WATCHER: OnceLock<Arc<NotifyWatcher>> = OnceLock::new();

/// The package-level watcher instance Go stores in `inotifyWatcher` et al.
fn default_watcher() -> Arc<NotifyWatcher> {
    DEFAULT_WATCHER
        .get_or_init(|| Arc::new(NotifyWatcher::new()))
        .clone()
}

// ----- path helpers (watcher.go + pathcompare.go, exact-comparer subset) ----

/// `filepath.Clean` (POSIX spelling): lexically resolves `.`/`..` segments,
/// collapses repeated separators, strips a trailing separator. `tspath`'s
/// `normalize_path` is close but preserves trailing separators and converts
/// `\` to `/` — the latter is wrong on POSIX where `\` is a valid filename
/// byte.
fn clean_path(path: &str) -> String {
    if path.is_empty() {
        return ".".to_owned();
    }
    let rooted = path.starts_with('/');
    let mut out: Vec<&str> = Vec::new();
    for seg in path.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                if out.last().is_some_and(|&s| s != "..") {
                    out.pop();
                } else if !rooted {
                    out.push("..");
                }
            }
            s => out.push(s),
        }
    }
    let mut result = String::new();
    if rooted {
        result.push('/');
    }
    result.push_str(&out.join("/"));
    if result.is_empty() {
        result.push('.');
    }
    result
}

/// `filepath.IsAbs`.
fn path_is_absolute(path: &str) -> bool {
    Path::new(path).is_absolute()
}

/// `filepath.Dir` for a cleaned absolute path.
fn dir_name(path: &str) -> String {
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        // `filepath.Dir("/") == "/"`; `filepath.Dir("") == "."`.
        return if path.starts_with('/') {
            "/".to_owned()
        } else {
            ".".to_owned()
        };
    }
    match trimmed.rfind('/') {
        Some(0) => "/".to_owned(),
        Some(i) => trimmed[..i].to_owned(),
        None => ".".to_owned(),
    }
}

/// `canonicalizePath` is a no-op on platforms whose watchers report paths
/// using the same bytes the caller provided (everything but Darwin FSEvents).
fn canonicalize_path(path: &str) -> String {
    path.to_owned()
}

/// `physicalDirFor` returns the physical path to watch for `dir`. If `dir`,
/// or an ancestor of `dir`, is a symlink or reparse point, events are
/// subscribed on its realpath while callbacks still use `dir`.
fn physical_dir_for(dir: &str) -> String {
    match tsc_nativepath::realpath(dir) {
        Ok(realpath) if realpath != dir => canonicalize_path(&clean_path(&realpath)),
        _ => dir.to_owned(),
    }
}

/// `os.IsPathSeparator`.
fn is_path_separator(c: char) -> bool {
    c == '/' || (cfg!(windows) && c == '\\')
}

/// `rebasePath` replaces the `from` root in `path` with `to`, preserving any
/// child suffix. Prefix matches must end at a path separator so sibling
/// paths like "/foo2" are not rebased from "/foo".
fn rebase_path(path: &str, from: &str, to: &str) -> String {
    if from == to {
        return path.to_owned();
    }
    if path == from {
        return to.to_owned();
    }
    if !path.starts_with(from) {
        return path.to_owned();
    }
    let suffix = &path[from.len()..];
    if !from.is_empty() && from.ends_with(is_path_separator) {
        return join_path_suffix(to, suffix);
    }
    if suffix.is_empty() || !suffix.starts_with(is_path_separator) {
        return path.to_owned();
    }
    join_path_suffix(to, suffix)
}

/// `joinPathSuffix`.
fn join_path_suffix(root: &str, suffix: &str) -> String {
    if suffix.is_empty() {
        return root.to_owned();
    }
    if suffix.starts_with(is_path_separator) {
        if !root.is_empty() && root.ends_with(is_path_separator) {
            return format!("{}{}", root, &suffix[1..]);
        }
        return format!("{root}{suffix}");
    }
    if !root.is_empty() && root.ends_with(is_path_separator) {
        return format!("{root}{suffix}");
    }
    format!("{root}{}{}", std::path::MAIN_SEPARATOR, suffix)
}

/// `isInDirectoryOrSelf`.
pub(crate) fn is_in_directory_or_self(dir: &str, path: &str) -> bool {
    if dir.is_empty() {
        return false;
    }
    if path == dir {
        return true;
    }
    if !path.starts_with(dir) {
        return false;
    }
    let rest = &path[dir.len()..];
    if rest.is_empty() {
        return false;
    }
    if dir.ends_with(is_path_separator) {
        return true;
    }
    rest.starts_with(is_path_separator)
}

/// `isDirectChild` reports whether `path` is an immediate child of `dir`.
/// Returns false for `path == dir`.
pub(crate) fn is_direct_child(dir: &str, path: &str) -> bool {
    let Some(rest) = path.strip_prefix(dir) else {
        return false;
    };
    if rest.is_empty() {
        return false;
    }
    if !rest.starts_with(is_path_separator) {
        return false;
    }
    let rest = &rest[1..];
    !rest.is_empty() && !rest.chars().any(is_path_separator)
}

/// `suffixOf` — the exact-comparer half of `pathComparer.suffixPrepared`:
/// returns `path` below `root` when `root` is `path` or a directory-prefix
/// of it.
fn suffix_of<'a>(root: &str, path: &'a str) -> Option<&'a str> {
    if is_in_directory_or_self(root, path) {
        Some(&path[root.len()..])
    } else {
        None
    }
}
