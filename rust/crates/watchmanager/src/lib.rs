// tsc-watchmanager — port of tsc/internal/execute/watchmanager @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Manages fswatch directory watches, event accumulation, and DoCycle
// signaling for `tsc --watch` and build mode. `WatchBackend` abstracts the
// watcher for tests; `FsWatchBackend` adapts `tsc_fswatch::Watcher`.
//
// PORT notes:
// - Go's `sync.Mutex` pair (`mu`, `changedMu`) becomes `Mutex<Inner>` +
//   `Mutex<ChangedState>`; `wm.Lock/Unlock` becomes [`WatchManager::lock`]'s
//   guard, which exposes the locked-region operations.
// - The `doCycleCh chan struct{}` (cap 1, non-blocking send) becomes an
//   `mpsc::sync_channel(1)` + `try_send`; `RunLoop`'s `select` on
//   `ctx.Done()` becomes a `recv_timeout` poll (see `run_loop`).
// - `io.Closer`/`io.Writer` become `WatchHandle`/`Box<dyn io::Write + Send>`.

mod watchbackend;
mod watchmanager;

#[cfg(test)]
mod watchmanager_test;

pub use watchbackend::{
    CommandLineTestingWithWatchBackend, FsWatchBackend, WatchBackend, WatchCallback,
    WatchDirectoryRequest, WatchHandle, WatchIgnore, can_watch_directory,
    perceived_os_root_length_for_watching, should_ignore_watch_path,
};
pub use watchmanager::{
    DirWatchSet, WatchEvent, WatchManager, WatchManagerLock, new_dir_watch_set, new_watch_manager,
};
