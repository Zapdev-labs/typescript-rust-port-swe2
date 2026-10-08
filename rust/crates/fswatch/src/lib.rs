// tsc-fswatch — port of tsc/internal/fswatch @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Filesystem watching for `tsc --watch` and the LSP watcher. Ports the
// consumed API surface of Go's `fswatch` package: the `Watcher` trait
// (`watch_directory`/`watch_directories`/`watch_file`), `Watch` handles,
// `Event`/`EventKind`, `WatchDirectoryRequest`, `WatchOption`s
// (`with_recursive`, `with_ignore`), the `ERR_OVERFLOW`/`ERR_WATCH_TERMINATED`
// error sentinels, and `debounce.go`'s event coalescing semantics.
//
// PORT: Go's hand-rolled syscall backends (inotify/fanotify on Linux,
// FSEvents via FFI on macOS, kqueue on BSDs, ReadDirectoryChangesW on
// Windows) are replaced by the `notify` crate's `RecommendedWatcher`. See
// `notify_backend.rs` and PORTING-NOTES.md for the deviation details.

mod debounce;
mod error;
mod event;
mod notify_backend;
mod watcher;

#[cfg(test)]
mod fswatch_test;

pub use error::{
    ERR_FILESYSTEM_UNSUPPORTED, ERR_OVERFLOW, ERR_UNAVAILABLE, ERR_WATCH_TERMINATED, Error,
};
pub use event::{Event, EventKind};
pub use watcher::{
    IgnoreFn, Watch, WatchCallback, WatchDirectoryRequest, WatchOption, Watcher, default, kqueue,
    with_ignore, with_recursive,
};
