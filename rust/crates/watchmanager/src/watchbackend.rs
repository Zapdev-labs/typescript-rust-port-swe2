// Ported from tsc/internal/execute/watchmanager/watchbackend.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_fswatch::{self as fswatch, Event, WatchOption};
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedPath};

use crate::watchmanager::WatchEvent;

/// `WatchBackend` abstracts `fswatch.Watcher` for testing.
///
/// PORT: Go returns `[]io.Closer`; the closers become boxed [`WatchHandle`]s
/// (`fswatch::Watch` implements it; test backends return no-ops). Go's
/// `error` result is `fswatch::Error`, the only backend error domain.
pub trait WatchBackend: Send + Sync {
    /// `WatchDirectories(requests)`.
    fn watch_directories(
        &self,
        requests: Vec<WatchDirectoryRequest>,
    ) -> Result<Vec<Box<dyn WatchHandle>>, fswatch::Error>;
}

/// `io.Closer` for a live watch.
pub trait WatchHandle: Send + Sync {
    /// `Close()` — idempotent; errors are discarded like Go's call sites do.
    fn close(&self);
}

impl WatchHandle for fswatch::Watch {
    fn close(&self) {
        let _ = fswatch::Watch::close(self);
    }
}

/// `WatchCallback` — receives batched events (`err` is `None` on success,
/// Go's nil error).
pub type WatchCallback = Arc<dyn Fn(Vec<WatchEvent>, Option<fswatch::Error>) + Send + Sync>;

/// `func(tspath.RootedPath) bool` — drop events for ignored paths.
pub type WatchIgnore = Arc<dyn Fn(&RootedPath) -> bool + Send + Sync>;

/// `WatchDirectoryRequest`.
pub struct WatchDirectoryRequest {
    /// `Dir`.
    pub dir: RootedDirectoryPath,
    /// `Callback`.
    pub callback: WatchCallback,
    /// `Recursive`.
    pub recursive: bool,
    /// `Ignore` — `None` is Go's nil function.
    pub ignore: Option<WatchIgnore>,
}

/// `CommandLineTestingWithWatchBackend` is an optional extension of
/// `CommandLineTesting` that supplies a [`WatchBackend`] for test mode.
pub trait CommandLineTestingWithWatchBackend {
    /// `WatchBackend()`.
    fn watch_backend(&self) -> Arc<dyn WatchBackend>;
}

/// `FSWatchBackend{Inner}`.
pub struct FsWatchBackend {
    /// `Inner`.
    pub inner: Arc<dyn fswatch::Watcher>,
}

impl WatchBackend for FsWatchBackend {
    fn watch_directories(
        &self,
        requests: Vec<WatchDirectoryRequest>,
    ) -> Result<Vec<Box<dyn WatchHandle>>, fswatch::Error> {
        let fswatch_requests: Vec<fswatch::WatchDirectoryRequest> = requests
            .into_iter()
            .map(|request| {
                let mut options: Vec<WatchOption> = Vec::new();
                if request.recursive {
                    options.push(fswatch::with_recursive());
                }
                if let Some(ignore) = request.ignore {
                    options.push(fswatch::with_ignore(move |path: &str| {
                        ignore(&tspath::rooted_path_from_absolute(path))
                    }));
                }
                let callback = request.callback;
                fswatch::WatchDirectoryRequest {
                    dir: request.dir.as_string().to_owned(),
                    callback: Some(Arc::new(
                        move |events: Vec<Event>, err: Option<fswatch::Error>| {
                            let typed_events: Vec<WatchEvent> = events
                                .into_iter()
                                .map(|event| WatchEvent {
                                    path: tspath::rooted_path_from_absolute(&event.path),
                                    kind: event.kind,
                                })
                                .collect();
                            callback(typed_events, err);
                        },
                    )),
                    options,
                }
            })
            .collect();
        let watches = self.inner.watch_directories(fswatch_requests)?;
        Ok(watches
            .into_iter()
            .map(|watch| Box::new(watch) as Box<dyn WatchHandle>)
            .collect())
    }
}

/// `ShouldIgnoreWatchPath`.
pub fn should_ignore_watch_path(path: &RootedPath) -> bool {
    let text = path.as_string();
    text.ends_with("/.git")
        || text.contains("/.git/")
        || text.contains("/node_modules/.")
        || text.contains("/.#")
}

/// `CanWatchDirectory`.
pub fn can_watch_directory(dir: &RootedDirectoryPath) -> bool {
    let components = dir.components();
    let length = components.len();
    if length <= 2 {
        return false;
    }
    let root_length = perceived_os_root_length_for_watching(&components);
    length > root_length + 1
}

/// `PerceivedOsRootLengthForWatching`.
pub fn perceived_os_root_length_for_watching(components: &[String]) -> usize {
    let length = components.len();
    if length <= 1 {
        return 1;
    }
    let root = &components[0];
    let mut index_after_os_root = 1;
    let root_bytes = root.as_bytes();
    let mut is_dos_style = root_bytes.len() >= 2
        && tspath::is_volume_character(root_bytes[0])
        && root_bytes[1] == b':';

    if root != "/" && !is_dos_style && length > 1 {
        let c1 = components[1].as_bytes();
        if c1.len() >= 2 && tspath::is_volume_character(c1[0]) && components[1].ends_with('$') {
            if length == 2 {
                return 2;
            }
            index_after_os_root = 2;
            is_dos_style = true;
        }
    }

    // `strings.EqualFold(x, "users")` — ASCII-insensitive is equivalent for
    // an ASCII needle except for exotic fold-into-ASCII runes.
    if is_dos_style
        && (index_after_os_root >= length
            || !components[index_after_os_root].eq_ignore_ascii_case("users"))
    {
        return index_after_os_root;
    }

    if index_after_os_root < length
        && components[index_after_os_root].eq_ignore_ascii_case("workspaces")
    {
        return index_after_os_root + 1;
    }

    index_after_os_root + 2
}
