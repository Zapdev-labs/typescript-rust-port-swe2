// Ported from tsc/internal/fswatch/watcher.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! Error type for fswatch. Go's sentinel `error` values become unit variants;
//! `fmt.Errorf("...: %w", err)` becomes `Wrapped`, `errors.Join` becomes
//! `Joined`. Use [`Error::is`] where Go would use `errors.Is`.

use std::fmt;
use std::io;
use std::sync::Arc;

/// `ErrOverflow` — the kernel event queue overflowed and some filesystem
/// changes were missed. The watch remains active; further events will
/// continue to be delivered. Callers should treat this as a signal to
/// rescan the watched directory.
pub const ERR_OVERFLOW: Error = Error::Overflow;

/// `ErrWatchTerminated` — the watch was terminated due to an unrecoverable
/// error (e.g. the watched directory was deleted or the watch descriptor was
/// revoked). No further events will be delivered. Close the watch to release
/// remaining state.
pub const ERR_WATCH_TERMINATED: Error = Error::WatchTerminated;

/// `ErrUnavailable` — a requested watcher is not available on the current
/// platform.
pub const ERR_UNAVAILABLE: Error = Error::Unavailable;

/// `ErrFilesystemUnsupported` — the active watcher backend cannot operate on
/// the target filesystem, even though the backend is available on the current
/// platform.
// PORT: fanotify-only in Go; the notify backend never produces this, but the
// sentinel is kept for API parity.
pub const ERR_FILESYSTEM_UNSUPPORTED: Error = Error::FilesystemUnsupported;

/// fswatch error. Go's sentinel `error` values become unit variants;
/// `fmt.Errorf("...: %w", err)` becomes `Wrapped`, `errors.Join` becomes
/// `Joined`. Use [`Error::is`] where Go would use `errors.Is`.
///
/// `Clone` is provided because Go shares the error value across subscribers
/// and also returns it; leaves that cannot be cloned are `Arc`-wrapped.
#[derive(Debug, Clone)]
pub enum Error {
    /// `ErrOverflow`.
    Overflow,
    /// `ErrWatchTerminated`.
    WatchTerminated,
    /// `ErrUnavailable`.
    Unavailable,
    /// `ErrFilesystemUnsupported`.
    FilesystemUnsupported,
    /// `errNilCallback` — "fswatch: callback must not be nil".
    NilCallback,
    /// `errRootPath` — "fswatch: cannot watch a root path".
    RootPath,
    /// `errNotAbsolute` — "fswatch: path must be absolute".
    NotAbsolute,
    /// A `notify` backend failure (`watcherImpl` internals).
    Notify(Arc<notify::Error>),
    /// An `io` failure (`os.Stat`, `realpath`, ENOTDIR equivalents).
    Io(Arc<io::Error>),
    /// `errors.New` / `fmt.Errorf` without `%w` — a plain message.
    Message(String),
    /// `fmt.Errorf("...: %w", err)` — `msg` is the fully rendered message
    /// (matching Go's `Error()` output); `source` is the wrapped error.
    Wrapped {
        /// The rendered `fmt.Errorf` message.
        msg: String,
        /// The `%w` operand.
        source: Box<Error>,
    },
    /// `errors.Join(a, b)` — Display renders each operand on its own line,
    /// as Go's `joinError.Error()` does.
    Joined(Box<Error>, Box<Error>),
}

impl Error {
    /// `fmt.Errorf("{msg}: %w", source)` — `msg` must already contain the
    /// rendered source text where `%w` appeared.
    pub(crate) fn wrapped(msg: impl Into<String>, source: Error) -> Error {
        Error::Wrapped {
            msg: msg.into(),
            source: Box::new(source),
        }
    }

    /// `errors.Is(err, target)`. Go compares the error value itself (pointer
    /// identity for sentinels) then walks `Unwrap`; here leaf variants compare
    /// by value and `Wrapped`/`Joined` recurse into their source chain.
    pub fn is(&self, target: &Error) -> bool {
        match self {
            // `errors.Join` — Is checks each operand.
            Error::Joined(a, b) => a.is(target) || b.is(target),
            // `fmt.wrapError` — never equal to the target itself; unwrap.
            Error::Wrapped { source, .. } => source.is(target),
            _ => self.leaf_eq(target),
        }
    }

    /// Value equality for non-wrapping variants — the `err == target` half of
    /// `errors.Is`.
    fn leaf_eq(&self, target: &Error) -> bool {
        match (self, target) {
            (Error::Overflow, Error::Overflow)
            | (Error::WatchTerminated, Error::WatchTerminated)
            | (Error::Unavailable, Error::Unavailable)
            | (Error::FilesystemUnsupported, Error::FilesystemUnsupported)
            | (Error::NilCallback, Error::NilCallback)
            | (Error::RootPath, Error::RootPath)
            | (Error::NotAbsolute, Error::NotAbsolute) => true,
            (Error::Message(a), Error::Message(b)) => a == b,
            (Error::Io(a), Error::Io(b)) => a.kind() == b.kind() && a.to_string() == b.to_string(),
            (Error::Notify(a), Error::Notify(b)) => a.to_string() == b.to_string(),
            _ => false,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Overflow => f.write_str("fswatch: event overflow; some changes were missed"),
            Error::WatchTerminated => f.write_str("fswatch: watch terminated"),
            Error::Unavailable => f.write_str("fswatch: watcher not available on this platform"),
            Error::FilesystemUnsupported => {
                f.write_str("fswatch: watcher backend unsupported on this filesystem")
            }
            Error::NilCallback => f.write_str("fswatch: callback must not be nil"),
            Error::RootPath => f.write_str("fswatch: cannot watch a root path"),
            Error::NotAbsolute => f.write_str("fswatch: path must be absolute"),
            Error::Notify(e) => e.fmt(f),
            Error::Io(e) => e.fmt(f),
            Error::Message(m) => f.write_str(m),
            Error::Wrapped { msg, .. } => f.write_str(msg),
            Error::Joined(a, b) => write!(f, "{a}\n{b}"),
        }
    }
}

impl std::error::Error for Error {}
