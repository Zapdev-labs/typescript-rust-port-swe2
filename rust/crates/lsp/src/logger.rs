// Ported from tsc/internal/lsp @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `logger.server *Server` → `Weak<Server>`: `Server` owns the logger, so
//   the back-pointer is weak to avoid an `Arc` cycle (same pattern as
//   `LogTree`'s `root`). `new_logger` takes the `Weak` so the server can
//   build it inside `Arc::new_cyclic`.
// - `mu sync.Mutex` + `verbosity` → a single `Mutex<LogVerbosity>`;
//   `initStarted.Load()` → `AtomicBool::load(Ordering::Acquire)`;
//   `ctx.Err() != nil` → `Context::is_cancelled()` (repo conventions).
// - Go's nil-receiver methods (`if l == nil { return }`) map to
//   `Option<Logger>` at call sites (`if let Some(l) = ...`); every method
//   here assumes a live `self`. `Verbose()`'s nil return is already
//   `Option<&dyn Logger>` on the `tsc_project_logging::Logger` trait.
// - `msg ...any` / `format, args...` collapse to `fmt::Arguments`
//   (`format_args!`), matching the `tsc_project_logging::Logger` port
//   shape; `fmt.Sprint`/`fmt.Sprintf` both arrive pre-formatted.
// - `error`/`warn`/`info` (and the `f` variants) override the trait
//   defaults — Go's versions send distinct `MessageType`s rather than
//   delegating to `log`.
//
// PORT(sibling): this file expects the `crate::server::Server` port to
// expose `init_started: AtomicBool`,
// `stderr: Mutex<Box<dyn io::Write + Send>>`,
// `outgoing_queue` — a `put(&Context, lsproto::Message) -> Result` port of
// `dynamic_queue.go`'s `dynamicQueue[*lsproto.Message]` — and
// `background_ctx: tsc_core::context::Context`. Reconcile with the sibling
// server.rs/dynamic_queue.rs ports.

use std::fmt;
use std::io::Write as _;
use std::sync::atomic::Ordering;
use std::sync::{Mutex, Weak};

use tsc_lsproto as lsproto;
use tsc_project_logging::Logger as ProjectLogger;

use crate::server::Server;

/// `type logger struct` — the `logging.Logger` implementation that forwards
/// to the client's `window/logMessage` notification (stderr until
/// initialization starts).
pub(crate) struct Logger {
    server: Weak<Server>,
    /// `mu sync.Mutex` + `verbosity lsproto.LogVerbosity`.
    verbosity: Mutex<lsproto::LogVerbosity>,
}

/// `func newLogger(server *Server) *logger`
pub(crate) fn new_logger(server: Weak<Server>) -> Logger {
    Logger {
        server,
        verbosity: Mutex::new(lsproto::LogVerbosity::Info),
    }
}

/// `func maxVerbosityForMessageType(msgType lsproto.MessageType) lsproto.LogVerbosity`
///
/// Returns the least-verbose log level at which messages of the given LSP
/// MessageType should still be sent.
fn max_verbosity_for_message_type(msg_type: lsproto::MessageType) -> lsproto::LogVerbosity {
    match msg_type {
        lsproto::MessageType::Error => lsproto::LogVerbosity::Error,
        lsproto::MessageType::Warning => lsproto::LogVerbosity::Warning,
        lsproto::MessageType::Info => lsproto::LogVerbosity::Info,
        lsproto::MessageType::Debug => lsproto::LogVerbosity::Debug,
        _ => lsproto::LogVerbosity::Info,
    }
}

/// `func isValidLogVerbosity(v lsproto.LogVerbosity) bool`
///
/// Reports whether `v` is one of the defined LogVerbosity values.
pub(crate) fn is_valid_log_verbosity(v: lsproto::LogVerbosity) -> bool {
    v >= lsproto::LogVerbosity::Off && v <= lsproto::LogVerbosity::Error
}

/// `fmt.Fprintln(l.server.stderr, message)`.
fn write_stderr(server: &Server, message: &str) {
    let _ = writeln!(server.stderr.lock().unwrap(), "{message}");
}

impl Logger {
    /// `func (l *logger) sendLogMessage(msgType lsproto.MessageType, message string)`
    fn send_log_message(&self, msg_type: lsproto::MessageType, message: fmt::Arguments) {
        // Go nil receiver (`if l == nil`): unreachable through the
        // `Option<Logger>` call sites.
        let Some(server) = self.server.upgrade() else {
            return;
        };

        if !server.init_started.load(Ordering::Acquire) {
            write_stderr(&server, &message.to_string());
            return;
        }

        // Don't send messages that the client will filter out anyway.
        let verbosity = *self.verbosity.lock().unwrap();
        if verbosity == lsproto::LogVerbosity::Off
            || verbosity > max_verbosity_for_message_type(msg_type)
        {
            return;
        }

        let message = message.to_string();
        let notification =
            lsproto::WINDOW_LOG_MESSAGE_INFO.new_notification_message(Some(
                lsproto::LogMessageParams {
                    type_: msg_type,
                    message: message.clone(),
                },
            ));

        if server
            .outgoing_queue
            .put(&server.background_ctx, notification.message())
            .is_err()
            && server.background_ctx.is_cancelled()
        {
            write_stderr(&server, &message);
        }
    }

    /// `func (l *logger) IsTracing() bool` — an extra `*logger` method, not
    /// part of `logging.Logger`.
    pub(crate) fn is_tracing(&self) -> bool {
        *self.verbosity.lock().unwrap() == lsproto::LogVerbosity::Trace
    }

    /// `func (l *logger) SetVerbosity(verbosity lsproto.LogVerbosity)` — an
    /// extra `*logger` method, not part of `logging.Logger`.
    pub(crate) fn set_verbosity(&self, verbosity: lsproto::LogVerbosity) {
        *self.verbosity.lock().unwrap() = verbosity;
    }
}

impl ProjectLogger for Logger {
    /// `func (l *logger) Log(msg ...any)`
    fn log(&self, msg: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Info, msg);
    }

    /// `func (l *logger) Logf(format string, args ...any)`
    fn logf(&self, args: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Info, args);
    }

    /// `func (l *logger) Verbose() logging.Logger`
    fn verbose(&self) -> Option<&dyn ProjectLogger> {
        let verbosity = *self.verbosity.lock().unwrap();
        if verbosity == lsproto::LogVerbosity::Off || verbosity > lsproto::LogVerbosity::Debug {
            return None;
        }
        Some(self)
    }

    /// `func (l *logger) IsVerbose() bool`
    fn is_verbose(&self) -> bool {
        let verbosity = *self.verbosity.lock().unwrap();
        verbosity >= lsproto::LogVerbosity::Trace && verbosity <= lsproto::LogVerbosity::Debug
    }

    /// `func (l *logger) SetVerbose(verbose bool)`
    fn set_verbose(&self, verbose: bool) {
        *self.verbosity.lock().unwrap() = if verbose {
            lsproto::LogVerbosity::Debug
        } else {
            lsproto::LogVerbosity::Info
        };
    }

    /// `func (l *logger) Error(msg ...any)`
    fn error(&self, msg: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Error, msg);
    }

    /// `func (l *logger) Errorf(format string, args ...any)`
    fn errorf(&self, args: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Error, args);
    }

    /// `func (l *logger) Warn(msg ...any)`
    fn warn(&self, msg: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Warning, msg);
    }

    /// `func (l *logger) Warnf(format string, args ...any)`
    fn warnf(&self, args: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Warning, args);
    }

    /// `func (l *logger) Info(msg ...any)`
    fn info(&self, msg: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Info, msg);
    }

    /// `func (l *logger) Infof(format string, args ...any)`
    fn infof(&self, args: fmt::Arguments) {
        self.send_log_message(lsproto::MessageType::Info, args);
    }
}
