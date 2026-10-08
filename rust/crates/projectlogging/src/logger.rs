// Ported from tsc/internal/project/logging/logger.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::io;
use std::io::Write as _;
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use crate::timefmt::format_time;

/// `Logger` — Go's `logging.Logger` interface.
///
/// PORT: `Log/Logf` and friends take `std::fmt::Arguments` — call sites use
/// `format_args!(...)`. Go's `...any` parameters collapse to a single
/// pre-formatted message (consumers already format their arguments), and
/// `%v`-style verbs map to `{}` — log output is diagnostic, not
/// spec-constrained.
///
/// `Verbose()` returning a nil-able `Logger` becomes `Option<&dyn Logger>`;
/// `None` is the Go nil logger, whose methods were safe no-ops — call sites
/// should do `if let Some(v) = logger.verbose() { ... }`. [`NopLogger`]
/// plays the role of `NewNopLogger()`'s typed-nil result.
pub trait Logger: Send + Sync {
    /// `Log(msg ...any)` — prints a line with the logger's header prefix.
    fn log(&self, msg: fmt::Arguments);
    /// `Logf(format, args...)`.
    fn logf(&self, args: fmt::Arguments);

    /// `Error(msg ...any)` — Go delegates to `Log`.
    fn error(&self, msg: fmt::Arguments) {
        self.log(msg);
    }
    /// `Errorf(format, args...)`.
    fn errorf(&self, args: fmt::Arguments) {
        self.logf(args);
    }
    /// `Warn(msg ...any)`.
    fn warn(&self, msg: fmt::Arguments) {
        self.log(msg);
    }
    /// `Warnf(format, args...)`.
    fn warnf(&self, args: fmt::Arguments) {
        self.logf(args);
    }
    /// `Info(msg ...any)`.
    fn info(&self, msg: fmt::Arguments) {
        self.log(msg);
    }
    /// `Infof(format, args...)`.
    fn infof(&self, args: fmt::Arguments) {
        self.logf(args);
    }

    /// `Verbose()` — `Some` iff verbose logging is enabled (`None` is Go's
    /// nil logger).
    fn verbose(&self) -> Option<&dyn Logger>;
    /// `IsVerbose()`.
    fn is_verbose(&self) -> bool;
    /// `SetVerbose(verbose)`.
    fn set_verbose(&self, verbose: bool);
}

/// `LogCollector` — Go's `fmt.Stringer + Logger` interface.
pub trait LogCollector: Logger + fmt::Display {}

impl<T: Logger + fmt::Display> LogCollector for T {}

pub(crate) struct LoggerInner {
    pub(crate) verbose: bool,
    pub(crate) writer: Box<dyn io::Write + Send>,
}

pub(crate) type PrefixFn = Arc<dyn Fn() -> String + Send + Sync>;

/// `logger` — the `io.Writer`-backed implementation returned by `NewLogger`.
pub struct WriterLogger {
    pub(crate) inner: Mutex<LoggerInner>,
    pub(crate) prefix: PrefixFn,
}

impl WriterLogger {
    /// Shared `Log` body (also used by `TestLogger`).
    pub(crate) fn write_log(inner: &Mutex<LoggerInner>, prefix: &PrefixFn, msg: fmt::Arguments) {
        let mut guard = inner.lock().unwrap();
        let _ = writeln!(guard.writer, "{} {}", (prefix)(), msg);
    }

    /// Shared `Logf` body.
    pub(crate) fn write_logf(inner: &Mutex<LoggerInner>, prefix: &PrefixFn, args: fmt::Arguments) {
        let mut guard = inner.lock().unwrap();
        let _ = writeln!(guard.writer, "{} {}", (prefix)(), args);
    }
}

impl Logger for WriterLogger {
    fn log(&self, msg: fmt::Arguments) {
        Self::write_log(&self.inner, &self.prefix, msg);
    }

    fn logf(&self, args: fmt::Arguments) {
        Self::write_logf(&self.inner, &self.prefix, args);
    }

    fn verbose(&self) -> Option<&dyn Logger> {
        if !self.inner.lock().unwrap().verbose {
            return None;
        }
        Some(self)
    }

    fn is_verbose(&self) -> bool {
        self.inner.lock().unwrap().verbose
    }

    fn set_verbose(&self, verbose: bool) {
        self.inner.lock().unwrap().verbose = verbose;
    }
}

/// `NewLogger(output)` — a [`Logger`] writing prefixed lines to `output`.
pub fn new_logger(output: Box<dyn io::Write + Send>) -> WriterLogger {
    WriterLogger {
        inner: Mutex::new(LoggerInner {
            verbose: false,
            writer: output,
        }),
        prefix: Arc::new(|| format_time(SystemTime::now())),
    }
}

/// `NewNopLogger()` — a no-op [`Logger`] that discards everything and is
/// never verbose. Go returns a typed-nil `*logger` whose methods all no-op;
/// here every method is an explicit no-op.
#[derive(Debug, Default, Clone, Copy)]
pub struct NopLogger;

/// `NewNopLogger()`.
pub fn new_nop_logger() -> NopLogger {
    NopLogger
}

impl Logger for NopLogger {
    fn log(&self, _msg: fmt::Arguments) {}
    fn logf(&self, _args: fmt::Arguments) {}
    fn verbose(&self) -> Option<&dyn Logger> {
        None
    }
    fn is_verbose(&self) -> bool {
        false
    }
    fn set_verbose(&self, _verbose: bool) {}
}
