// Ported from tsc/internal/project/logging/logcollector.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::io;
use std::sync::{Arc, Mutex};
use std::time::{Duration, UNIX_EPOCH};

use crate::logger::{Logger, LoggerInner, PrefixFn, WriterLogger};
use crate::timefmt::format_time;

/// `strings.Builder` as an `io.Writer` — everything written is retained for
/// `String()`.
struct SharedBuf(Arc<Mutex<Vec<u8>>>);

impl io::Write for SharedBuf {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `logCollector` — the `Logger` returned by `NewTestLogger()`: writes to an
/// in-memory buffer, retrievable via `Display` (`String()`).
pub struct TestLogger {
    inner: Mutex<LoggerInner>,
    prefix: PrefixFn,
    buf: Arc<Mutex<Vec<u8>>>,
}

impl fmt::Display for TestLogger {
    /// `String()` — the accumulated log output.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let buf = self.buf.lock().unwrap();
        f.write_str(&String::from_utf8_lossy(&buf))
    }
}

impl Logger for TestLogger {
    fn log(&self, msg: fmt::Arguments) {
        WriterLogger::write_log(&self.inner, &self.prefix, msg);
    }

    fn logf(&self, args: fmt::Arguments) {
        WriterLogger::write_logf(&self.inner, &self.prefix, args);
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

/// `NewTestLogger()` — a [`TestLogger`] with the fixed timestamp prefix
/// `formatTime(time.Unix(1349085672, 0))`.
pub fn new_test_logger() -> TestLogger {
    let buf = Arc::new(Mutex::new(Vec::new()));
    TestLogger {
        inner: Mutex::new(LoggerInner {
            verbose: false,
            writer: Box::new(SharedBuf(Arc::clone(&buf))),
        }),
        prefix: Arc::new(|| format_time(UNIX_EPOCH + Duration::from_secs(1_349_085_672))),
        buf,
    }
}
