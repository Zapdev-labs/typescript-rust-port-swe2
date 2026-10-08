// Ported from tsc/internal/project/logging/logtree.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, Weak};
use std::time::SystemTime;

use crate::logger::Logger;
use crate::timefmt::format_time;

/// `var seq atomic.Uint64` — a process-wide sequence for log entries.
static SEQ: AtomicU64 = AtomicU64::new(0);

/// `logEntry` — one log line plus an optional embedded/forked child tree.
struct LogEntry {
    #[allow(dead_code)] // `seq` is recorded for fidelity; Go never reads it either.
    seq: u64,
    time: SystemTime,
    message: String,
    child: Option<LogTree>,
}

fn new_log_entry(child: Option<LogTree>, message: String) -> LogEntry {
    LogEntry {
        seq: SEQ.fetch_add(1, Ordering::Relaxed) + 1,
        time: SystemTime::now(),
        message,
        child,
    }
}

struct LogTreeInner {
    name: String,
    logs: Mutex<Vec<LogEntry>>,
    /// `root` — `Weak` so the root can drop once no `LogTree` handles remain.
    /// Go keeps the root alive through the child's strong pointer; on
    /// upgrade failure here the counter update is skipped while the log is
    /// still appended (the counters only size `String()`'s buffer).
    root: Weak<LogTreeInner>,
    is_root: bool,
    level: i32,
    /// `verbose` is a plain bool in Go (unsynchronized reads and writes);
    /// `AtomicBool` preserves the semantics without a data race.
    verbose: AtomicBool,

    // Only written through `root` (i.e. only populated on the root node):
    // `Embed`/`String` read them off `self` exactly like Go reads
    // `logs.count`/`c.stringLength`, which are zero on non-root trees.
    count: AtomicI32,
    string_length: AtomicI32,
}

impl LogTreeInner {
    /// `c.add(log)`.
    fn add(&self, log: LogEntry) {
        // indent + header + message + newline
        if let Some(root) = self.root.upgrade() {
            root.string_length
                .fetch_add(self.level + 15 + log.message.len() as i32 + 1, Ordering::Relaxed);
            root.count.fetch_add(1, Ordering::Relaxed);
        }
        self.logs.lock().unwrap().push(log);
    }

    fn write_logs_recursive(&self, builder: &mut String, indent: &str) {
        for log in self.logs.lock().unwrap().iter() {
            builder.push_str(indent);
            builder.push_str(&format_time(log.time));
            builder.push(' ');
            builder.push_str(&log.message);
            builder.push('\n');
            if let Some(child) = &log.child {
                if let Some(inner) = &child.0 {
                    inner.write_logs_recursive(builder, &format!("{indent}\t"));
                }
            }
        }
    }
}

/// `LogTree` — a tree-shaped `LogCollector` implementing [`Logger`].
///
/// PORT: Go's `*LogTree` is nil-able and every method tolerates (or
/// deliberately panics on) a nil receiver — here `LogTree` is an
/// `Option<Arc>` handle; [`LogTree::none`] is the Go nil. `Clone` shares the
/// node, like Go copying the pointer.
#[derive(Clone)]
pub struct LogTree(Option<Arc<LogTreeInner>>);

impl LogTree {
    /// Go's nil `*LogTree` — all methods are safe no-ops, exactly like Go.
    pub const fn none() -> LogTree {
        LogTree(None)
    }

    /// `NewLogTree(name)`.
    pub fn new_log_tree(name: String) -> LogTree {
        LogTree(Some(Arc::new_cyclic(|me| LogTreeInner {
            name,
            logs: Mutex::new(Vec::new()),
            root: me.clone(),
            is_root: true,
            level: 0,
            verbose: AtomicBool::new(false),
            count: AtomicI32::new(0),
            string_length: AtomicI32::new(0),
        })))
    }

    /// `c.Embed(logs)` — appends `logs` as a nested child entry.
    ///
    /// PORT: reads `logs`'s OWN `count`/`stringLength` like Go — which are
    /// zero on non-root trees (only the root's counters are incremented by
    /// `add`). A nil `logs` panics, like Go's nil field access.
    pub fn embed(&self, logs: &LogTree) {
        let Some(inner) = &self.0 else {
            return;
        };
        let logs_inner = logs.0.as_ref().expect("Embed on nil LogTree");
        let count = logs_inner.count.load(Ordering::Relaxed);
        if let Some(root) = inner.root.upgrade() {
            root.string_length.fetch_add(
                logs_inner.string_length.load(Ordering::Relaxed) + count * inner.level,
                Ordering::Relaxed,
            );
            root.count.fetch_add(count, Ordering::Relaxed);
        }
        let log = new_log_entry(Some(logs.clone()), logs_inner.name.clone());
        inner.add(log);
    }

    /// `c.Fork(message)` — creates a child node and logs `message` linking
    /// to it.
    pub fn fork(&self, message: &str) -> LogTree {
        let Some(inner) = &self.0 else {
            return LogTree::none();
        };
        let child = LogTree(Some(Arc::new(LogTreeInner {
            name: String::new(),
            logs: Mutex::new(Vec::new()),
            root: inner.root.clone(),
            is_root: false,
            level: inner.level + 1,
            verbose: AtomicBool::new(inner.verbose.load(Ordering::Relaxed)),
            count: AtomicI32::new(0),
            string_length: AtomicI32::new(0),
        })));
        let log = new_log_entry(Some(child.clone()), message.to_owned());
        inner.add(log);
        child
    }
}

impl Default for LogTree {
    /// Same as [`LogTree::none`].
    fn default() -> Self {
        LogTree::none()
    }
}

impl fmt::Display for LogTree {
    /// `String()` — renders the whole tree; panics on a non-root or nil
    /// `LogTree` (Go panics on `c.root != c` / nil receiver).
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(inner) = &self.0 else {
            panic!("can only call String on root LogTree");
        };
        assert!(
            inner.is_root,
            "can only call String on root LogTree"
        );
        let header = format!("======== {} ========\n", inner.name);
        let mut builder = String::with_capacity(
            inner.string_length.load(Ordering::Relaxed) as usize + header.len(),
        );
        builder.push_str(&header);
        inner.write_logs_recursive(&mut builder, "");
        f.write_str(&builder)
    }
}

impl Logger for LogTree {
    /// `c.Log(message ...any)`.
    fn log(&self, msg: fmt::Arguments) {
        let Some(inner) = &self.0 else {
            return;
        };
        inner.add(new_log_entry(None, msg.to_string()));
    }

    /// `c.Logf(format, args...)`.
    fn logf(&self, args: fmt::Arguments) {
        let Some(inner) = &self.0 else {
            return;
        };
        inner.add(new_log_entry(None, args.to_string()));
    }

    /// `c.Verbose()` — `Some` iff non-nil and verbose (Go returns nil
    /// otherwise).
    fn verbose(&self) -> Option<&dyn Logger> {
        match &self.0 {
            Some(inner) if inner.verbose.load(Ordering::Relaxed) => Some(self),
            _ => None,
        }
    }

    /// `c.IsVerbose()` — Go reads `c.verbose` without a nil check and panics
    /// on a nil `*LogTree`; mirrored.
    fn is_verbose(&self) -> bool {
        self.0
            .as_ref()
            .expect("IsVerbose on nil LogTree")
            .verbose
            .load(Ordering::Relaxed)
    }

    /// `c.SetVerbose(verbose)`.
    fn set_verbose(&self, verbose: bool) {
        if let Some(inner) = &self.0 {
            inner.verbose.store(verbose, Ordering::Relaxed);
        }
    }
}
