// tsc-project-logging — port of tsc/internal/project/logging @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The project/session logger: a `Logger` trait (`Log`/`Logf`/`Verbose`),
// an `io.Writer`-backed `WriterLogger`, an in-memory `TestLogger`, and the
// tree-shaped `LogTree` collector.
//
// PORT notes:
// - `...any`/`format, args...` parameters become `std::fmt::Arguments`
//   (`format_args!`); `%v`-style verbs map to `{}`.
// - Nil-able receivers (`*logger`, `*LogTree`) become explicit no-op types
//   (`NopLogger`) or an `Option`-backed handle (`LogTree::none()`); nil-able
//   `Logger` returns become `Option<&dyn Logger>`.
// - `formatTime` renders UTC — Go uses the local timezone, which Rust std
//   cannot query (see timefmt.rs / PORTING-NOTES).

mod logcollector;
mod logger;
mod logtree;
mod timefmt;

#[cfg(test)]
mod logtree_test;

pub use logcollector::{TestLogger, new_test_logger};
pub use logger::{LogCollector, Logger, NopLogger, WriterLogger, new_logger, new_nop_logger};
pub use logtree::LogTree;
