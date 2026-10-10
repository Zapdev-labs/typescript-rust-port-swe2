// Ported from tsc/internal/execute @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `execute` crate is the `tsc` CLI: the `CommandLine` entry point,
// `-b` build orchestration, `--watch` mode, and incremental build info.
// Submodules mirror the Go package layout:
//   - `tsc`        → tsc/internal/execute/tsc
//   - `incremental`→ tsc/internal/execute/incremental
//   - `build`      → tsc/internal/execute/build
//   - root files   → tsc/internal/execute/{tsc,watcher}.go

pub mod build;
pub mod incremental;
pub mod tsc;
mod tsc_main;
pub mod util;
mod watcher;

/// `tsc.CommandLineResult`, `tsc.Watcher`, `tsc.System`, `tsc.Testing`,
/// `tsc.ExitStatus` — the interfaces the result and tests interact with.
pub use tsc::{CommandLineResult, CommandLineTesting, ExitStatus, System, Watcher};
/// `CommandLine` — `execute.CommandLine(sys, commandLineArgs, testing)`.
pub use tsc_main::command_line;
