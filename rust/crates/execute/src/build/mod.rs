// Ported from tsc/internal/execute/build @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Implements `tsc -b` build orchestration: build-graph generation from
// project references, per-project up-to-date checking, build-info
// load/store, pseudo-builds (timestamp touches), cleaning, reporting, and
// fswatch-driven watch rebuilds.
//
// Concurrency: the Go package runs tasks on a pool of `builders` goroutines
// coordinated by `BuildTask.done`/`built` channels and guarded by per-task
// mutexes, and parses config files on a `core.WorkGroup`. This port runs a
// sequential work-list (see the banner in `orchestrator.rs`) because the
// Rust compiler stack — `Program`, `ParsedCommandLine`, `ParsedSourceFile`
// — is `Rc`/arena-backed and not `Send`/`Sync`, so tasks cannot move between
// threads. Goroutine primitives collapse as follows:
//
//   - `BuildTask.done`/`built` channels + `waitOnUpstream` → no-ops; the
//     build order is already a topological order, so every upstream task
//     has finished when its downstream runs.
//   - `buildInfoEntryMu`/`downStreamUpdateMu`/`atomic.Bool` → `RefCell`/
//     plain `bool`s.
//   - `SyncMap[PathKey, *BuildTask]` → `Vec<BuildTask>` + `PathKey` index
//     (`buildtask.rs`'s `TaskId`).
//   - `WatchManager` stays internally synchronized — its callbacks arrive
//     on fswatch backend threads; `Orchestrator::do_cycle` locks it.
//
// Build-info/incremental integration goes through `crate::incremental`
// (`build_info::BuildInfo`, `new_program`, `read_build_info_program`,
// `new_build_info_reader`, `compute_hash`,
// `build_info::resolve_build_info_file_name`, `get_mtime`, `Host`,
// `BuildInfoReader`, `BuildInfoRootInfoReader`,
// `build_info::content_mapper_identities`,
// `build_info::is_build_info_file_name_default_library`, `Program`).

mod buildtask;
mod compiler_host;
mod host;
mod orchestrator;
mod parse_cache;
mod uptodatestatus;

pub use orchestrator::{Options, Orchestrator, OrchestratorResult, new_orchestrator};
