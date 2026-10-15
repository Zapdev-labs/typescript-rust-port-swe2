// Ported from tsc/internal/execute/tsctests @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `tsctests` is the tsc CLI test harness: a `vfs`-backed `TestSys`
// implementing `tsc::System` + `tsc::CommandLineTesting`, a mock `fswatch`
// backend, readable `.tsbuildinfo` baselines, and the `tscInput` runner.
//
// PORT: the whole module is `#[cfg(test)]`-gated — `tsc-testutil` is a
// dev-dependency because a normal dependency would cycle
// (tsc-execute → tsc-testutil → tsc-lsp → tsc-api → tsc-execute).

pub mod fs;
pub mod mock_watch_backend;
pub mod readablebuildinfo;
pub mod runner;
pub mod sys;

pub use fs::TestFs;
pub use mock_watch_backend::{MockWatch, MockWatchBackend, new_mock_watch_backend};
pub use readablebuildinfo::to_readable_build_info;
pub use runner::{
    TscEdit, TscInput, get_diff_for_incremental, no_change, no_change_only_edit,
};
pub use sys::{
    FileMap, TestClock, TestSys, get_file_map_with_build, get_test_lib_path_for, new_test_sys,
    new_tsc_system,
};
