// Ported from the `incremental`-package call sites in
// tsc/internal/execute/tsc.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! `tsc.go`'s `performIncrementalCompilation` — which reads the prior
//! `.tsbuildinfo` via `ReadBuildInfoProgram`/`NewBuildInfoReader`, builds the
//! `compiler.Program`, wraps it in `incremental.NewProgram` and hands the
//! incremental program to `EmitAndReportStatistics` — is ported as
//! `crate::tsc_main::perform_incremental_compilation`. The functions it
//! calls are re-exported from this module's siblings:
//!
//! - `crate::incremental::new_build_info_reader` (`NewBuildInfoReader`)
//! - `crate::incremental::read_build_info_program` (`ReadBuildInfoProgram`)
//! - `crate::incremental::create_host` (`CreateHost`)
//! - `crate::incremental::new_program` (`NewProgram`)
//! - `incremental::Program::take_nested_emit_time` (`TakeNestedEmitTime`)
//! - `incremental::Program::has_changed_dts_file` (`HasChangedDtsFile`)
//!
//! This file intentionally contains no code — it documents where the Go
//! `tsc.go` ↔ `incremental` boundary landed in the Rust port.
