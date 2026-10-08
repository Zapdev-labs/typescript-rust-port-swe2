// Ported from tsc/internal/diagnostics @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Package diagnostics contains generated localizable diagnostic messages.
//
// PORT: `generate.go`/`generate_deps.go` (the Go codegen program and its dep
// marker) are not ported — codegen moved to this crate's `build.rs` per SPEC
// §5.8, which reads `tsc/internal/diagnostics/diagnosticMessages.json` (the
// single source of truth — the JSON is not forked) plus
// `tools/LocProject.json` and `loc/*.generated.json`.

mod diagnostics;
mod diagnostics_generated;
mod loc_generated;
mod stringer_generated;

pub use diagnostics::*;
pub use diagnostics_generated::*;
