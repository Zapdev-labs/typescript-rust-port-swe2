// Ported from tsc/internal/fourslash @ ec47d33c23e464a17cdf2475632cba629bee8763
// The fourslash language-service test harness (drives ls/lsp over a VFS).
pub mod baselineutil;
pub mod fourslash;
pub mod semantictokens;
pub mod statebaseline;
pub mod test_parser;
pub mod testsutil;
pub mod verify;
pub mod verify_baseline;

// Flat re-exports for the generated test suite (`use tsc_fourslash::*` —
// tests reference harness types/consts unqualified, matching Go's
// package-scoped `fourslash.` surface).
pub use baselineutil::*;
pub use fourslash::*;
pub use semantictokens::*;
pub use statebaseline::*;
pub use test_parser::*;
pub use testsutil::*;
pub use verify::*;
pub use verify_baseline::*;
