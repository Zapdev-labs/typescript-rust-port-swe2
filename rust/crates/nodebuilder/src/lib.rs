// Ported from tsc/internal/nodebuilder @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Only `types.go` is ported so far — the interfaces and flag types used by the
// emit resolver in the printer. The concrete node builder implementation lands
// with the checker.

mod types;

pub use types::*;
