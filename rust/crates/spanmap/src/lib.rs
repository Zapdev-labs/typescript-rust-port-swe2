// Ported from tsc/internal/spanmap @ ec47d33c23e464a17cdf2475632cba629bee8763
pub mod spanmap;

#[cfg(test)]
mod spanmap_test;

// Flat re-exports so call sites mirror Go's `spanmap.X` as `spanmap::X`.
pub use spanmap::*;
