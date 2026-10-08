// Ported from tsc/internal/outputpaths @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod outputpaths;

#[cfg(test)]
mod outputpaths_test;

// Flat re-exports so call sites mirror Go's `outputpaths.X` as `outputpaths::X`.
pub use outputpaths::*;
