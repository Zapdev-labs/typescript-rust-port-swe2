// Ported from tsc/internal/symlinks @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod knownsymlinks;

#[cfg(test)]
mod knownsymlinks_bench_test;
#[cfg(test)]
mod knownsymlinks_test;

// Flat re-exports so call sites mirror Go's `symlinks.X`.
pub use knownsymlinks::{KnownDirectoryLink, KnownSymlinks};
