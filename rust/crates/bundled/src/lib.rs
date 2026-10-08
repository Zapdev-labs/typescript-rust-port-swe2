// Ported from tsc/internal/bundled @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Provides access to the lib.d.ts files bundled with TypeScript. Lib
// contents are embedded into the binary via build.rs-generated
// `include_str!` table (the `//go:embed` analogue).

mod bundled;

pub use bundled::*;

#[cfg(test)]
mod bundled_test;
