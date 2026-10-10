//! Ported from `tsc/internal/transpile` @ ec47d33c23e464a17cdf2475632cba629bee8763.
//!
//! Package transpile implements single-file JavaScript and declaration emit.

pub mod fs;
pub mod options_generated;
pub mod transpile;

pub use transpile::{transpile_declaration, transpile_module, Options, Output};
