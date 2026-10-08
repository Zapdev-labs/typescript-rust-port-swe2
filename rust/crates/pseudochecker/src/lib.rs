// Ported from tsc/internal/pseudochecker @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `pseudochecker` is a limited "checker" that returns pseudo-"types" of
// expressions — mostly those which trivially have type nodes. It is the
// minimal symbol/type lookup layer used before the real checker exists.

pub mod checker;
pub mod lookup;
pub mod types;

#[cfg(test)]
mod lookup_test;

pub use checker::PseudoChecker;
pub use lookup::{could_already_refer_to_undefined_type, is_in_const_context};
pub use types::*;
