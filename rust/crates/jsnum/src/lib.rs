// Ported from tsc/internal/jsnum @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Package jsnum provides JS-like number handling.

mod bigint_shim;
mod jsnum;
mod pseudobigint;
mod string;
mod stringutil_shim;

#[cfg(test)]
mod jsnum_test;
#[cfg(test)]
mod pseudobigint_test;
#[cfg(test)]
mod ryu_test;
#[cfg(test)]
mod string_test;

pub use jsnum::*;
pub use pseudobigint::*;
pub use string::*;
