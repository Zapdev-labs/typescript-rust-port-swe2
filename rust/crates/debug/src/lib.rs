// Ported from tsc/internal/debug @ ec47d33c23e464a17cdf2475632cba629bee8763
pub mod debug;

// `debug.Fail`, `debug.KindString` and the macro-internal impl fns live at
// the crate root so `$crate::` paths inside the exported macros resolve.
pub use debug::{KindString, fail};
#[doc(hidden)]
pub use debug::{assert_never, assert_slow, fail_bad_syntax_kind};
