// Ported from tsc/internal/transformers/jsxtransforms/jsx.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The JSX runtime transformer (classic `createElement` and automatic
// `jsx`/`jsxs`/`jsxDEV` runtimes). See `estransforms/mod.rs` for the shared
// `Rc<RefCell<EmitContext>>`/`NodeVisitor` conventions.

mod jsx;

pub use jsx::*;
