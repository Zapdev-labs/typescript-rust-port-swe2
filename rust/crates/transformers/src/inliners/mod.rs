// Ported from tsc/internal/transformers/inliners @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The value inliners (currently just the const-enum inliner). File layout
// mirrors the Go package one-to-one. See `estransforms/mod.rs` for the
// `Rc<RefCell<EmitContext>>`/`NodeVisitor` conventions shared by every
// transform module.

pub mod constenum;

pub use constenum::*;
