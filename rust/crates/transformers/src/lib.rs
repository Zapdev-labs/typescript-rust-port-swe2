// Ported from tsc/internal/transformers @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `transformers` package root: the `Transformer`/`TransformerFactory`
// plumbing (`transformer.go`, `chain.go`), the destructuring flattener
// (`destructuring.go`), the modifier filter (`modifiervisitor.go`), and
// shared helpers (`utilities.go`). The transform subpackages
// (`estransforms`, `tstransforms`, `moduletransforms`, `jsxtransforms`,
// `inliners`, `declarations`) are ported separately.
//
// PORT: `*ast.Node` is `NodeId` into a `Vec<ast::Node>` arena threaded
// through the API, nilable results are `Option<NodeId>`, and `*ast.NodeList`
// is `Option<NodeList>`. See `transformer.rs` for how Go's
// `emitContext`/`factory`/`visitor` triple maps onto the Rust visitor
// machinery.

mod chain;
mod destructuring;
mod modifier_visitor;
mod transformer;
mod utilities;

pub use chain::*;
pub use destructuring::*;
pub use modifier_visitor::*;
pub use transformer::*;
pub use utilities::*;
