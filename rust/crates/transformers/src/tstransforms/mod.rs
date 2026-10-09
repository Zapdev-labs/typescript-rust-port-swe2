// Ported from tsc/internal/transformers/tstransforms @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The TypeScript-specific transforms: type erasure (`typeeraser.go`),
// import elision (`importelision.go`), enum/namespace runtime syntax
// (`runtimesyntax.go`), legacy decorators (`legacydecorators.go`) with their
// `design:*` metadata serializer (`metadata.go`, `typeserializer.go`), and
// shared helpers (`utilities.go`). File layout mirrors the Go package
// one-to-one.
//
// PORT notes common to every file in this module (mirroring
// `crate::estransforms`):
//   - Go transformer structs embed `transformers.Transformer` so their visit
//     methods can reach `tx.Visitor()`, `tx.Factory()`, and
//     `tx.EmitContext()`. Rust cannot capture the `Transformer` being built
//     inside its own visit closure, so each transform's state lives in an
//     `Rc`d struct captured by the closure, the `EmitContext` is captured as
//     `Rc<RefCell<EmitContext>>`, and the running `NodeVisitor` arrives as
//     the visit callback's first parameter. `tx.Factory()` calls map onto
//     `ec.borrow_mut().factory`.
//   - A `RefCell<EmitContext>` borrow may never span a `v.visit_*` call nor a
//     factory call that fires hooks — all `borrow`/`borrow_mut` scopes are
//     single statements or tight blocks. `with_ec_mut` is used for the
//     re-entrant `EmitContext` visitor helpers (`visit_parameters`,
//     `visit_function_body`, `visit_iteration_body`, `variable_statements`,
//     ...).
//   - `update_*` factory methods return `Option<NodeId>` where `None` means
//     "unchanged" (Go returned the input pointer); call sites unwrap with
//     `.unwrap_or(node)`.
//   - `binder.ReferenceResolver`/`printer.EmitResolver` methods take the node
//     and symbol arenas explicitly. Transforms reach the binder's symbol
//     arena through `TransformOptions::symbols`
//     (`Option<&'a RefCell<Vec<Symbol>>>`), passed by the caller alongside
//     `resolver`.

pub mod importelision;
pub mod legacydecorators;
pub mod metadata;
pub mod runtimesyntax;
pub mod typeeraser;
pub mod typeserializer;
pub mod utilities;

pub use importelision::*;
pub use legacydecorators::*;
pub use metadata::*;
pub use runtimesyntax::*;
pub use typeeraser::*;
pub use typeserializer::*;
pub use utilities::*;
