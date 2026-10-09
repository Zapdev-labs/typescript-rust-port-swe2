// Ported from tsc/internal/transformers/moduletransforms @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The module transforms: `commonjsmodule.go`, `esmodule.go`,
// `impliedmodule.go`, `externalmoduleinfo.go`, and `utilities.go`.
// File layout mirrors the Go package one-to-one.
//
// PORT notes common to every file in this module (shared with
// `estransforms`, which established the pattern):
//   - Go transformer structs (e.g. `type CommonJSModuleTransformer struct {
//     transformers.Transformer; ... }`) embed `*Transformer` so their visit
//     methods can reach `tx.Visitor()`, `tx.Factory()`, and
//     `tx.EmitContext()`. Rust cannot capture the `Transformer` being built
//     inside its own visit closure, so each transform's state lives in an
//     `Rc`d struct captured by the closure, the `EmitContext` is captured as
//     `Rc<RefCell<EmitContext>>`, and the running `NodeVisitor` arrives as
//     the visit callback's first parameter. Go's `tx.Factory()` calls map
//     onto `ec.borrow_mut().factory`.
//   - `tx.Visitor()` is the transformer's *main* visitor (`tx.visit`). The
//     CommonJS transform also installs several *sibling* visitors
//     (`topLevelVisitor`, `topLevelNestedVisitor`, `discardedValueVisitor`,
//     `assignmentPatternVisitor`) created via
//     `emitContext.NewNodeVisitor` in `NewCommonJSModuleTransformer`. These
//     are stored on the state struct behind `RefCell` and their visit
//     closures re-enter the state through `Weak`.
//   - A `RefCell<EmitContext>` borrow may never span a `v.visit_*` call
//     (nested visits re-enter the state and re-borrow the context) — all
//     `borrow`/`borrow_mut` scopes are single statements or tight blocks.
//   - `update_*` factory methods return `Option<NodeId>` where `None` means
//     "unchanged" (Go returned the input pointer); call sites unwrap with
//     `.unwrap_or(node)`.
//   - `visit_slice` returns `Some(Vec)` when any element changed and `None`
//     when the slice was unchanged; `visit_node`/`visit_nodes` return the
//     resulting node(s) (`None` = removed, mirroring Go nil).
//
// PORT: `tx.Visitor()` resolves to `visitors.main` — a `NodeVisitor`
// constructed with the *same* visit function and emit-context hooks as the
// real `Transformer` visitor (which Rust cannot reach from the state
// struct). Behavior is identical because `NodeVisitor` behavior is
// determined entirely by its `visit` callback and hooks.

pub mod commonjsmodule;
pub mod esmodule;
pub mod externalmoduleinfo;
pub mod impliedmodule;
pub mod utilities;

pub use commonjsmodule::*;
pub use esmodule::*;
pub use externalmoduleinfo::*;
pub use impliedmodule::*;
pub use utilities::*;
