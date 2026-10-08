// Ported from tsc/internal/ast @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The Go `ast` package split: `ast.go`/`ast_generated.go` are `ast` +
// `ast_generated` here; `kind_generated.go`/`kind_stringer_generated.go` are
// `kind_generated`; `visitor.go` is `visitor`; `subtreefacts.go` plus the
// hand-written `computeSubtreeFacts` bodies are `subtreefacts`; `flow.go` is
// `flow`; `symbol.go` is `symbol`; and the `*flags.go` files are the flag
// modules. `utilities.go` is only partially ported — the helpers needed by
// the AST core live in `utilities`; the rest lands with the checker.

#[macro_use]
mod flagdef;

pub mod ast;
pub mod ast_generated;
pub mod checkflags;
pub mod diagnostic;
pub mod flow;
pub mod functionflags;
pub mod ids;
pub mod kind_generated;
pub mod modifierflags;
pub mod nodeflags;
pub mod parseoptions;
pub mod positionmap;
pub mod precedence;
pub mod subtreefacts;
pub mod symbol;
pub mod symbolflags;
pub mod tokenflags;
pub mod utilities;
pub mod visitor;

#[cfg(test)]
mod ast_accessor_test;
#[cfg(test)]
mod kind_ordinals_test;
#[cfg(test)]
mod positionmap_test;

// Go package-level names land at the crate root, mirroring `package ast`.
pub use ast::*;
pub use ast_generated::NodeData;
pub use flow::{FlowFlags, FlowList, FlowNode};
pub use ids::{FlowListId, FlowNodeId, NodeId, SymbolId};
pub use kind_generated::Kind;
pub use modifierflags::ModifierFlags;
pub use nodeflags::NodeFlags;
pub use subtreefacts::SubtreeFacts;
pub use symbol::{Symbol, SymbolTable};
pub use symbolflags::SymbolFlags;
pub use tokenflags::TokenFlags;
pub use utilities::is_private_identifier_class_element_declaration;
pub use visitor::{NodeVisitor, NodeVisitorHooks, VisitorCx};
