// Ported from tsc/internal/checker/emitresolver.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the link-store payload structs
// and `EmitResolverLinks` referenced by `Checker::emit_resolver_links`.
// `EmitResolver` itself is a minimal `PORT(deferred)` shell: its real
// implementation lands with emitresolver.go (wave-2); it exists only so
// `Checker`-shaped state and the `printer::EmitResolver` trait have an
// anchor.

use tsc_ast::NodeId;
use tsc_core::linkstore::LinkStore;
use tsc_core::tristate::Tristate;

/// `type JSXLinks struct` (emitresolver.go) — links for jsx.
#[derive(Default)]
pub struct JsxLinks {
    /// `importRef`.
    pub import_ref: Option<NodeId>,
}

/// `type DeclarationLinks struct` (emitresolver.go) — links for
/// declarations.
#[derive(Default)]
pub struct DeclarationLinks {
    /// `isVisible` — if declaration is depended upon by exported
    /// declarations.
    pub is_visible: Tristate,
}

/// `type DeclarationFileLinks struct` (emitresolver.go).
#[derive(Default)]
pub struct DeclarationFileLinks {
    /// `aliasesMarked` — if file has had alias visibility marked.
    pub aliases_marked: bool,
}

/// `type EmitResolverLinks struct` (emitresolver.go) — owned by
/// `Checker::emit_resolver_links`.
#[derive(Default)]
pub struct EmitResolverLinks {
    /// `jsxLinks`.
    pub jsx_links: LinkStore<NodeId, JsxLinks>,
    /// `declarationLinks`.
    pub declaration_links: LinkStore<NodeId, DeclarationLinks>,
    /// `declarationFileLinks`.
    pub declaration_file_links: LinkStore<NodeId, DeclarationFileLinks>,
}
