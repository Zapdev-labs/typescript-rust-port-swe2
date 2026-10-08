// Ported from tsc/internal/checker/symbolaccessibility.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the symbol-accessibility index
// state referenced by `Checker::external_module_containers` plus the
// `symbolTableID` machinery and `accessibleSymbolChainContext`. Query
// methods stay `PORT(deferred)` with the rest of symbolaccessibility.go.

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_ast::{NodeId, SymbolFlags, SymbolId};

// externalModuleContainerIndex

/// `type externalModuleContainerIndex struct` (symbolaccessibility.go).
#[derive(Default)]
pub struct ExternalModuleContainerIndex {
    /// `complete`.
    pub complete: bool,
    /// `containersByTarget` — `map[*ast.Symbol][]*ast.Symbol`.
    pub containers_by_target: FxHashMap<SymbolId, Vec<SymbolId>>,
    /// `moduleOrder` — `map[*ast.Symbol]int`.
    pub module_order: FxHashMap<SymbolId, i32>,
}

impl ExternalModuleContainerIndex {
    /// `(index *externalModuleContainerIndex) add` — modules are indexed
    /// one at a time, so a repeat of this container is always the last
    /// entry.
    pub fn add(&mut self, target: SymbolId, container: SymbolId) {
        let existing = self.containers_by_target.entry(target).or_default();
        if existing.last() != Some(&container) {
            existing.push(container);
        }
    }
}

// accessibleSymbolChainContext

/// `type accessibleSymbolChainContext struct` (symbolaccessibility.go).
#[derive(Default)]
pub struct AccessibleSymbolChainContext {
    /// `symbol`.
    pub symbol: Option<SymbolId>,
    /// `enclosingDeclaration`.
    pub enclosing_declaration: Option<NodeId>,
    /// `meaning`.
    pub meaning: SymbolFlags,
    /// `useOnlyExternalAliasing`.
    pub use_only_external_aliasing: bool,
    /// `visitedSymbolTablesMap` — `map[ast.SymbolId]map[symbolTableID]struct{}`.
    /// PORT: keyed by the owning `SymbolId`; `Option<SymbolId>` callers use
    /// `SymbolId::NONE` like Go's nil-symbol key (never populated in
    /// practice — Go only inserts under non-nil symbols).
    pub visited_symbol_tables_map: FxHashMap<SymbolId, FxHashSet<SymbolTableId>>,
}

// symbolTableID

/// `type symbolTableID uint64` (symbolaccessibility.go) — uniquely
/// identifies a symbol table by encoding its source. The high 3 bits
/// encode the kind, and the remaining bits encode the `NodeId` or
/// `SymbolId` of the source.
///
/// PORT: widened to `u128` — Go's `ast.NodeId` is a sequential `uint32`,
/// but this port's `NodeId` packs `file:20|local:44` and uses all 64 bits,
/// so kind bits at 61–63 would collide with the file index.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct SymbolTableId(pub u128);

/// `const stKindShift = 61` — in this port, above the 64-bit `NodeId`
/// payload (see the `u128` note above).
pub const ST_KIND_SHIFT: u32 = 64;

/// `stKindLocals`.
pub const ST_KIND_LOCALS: SymbolTableId = SymbolTableId(0 << ST_KIND_SHIFT);
/// `stKindExports`.
pub const ST_KIND_EXPORTS: SymbolTableId = SymbolTableId(1 << ST_KIND_SHIFT);
/// `stKindMembers`.
pub const ST_KIND_MEMBERS: SymbolTableId = SymbolTableId(2 << ST_KIND_SHIFT);
/// `stKindGlobals`.
pub const ST_KIND_GLOBALS: SymbolTableId = SymbolTableId(3 << ST_KIND_SHIFT);
/// `stKindResolvedExports` — resolved/derived exports from
/// `getExportsOfSymbol`, distinct from raw `sym.Exports`.
pub const ST_KIND_RESOLVED_EXPORTS: SymbolTableId =
    SymbolTableId(4 << ST_KIND_SHIFT);
/// `stKindMask` — extracts the kind bits from a `SymbolTableId`.
pub const ST_KIND_MASK: SymbolTableId = SymbolTableId(7 << ST_KIND_SHIFT);

/// `symbolTableIDFromLocals`.
pub fn symbol_table_id_from_locals(node: NodeId) -> SymbolTableId {
    SymbolTableId(ST_KIND_LOCALS.0 | node.0 as u128)
}

/// `symbolTableIDFromExports`.
pub fn symbol_table_id_from_exports(sym: SymbolId) -> SymbolTableId {
    SymbolTableId(ST_KIND_EXPORTS.0 | sym.0 as u128)
}

/// `symbolTableIDFromResolvedExports` — an ID for resolved/derived export
/// tables (e.g. from `getExportsOfSymbol`/`getExportsOfModule`, which may
/// include `export *` resolution and late-bound members). Distinct from
/// `symbol_table_id_from_exports` to prevent cache collisions with raw
/// `sym.exports` tables passed by `someSymbolTableInScope`.
pub fn symbol_table_id_from_resolved_exports(sym: SymbolId) -> SymbolTableId {
    SymbolTableId(ST_KIND_RESOLVED_EXPORTS.0 | sym.0 as u128)
}

/// `symbolTableIDFromMembers`.
pub fn symbol_table_id_from_members(sym: SymbolId) -> SymbolTableId {
    SymbolTableId(ST_KIND_MEMBERS.0 | sym.0 as u128)
}

/// `symbolTableIDFromGlobals`.
pub fn symbol_table_id_from_globals() -> SymbolTableId {
    ST_KIND_GLOBALS
}
