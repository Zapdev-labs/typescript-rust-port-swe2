// Ported from tsc/internal/ast/symbol.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Symbol shell. Symbols are stored in a `SymbolArena` shared program-wide;
// references use `SymbolId`. `SymbolTable` is an insertion-ordered map
// (`tsc_collections::OrderedMap`), preserving the deterministic iteration
// order the Go port relies on via `collections.OrderedMap`.

use crate::checkflags::CheckFlags;
use crate::chunked::ChunkedArena;
use crate::ids::{NodeId, SymbolId};
use crate::symbolflags::SymbolFlags;
use crate::{ModifierFlags, is_private_identifier_class_element_declaration};
use std::ops::{Index, IndexMut};
use std::rc::Rc;
use std::sync::Arc;

use tsc_collections::OrderedMap;

// Symbol

pub struct Symbol {
    pub flags: SymbolFlags,
    /// Non-zero only in transient symbols created by Checker
    pub check_flags: CheckFlags,
    /// `Arc<str>` — Go shares the header on `symbol.Name`; `.name.clone()`
    /// sites become refcount bumps.
    pub name: Arc<str>,
    pub declarations: Vec<NodeId>,
    pub value_declaration: Option<NodeId>,
    /// `Rc<SymbolTable>` — Go shares `map[string]*Symbol` headers on struct
    /// copies; `members.clone()`/`exports.clone()` sites (checker merge and
    /// lookup paths) become refcount bumps instead of deep `OrderedMap`
    /// copies. `Rc::make_mut` gives copy-on-write for the rare writes.
    /// PORT: Go map-reference semantics would let a clone observe later
    /// writes through the shared map; `Rc::make_mut` detaches instead —
    /// sites relying on shared-mutation visibility are marked `// PORT:`.
    pub members: Rc<SymbolTable>,
    pub exports: Rc<SymbolTable>,
    // Go stores a lazily-assigned `id atomic.Uint64`; the slot index in the
    // owning `Vec<Symbol>` is the id in this port.
    pub parent: Option<SymbolId>,
    pub export_symbol: Option<SymbolId>,
}

thread_local! {
    /// Shared never-mutated empty `members`/`exports` — every
    /// `Symbol::default()` starts with refcount-bumps of this instead of two
    /// fresh `OrderedMap` allocations. `Rc::make_mut` detaches on first write.
    static EMPTY_SYMBOL_TABLE: Rc<SymbolTable> = Rc::new(SymbolTable::default());
}

impl Default for Symbol {
    fn default() -> Self {
        EMPTY_SYMBOL_TABLE.with(|t| Symbol {
            flags: SymbolFlags::default(),
            check_flags: CheckFlags::default(),
            name: Default::default(),
            declarations: Vec::new(),
            value_declaration: None,
            members: t.clone(),
            exports: t.clone(),
            parent: None,
            export_symbol: None,
        })
    }
}

impl Symbol {
    pub fn is_external_module(&self) -> bool {
        self.flags.intersects(SymbolFlags::MODULE) && is_ambient_module_symbol_name(&self.name)
    }
}

// SymbolArena — the program-global `Vec<Symbol>` store of SPEC §5.2.

/// `SymbolArena` is the program-global arena of `Symbol` elements; `SymbolId`
/// indexes it. Same shape as the checker's `TypeArena`: chunked slab
/// (`ChunkedArena` — `Rc<UnsafeCell<Chunked<T>>>`) because the pipeline is
/// single-threaded; fixed-capacity inner Vecs give each `Symbol` a stable
/// heap address so `SymbolPtr` handles stay valid across pushes. Go
/// semantics: every `*ast.Symbol` lives on a shared heap and mutation is in
/// place — readers see writes immediately.
#[derive(Clone, Default)]
pub struct SymbolArena {
    symbols: ChunkedArena<Symbol>,
}

/// Shared handle to an arena-resident `Symbol` — Go's `*Symbol`. `Copy`, no
/// refcounting; validity is the arena's lifetime.
#[derive(Clone, Copy)]
pub struct SymbolPtr(*const Symbol);

#[allow(unsafe_code)] // stable-address arena deref — see `SymbolArena`
impl std::ops::Deref for SymbolPtr {
    type Target = Symbol;
    #[inline]
    fn deref(&self) -> &Symbol {
        unsafe { &*self.0 }
    }
}

impl SymbolPtr {
    /// Go pointer-identity comparison (replaces `Rc::ptr_eq`).
    pub fn ptr_eq(a: SymbolPtr, b: SymbolPtr) -> bool {
        a.0 == b.0
    }
}

/// Mutable handle — Go's `*Symbol` write shape. Interior mutation while
/// other `SymbolPtr`s exist is legal (Go aliasing), matching binder/checker
/// code that writes flags/parent/members on shared symbols.
#[derive(Clone, Copy)]
pub struct SymbolMutPtr(*mut Symbol);

#[allow(unsafe_code)] // stable-address arena deref — see `SymbolArena`
impl std::ops::Deref for SymbolMutPtr {
    type Target = Symbol;
    #[inline]
    fn deref(&self) -> &Symbol {
        unsafe { &*self.0 }
    }
}

#[allow(unsafe_code)] // stable-address arena deref — see `SymbolArena`
impl std::ops::DerefMut for SymbolMutPtr {
    #[inline]
    fn deref_mut(&mut self) -> &mut Symbol {
        unsafe { &mut *self.0 }
    }
}

#[allow(unsafe_code)] // arena internals reach through `UnsafeCell`
impl SymbolArena {
    /// Allocate a symbol in the arena, returning its `SymbolId`.
    pub fn alloc(&self, s: Symbol) -> SymbolId {
        SymbolId(self.symbols.alloc(s) as u32)
    }

    /// Scoped-thread parallel-bind protocol — see `ChunkedArena`.
    pub fn enter_parallel(&self, extra_elements: usize) {
        self.symbols.enter_parallel(extra_elements);
    }
    /// Scoped-thread parallel-bind protocol — see `ChunkedArena`.
    pub fn exit_parallel(&self) {
        self.symbols.exit_parallel();
    }

    /// Shared-pointer access to a single symbol — the Go `s.field` read
    /// shape. A single pointer deref: no borrow flag, no refcount.
    #[inline]
    pub fn get(&self, id: SymbolId) -> SymbolPtr {
        // SAFETY: `id` was handed out by `alloc`, so `id.index()` is in
        // bounds (elements are only ever pushed). The slab element address
        // is stable (inner Vecs never grow past capacity).
        unsafe { SymbolPtr(self.symbols.get(id.index())) }
    }

    /// `&Symbol` access — same deref as `get` without wrapping the pointer.
    /// The reference stays valid across `alloc` (stable `Box` addresses);
    /// it reads through any `get_mut` writes (Go semantics).
    #[inline]
    pub fn get_ref(&self, id: SymbolId) -> &Symbol {
        // SAFETY: same as `get`.
        unsafe { &*self.symbols.get(id.index()) }
    }

    /// Write access to a single symbol — the Go `s.field = v` write shape.
    /// Mutates in place; existing `SymbolPtr`/`&Symbol` handles observe the
    /// write (Go aliasing).
    #[inline]
    pub fn get_mut(&self, id: SymbolId) -> SymbolMutPtr {
        // SAFETY: same as `get`. Interior mutation of a shared element is
        // the port's Go-aliasing model — callers must not rely on stale
        // field snapshots across a `get_mut`, same as in Go.
        unsafe { SymbolMutPtr(self.symbols.get_mut(id.index())) }
    }

    /// `len(symbols)`.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Stable identity token for the arena's backing store — the port's
    /// answer to `(*Vec<Symbol>).as_ptr()` keys that distinguish which file's
    /// arena a `SymbolId` belongs to.
    pub fn arena_id(&self) -> usize {
        self.symbols.arena_id()
    }

    /// `len(symbols) == 0`.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Iteration over `&Symbol` handles. Index-based (not slice-based) so
    /// `alloc` during iteration can't invalidate the iterator; the end index
    /// is a snapshot, matching the old `Ref`-guard iteration scope.
    pub fn iter(&self) -> SymbolArenaIter<'_> {
        SymbolArenaIter {
            arena: self,
            next: 0,
            end: self.len(),
        }
    }

    /// Field-by-field copy into a plain `Vec<Symbol>` (`Symbol` is not
    /// `Clone`). Used by emit paths that need a detached snapshot of the
    /// arena to hand to the binder resolver. `members`/`exports` are
    /// `Rc`-shared with the live arena (Go map-header copy): reads see the
    /// same entries, and `Rc::make_mut` detaches on the first write, so the
    /// "mutations don't reach the shared store" guarantee of `snapshot`
    /// still holds.
    pub fn to_vec(&self) -> Vec<Symbol> {
        self.iter()
            .map(|s| Symbol {
                flags: s.flags,
                check_flags: s.check_flags,
                name: s.name.clone(),
                declarations: s.declarations.clone(),
                value_declaration: s.value_declaration,
                members: s.members.clone(),
                exports: s.exports.clone(),
                parent: s.parent,
                export_symbol: s.export_symbol,
            })
            .collect()
    }

    /// Build an arena from an owned `Vec<Symbol>` (detached snapshots, test
    /// scaffolding).
    pub fn from_vec(v: Vec<Symbol>) -> SymbolArena {
        let arena = SymbolArena::default();
        for s in v {
            arena.alloc(s);
        }
        arena
    }

    /// Detached copy of the whole arena — mutations don't reach the shared
    /// store (the emit resolver's unhooked-resolver snapshot path).
    pub fn snapshot(&self) -> SymbolArena {
        SymbolArena::from_vec(self.to_vec())
    }
}

#[allow(unsafe_code)] // `symbols[i]` reads reach through the slab
impl Index<usize> for SymbolArena {
    type Output = Symbol;
    #[inline]
    fn index(&self, i: usize) -> &Symbol {
        // SAFETY: callers index with ids handed out by `alloc`; slab
        // element addresses are stable across growth.
        unsafe { &*self.symbols.get(i) }
    }
}

impl Index<SymbolId> for SymbolArena {
    type Output = Symbol;
    #[inline]
    fn index(&self, id: SymbolId) -> &Symbol {
        &self[id.index()]
    }
}

#[allow(unsafe_code)] // `symbols[i]` writes reach through the slab
impl IndexMut<usize> for SymbolArena {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Symbol {
        // SAFETY: same as `Index`. Interior mutation of a shared element is
        // the port's Go-aliasing model.
        unsafe { &mut *self.symbols.get_mut(i) }
    }
}

impl IndexMut<SymbolId> for SymbolArena {
    #[inline]
    fn index_mut(&mut self, id: SymbolId) -> &mut Symbol {
        &mut self[id.index()]
    }
}

/// Index-based `&Symbol` iterator for `SymbolArena::iter` — snapshots `end`
/// at creation; `alloc` mid-iteration can't invalidate the yielded refs
/// (Box targets are stable).
pub struct SymbolArenaIter<'a> {
    arena: &'a SymbolArena,
    next: usize,
    end: usize,
}

impl<'a> Iterator for SymbolArenaIter<'a> {
    type Item = &'a Symbol;
    #[inline]
    fn next(&mut self) -> Option<&'a Symbol> {
        if self.next >= self.end {
            return None;
        }
        let i = self.next;
        self.next += 1;
        // SAFETY: `i < end <= len()` at iterator creation; elements are only
        // ever pushed, so `i` stays in bounds and the slab element address
        // is stable across growth.
        #[allow(unsafe_code)]
        unsafe {
            Some(&*self.arena.symbols.get(i))
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.end - self.next, Some(self.end - self.next))
    }
}

impl ExactSizeIterator for SymbolArenaIter<'_> {}

/// Ported from `(s *Symbol).IsStatic`. Needs the node arena to inspect the
/// value declaration's modifier flags.
pub fn symbol_is_static(s: &Symbol, nodes: &[crate::Node]) -> bool {
    let Some(value_declaration) = s.value_declaration else {
        return false;
    };
    let node = &nodes[value_declaration.local_index() as usize];
    node.modifier_flags().intersects(ModifierFlags::STATIC)
}

// SymbolTable

/// `SymbolTable` is an ordered map from name to `SymbolId`, mirroring
/// `map[string]*Symbol` while keeping deterministic insertion order.
/// Keys are `Arc<str>`: Go shares the string header on map copy/extend;
/// `Arc<str>` clones are refcount bumps while `String` keys would
/// alloc+memcpy per entry (member-table merges are check-time hot).
/// `str` lookups work via `Equivalent`/`Borrow`. `Arc` (not `Rc`)
/// for parity with earlier thread-safe handles; the refcount-bump
/// clone cost vs `String` is the win that matters.
pub type SymbolTable = OrderedMap<std::sync::Arc<str>, SymbolId>;

/// Not a valid identifier char and escapes to `\uFFFD` — Rust's UTF-8-safe
/// equivalent of Go's invalid-UTF-8 `\xFE` marker byte.
pub const INTERNAL_SYMBOL_NAME_PREFIX: &str = "\u{FFFD}";

pub const INTERNAL_SYMBOL_NAME_CALL: &str = "\u{FFFD}call"; // Call signatures
pub const INTERNAL_SYMBOL_NAME_CONSTRUCTOR: &str = "\u{FFFD}constructor"; // Constructor implementations
pub const INTERNAL_SYMBOL_NAME_NEW: &str = "\u{FFFD}new"; // Constructor signatures
pub const INTERNAL_SYMBOL_NAME_INDEX: &str = "\u{FFFD}index"; // Index signatures
pub const INTERNAL_SYMBOL_NAME_EXPORT_STAR: &str = "\u{FFFD}export"; // Module export * declarations
pub const INTERNAL_SYMBOL_NAME_GLOBAL: &str = "\u{FFFD}global"; // Global self-reference
pub const INTERNAL_SYMBOL_NAME_MISSING: &str = "\u{FFFD}missing"; // Indicates missing symbol
pub const INTERNAL_SYMBOL_NAME_TYPE: &str = "\u{FFFD}type"; // Anonymous type literal symbol
pub const INTERNAL_SYMBOL_NAME_OBJECT: &str = "\u{FFFD}object"; // Anonymous object literal declaration
pub const INTERNAL_SYMBOL_NAME_JSX_ATTRIBUTES: &str = "\u{FFFD}jsxAttributes"; // Anonymous JSX attributes object literal declaration
pub const INTERNAL_SYMBOL_NAME_CLASS: &str = "\u{FFFD}class"; // Unnamed class expression
pub const INTERNAL_SYMBOL_NAME_FUNCTION: &str = "\u{FFFD}function"; // Unnamed function expression
pub const INTERNAL_SYMBOL_NAME_COMPUTED: &str = "\u{FFFD}computed"; // Computed property name declaration with dynamic name
pub const INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION: &str = "\u{FFFD}assignment"; // Assignment declarations
pub const INTERNAL_SYMBOL_NAME_INSTANTIATION_EXPRESSION: &str = "\u{FFFD}instantiationExpression"; // Instantiation expressions
pub const INTERNAL_SYMBOL_NAME_IMPORT_ATTRIBUTES: &str = "\u{FFFD}importAttributes";
/// Export assignment symbol
pub const INTERNAL_SYMBOL_NAME_EXPORT_EQUALS: &str = "export=";
/// Default export symbol (technically not wholly internal, but included here for usability)
pub const INTERNAL_SYMBOL_NAME_DEFAULT: &str = "default";
pub const INTERNAL_SYMBOL_NAME_THIS: &str = "this";
pub const INTERNAL_SYMBOL_NAME_MODULE_EXPORTS: &str = "module.exports";

/// Ported from `SymbolName`.
pub fn symbol_name<'a>(symbol: &'a Symbol, nodes: &'a [crate::Node]) -> std::borrow::Cow<'a, str> {
    if let Some(value_declaration) = symbol.value_declaration
        && is_private_identifier_class_element_declaration(
            &nodes[value_declaration.local_index() as usize],
            nodes,
        )
        && let Some(name) = nodes[value_declaration.local_index() as usize].name()
    {
        return nodes[name.local_index() as usize].text(nodes);
    }
    std::borrow::Cow::Borrowed(symbol.name.as_ref())
}

/// `EscapeAllInternalSymbolNames` replaces internal symbol name markers ("\xFE") with "__".
pub fn escape_all_internal_symbol_names(name: &str) -> String {
    name.replace(INTERNAL_SYMBOL_NAME_PREFIX, "__")
}

/// `EscapeInternalSymbolName` escapes a single leading internal marker.
pub fn escape_internal_symbol_name(name: &str) -> std::borrow::Cow<'_, str> {
    if let Some(rest) = name.strip_prefix(INTERNAL_SYMBOL_NAME_PREFIX) {
        return std::borrow::Cow::Owned(format!("__{rest}"));
    }
    std::borrow::Cow::Borrowed(name)
}

/// `EscapeSymbolName` converts a binder symbol name into its escaped "__String"
/// form. Internal names (prefixed with the "\xFE" sentinel) become "__"-prefixed,
/// and user names that already begin with "__" gain an extra leading underscore
/// so they can be distinguished from internal names.
pub fn escape_symbol_name(name: &str) -> std::borrow::Cow<'_, str> {
    if let Some(rest) = name.strip_prefix(INTERNAL_SYMBOL_NAME_PREFIX) {
        return std::borrow::Cow::Owned(format!("__{rest}"));
    }
    if name.starts_with("__") {
        return std::borrow::Cow::Owned(format!("_{name}"));
    }
    std::borrow::Cow::Borrowed(name)
}

/// `IsAmbientModuleSymbolName` reports whether `s` names an ambient module
/// symbol. Ambient module symbols are either of the form `"modulename"` or
/// `InternalSymbolNamePrefix + "\"modulename\"pattern@nodeId"`; see
/// `getDeclarationName` in the Go binder.
pub fn is_ambient_module_symbol_name(s: &str) -> bool {
    try_get_ambient_module_name_from_symbol_name(s).is_some()
}

/// Ported from `TryGetAmbientModuleNameFromSymbolName` in utilities.go. Kept
/// here because symbol.go is its only caller within the `ast` layer.
pub fn try_get_ambient_module_name_from_symbol_name(s: &str) -> Option<String> {
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return Some(s[1..s.len() - 1].to_string());
    }

    let pattern_prefix = format!("{INTERNAL_SYMBOL_NAME_PREFIX}\"");
    let rest = s.strip_prefix(&pattern_prefix)?;
    let marker_index = rest.rfind("\"pattern@")?;
    if marker_index < 1 {
        return None;
    }
    Some(rest[..marker_index].to_string())
}
