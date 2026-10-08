// Ported from tsc/internal/checker/links.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Link stores keyed by node/symbol arena ids. PORT: Go keys stores by
// `*ast.Node`/`*ast.Symbol` pointers (via `ast.GetNodeId`/`ast.GetSymbolId`);
// here `NodeId`/`SymbolId` are the keys directly.
//
// `symbolArenaLinkStore` in Go stores `*V` pointers allocated out of a
// `core.Arena[V]` — the arena exists purely to amortize allocations of the
// larger value structs. The Rust port stores `Option<Box<V>>` slots directly
// (one heap allocation per populated link, like `core.LinkStore`'s Box
// entries), which keeps Go's lazy-init and `Has`/`TryGet` visibility
// semantics exactly: a slot is `Some` iff `Get` populated it, regardless of
// whether its page exists. `PagedLinkStore` pages are still shared/amortized.

use tsc_ast::{NodeId, SymbolId};
use tsc_core::linkstore::PagedLinkStore;

/// `nodeLinkStore` is a links store keyed by node references. Values are
/// stored directly in the pages of the store which is suitable for values
/// where `sizeof(V)` is small.
///
/// PORT: all methods take `NodeId` where Go takes `*ast.Node`.
pub struct NodeLinkStore<V> {
    /// `store`.
    pub store: PagedLinkStore<V>,
}

impl<V: Default> Default for NodeLinkStore<V> {
    fn default() -> Self {
        Self {
            store: PagedLinkStore::new(),
        }
    }
}

impl<V: Default> NodeLinkStore<V> {
    /// `(s *nodeLinkStore[V]) Get`.
    pub fn get(&mut self, node: NodeId) -> &mut V {
        self.store.get(node.0)
    }

    /// `(s *nodeLinkStore[V]) Has`. PORT: `PagedLinkStore::has` only reports
    /// whether the page exists — matching Go, where `Has` likewise reports
    /// page existence for the inline store.
    pub fn has(&self, node: NodeId) -> bool {
        self.store.has(node.0)
    }

    /// `(s *nodeLinkStore[V]) TryGet`.
    pub fn try_get(&mut self, node: NodeId) -> Option<&mut V> {
        self.store.try_get(node.0)
    }
}

/// `symbolArenaLinkStore` is a links store keyed by symbol references.
/// Values are stored indirectly in an arena which is suitable for values
/// where `sizeof(V)` is larger.
///
/// PORT: `Option<Box<V>>` slots replace the `*V`-into-`core.Arena` scheme —
/// see the file header.
pub struct SymbolArenaLinkStore<V> {
    /// `store` — slot is `Some` iff `get` has populated it.
    store: PagedLinkStore<Option<Box<V>>>,
}

impl<V: Default> Default for SymbolArenaLinkStore<V> {
    fn default() -> Self {
        Self {
            store: PagedLinkStore::new(),
        }
    }
}

impl<V: Default> SymbolArenaLinkStore<V> {
    /// `(s *symbolArenaLinkStore[V]) Get`.
    pub fn get(&mut self, symbol: SymbolId) -> &mut V {
        let slot = self.store.get(symbol.0 as u64);
        if slot.is_none() {
            *slot = Some(Box::default());
        }
        slot.as_mut().unwrap()
    }

    /// `(s *symbolArenaLinkStore[V]) Has`.
    pub fn has(&mut self, symbol: SymbolId) -> bool {
        self.try_get(symbol).is_some()
    }

    /// `(s *symbolArenaLinkStore[V]) TryGet`.
    pub fn try_get(&mut self, symbol: SymbolId) -> Option<&mut V> {
        self.store.try_get(symbol.0 as u64)?.as_deref_mut()
    }
}
