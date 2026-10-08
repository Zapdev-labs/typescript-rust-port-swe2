// Ported from tsc/internal/collections/cow.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;

use rustc_hash::FxHashMap;

/// CopyOnWriteMap is a map that defers cloning of an inherited backing map
/// until the first mutation, and supports nested scopes that share the parent's
/// map for reads but get their own clone on write.
///
/// The zero value is an empty map ready to use.
///
/// PORT: Go achieves sharing by shallow-copying the map header
/// (`saved := *c` in EnterScope) and tracking ownership with an `owned` flag.
/// An `Rc` expresses the same sharing — an inherited map is an `Rc` whose
/// strong count is > 1 — and `Rc::make_mut` is exactly the deferred
/// clone-on-write, so the `owned` flag is redundant and dropped.
/// `EnterScope`'s restore closure takes the map as an argument because Rust
/// closures cannot capture `&mut self` for later use.
#[derive(Debug)]
pub struct CopyOnWriteMap<K, V> {
    m: Rc<FxHashMap<K, V>>,
}

impl<K, V> Default for CopyOnWriteMap<K, V> {
    fn default() -> Self {
        Self {
            m: Rc::new(FxHashMap::default()),
        }
    }
}

impl<K: Eq + Hash, V> CopyOnWriteMap<K, V> {
    /// Creates an empty CopyOnWriteMap (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// Get returns the value for k and whether it was present.
    ///
    /// PORT: Go returns `(V, bool)`; Rust returns `Option<&V>`.
    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.get(k)
    }

    /// Has reports whether k is in the map.
    pub fn has<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.contains_key(k)
    }

    /// Set assigns v to k, cloning the inherited backing map first if necessary.
    pub fn set(&mut self, k: K, v: V)
    where
        K: Clone,
        V: Clone,
    {
        self.ensure_owned().insert(k, v);
    }

    fn ensure_owned(&mut self) -> &mut FxHashMap<K, V>
    where
        K: Clone,
        V: Clone,
    {
        // Clones the map iff it is shared with a saved parent scope;
        // equivalent to Go's `if !c.owned { c.m = maps.Clone(c.m) }`.
        Rc::make_mut(&mut self.m)
    }

    /// EnterScope returns a function that restores this map to its current state.
    /// While the scope is active, the map shares its current backing storage with
    /// the parent scope: reads see the inherited entries, and the first mutation
    /// transparently clones the storage so the parent's view is not modified.
    ///
    /// PORT: the returned closure takes the map as an argument —
    /// `let restore = c.enter_scope(); ...; restore(&mut c)` — instead of
    /// closing over `c` as the Go func does.
    pub fn enter_scope(&mut self) -> impl FnOnce(&mut Self) {
        let saved = Rc::clone(&self.m);
        move |c: &mut Self| c.m = saved
    }
}

/// CopyOnWriteSet is the set analogue of CopyOnWriteMap.
#[derive(Debug)]
pub struct CopyOnWriteSet<K> {
    m: CopyOnWriteMap<K, ()>, // Go: CopyOnWriteMap[K, struct{}]
}

impl<K> Default for CopyOnWriteSet<K> {
    fn default() -> Self {
        Self {
            m: CopyOnWriteMap::default(),
        }
    }
}

impl<K: Eq + Hash> CopyOnWriteSet<K> {
    /// Creates an empty CopyOnWriteSet (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// Has reports whether k is in the set.
    pub fn has<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.has(k)
    }

    /// Set adds k to the set, cloning the inherited backing map first if necessary.
    pub fn add(&mut self, k: K)
    where
        K: Clone,
    {
        self.m.set(k, ());
    }

    /// EnterScope returns a function that restores this set to its current state.
    /// While the scope is active, the set shares its current backing storage with
    /// the parent scope: reads see the inherited entries, and the first mutation
    /// transparently clones the storage so the parent's view is not modified.
    ///
    /// PORT: same restore-closure signature change as `CopyOnWriteMap::enter_scope`.
    pub fn enter_scope(&mut self) -> impl FnOnce(&mut Self) {
        let restore = self.m.enter_scope();
        move |s: &mut Self| restore(&mut s.m)
    }
}
