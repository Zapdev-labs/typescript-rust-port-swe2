// Ported from tsc/internal/project/dirty/{interfaces.go,cloneablemap.go} @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;

/// `Cloneable[T]` — Go's `Cloneable` interface (`Clone() T`).
///
/// Go relies on two distinct copy operations on these value types:
///
/// - plain assignment (`e.value = v`, `original: val`) — a shallow descriptor
///   copy that shares the pointee/backing store for pointer and map types;
/// - the `Clone()` method — a fresh, independently mutable copy used by the
///   copy-on-write paths (`change`), so a mutating `apply` never touches the
///   snapshot's base value.
///
/// In this port, `Clone::clone` plays the role of Go's assignment: for
/// `Rc`/`Arc`-backed handle types it should be a shallow handle copy. Types
/// stored in [`crate::Map`], [`crate::SyncMap`], or [`crate::Box`] MUST
/// implement `clone_value` to return a fresh, independently mutable value —
/// the equivalent of Go's user-defined `Clone()` (e.g. `maps.Clone`, a deep
/// copy of the pointee). There is deliberately no blanket `impl` for `T:
/// Clone`: silently treating `Rc::clone` as `Clone()` would break
/// copy-on-write isolation.
pub trait Cloneable: Clone {
    /// Go's `Clone()` — a fresh, independently mutable copy.
    fn clone_value(&self) -> Self;
}

/// `Cloneable` for `Rc<T>` — Go's `*T` is cloneable when `T` has `Clone()`.
/// `Clone::clone` is Go's pointer assignment (shared pointee);
/// `clone_value` is Go's `T.Clone()` + fresh pointer (`&clone`).
impl<T: Cloneable> Cloneable for Rc<T> {
    fn clone_value(&self) -> Self {
        Rc::new((**self).clone_value())
    }
}

/// `Cloneable` for `Option<T>` — a nil-able value type is cloneable when
/// its payload is. `Clone::clone` is Go's assignment semantics (a shallow
/// copy of the payload); `clone_value` deep-copies the payload.
impl<T: Cloneable> Cloneable for Option<T> {
    fn clone_value(&self) -> Self {
        self.as_ref().map(Cloneable::clone_value)
    }
}

/// `Cloneable` for plain `FxHashMap` — for value-typed entries `Clone::clone`
/// is already a fresh copy, matching both Go assignment and `maps.Clone`
/// (Go `map[K]*T` clones share pointers; store `Rc`/`Arc` values to mirror).
impl<K: Eq + std::hash::Hash + Clone, V: Clone> Cloneable for FxHashMap<K, V> {
    fn clone_value(&self) -> Self {
        self.clone()
    }
}

/// `CloneableMap[K, V]` — Go's named `map[K]V` type whose `Clone()` is
/// `maps.Clone`.
///
/// Go maps are reference types: assignment and `Value()` returns share the
/// backing table. This port wraps the table in `Rc<RefCell<…>>` to preserve
/// that sharing: `Clone::clone` shares the table (Go assignment), while
/// `clone_value` produces a fresh table (`maps.Clone`).
#[derive(Debug)]
pub struct CloneableMap<K, V>(pub Rc<RefCell<FxHashMap<K, V>>>);

impl<K, V> CloneableMap<K, V> {
    /// `make(CloneableMap[K, V])`.
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(FxHashMap::default())))
    }

    /// Wrap an existing map without copying it.
    pub fn from_map(map: FxHashMap<K, V>) -> Self {
        Self(Rc::new(RefCell::new(map)))
    }

    /// `len(m)`.
    pub fn len(&self) -> usize {
        self.0.borrow().len()
    }

    /// `len(m) == 0`.
    pub fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }
}

impl<K, V> Default for CloneableMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Clone for CloneableMap<K, V> {
    /// Go map assignment — shares the backing table.
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<K: Eq + std::hash::Hash + Clone, V: Clone> Cloneable for CloneableMap<K, V> {
    /// `maps.Clone` — a fresh table with cloned entries.
    fn clone_value(&self) -> Self {
        Self(Rc::new(RefCell::new(self.0.borrow().clone())))
    }
}
