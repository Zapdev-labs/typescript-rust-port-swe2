// Ported from tsc/internal/collections/set.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Borrow;
use std::hash::Hash;

use rustc_hash::{FxBuildHasher, FxHashSet};

/// Set is an unordered set.
///
/// PORT: Go's `M` is a public `map[T]struct{}`; `m` keeps that public-field
/// shape as an `FxHashSet<T>`. Go map iteration order is randomized, so no
/// consumer may depend on it — FxHashSet's deterministic-but-arbitrary
/// iteration order is a valid realization.
#[derive(Debug)]
pub struct Set<T> {
    pub m: FxHashSet<T>,
}

impl<T> Default for Set<T> {
    fn default() -> Self {
        Self {
            m: FxHashSet::default(),
        }
    }
}

impl<T: Eq + Hash> Set<T> {
    /// Creates an empty Set (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// NewSetWithSizeHint creates a new Set with a hint for the number of elements it will contain.
    pub fn with_size_hint(hint: usize) -> Self {
        Self {
            m: FxHashSet::with_capacity_and_hasher(hint, FxBuildHasher),
        }
    }

    /// Has returns true if the set contains the key.
    ///
    /// PORT: Go's nil receiver returns false; `Option<Set>` receivers use
    /// `s.map_or(false, |s| s.has(k))` or `s.is_some_and(...)` at call sites.
    pub fn has<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.contains(key)
    }

    /// Add adds the key to the set.
    pub fn add(&mut self, key: T) {
        self.m.insert(key);
    }

    /// Delete removes the key from the set.
    ///
    /// PORT: returns whether the key was present (Go returns nothing; the bool
    /// is free and helps call sites porting delete-and-check patterns).
    pub fn delete<Q>(&mut self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.remove(key)
    }

    /// Len returns the number of elements in the set.
    ///
    /// PORT: Go's nil receiver returns 0.
    pub fn len(&self) -> usize {
        self.m.len()
    }

    /// IsEmpty returns true if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.m.is_empty()
    }

    /// Keys returns the backing set.
    ///
    /// PORT: Go returns the `map[T]struct{}` itself; the `&FxHashSet<T>` here
    /// can be iterated (`for k in s.keys()`), counted (`.len()`), or queried
    /// (`.contains(k)`), covering every Go usage.
    pub fn keys(&self) -> &FxHashSet<T> {
        &self.m
    }

    /// Clear removes all elements from the set.
    ///
    /// PORT: Go's nil receiver is a no-op.
    pub fn clear(&mut self) {
        self.m.clear();
    }

    /// AddIfAbsent returns true if the key was not already present in the set.
    pub fn add_if_absent(&mut self, key: T) -> bool {
        self.m.insert(key)
    }
}

impl<T: Clone + Eq + Hash> Clone for Set<T> {
    /// Clone returns a shallow copy of the set.
    fn clone(&self) -> Self {
        Self { m: self.m.clone() }
    }
}

impl<T: Eq + Hash> Set<T> {
    /// Union adds all elements of other to this set.
    ///
    /// PORT: Go's nil `other` is an `Option` (None = empty set). A nil receiver
    /// panics in Go ("cannot modify nil Set"); `Option<Set>` receivers can't
    /// call `&mut` methods on `None`, which surfaces the same bug.
    pub fn union(&mut self, other: Option<&Self>)
    where
        T: Clone,
    {
        if let Some(other) = other {
            self.m.extend(other.m.iter().cloned());
        }
    }

    /// UnionedWith returns a new set with the union of this set and other.
    /// A nil result is returned iff both sets are nil.
    ///
    /// PORT: Go's possibly-nil receivers/arguments are `Option<&Set>`; call as
    /// `Set::unioned_with(a.as_ref(), b.as_ref())`.
    pub fn unioned_with(this: Option<&Self>, other: Option<&Self>) -> Option<Self>
    where
        T: Clone,
    {
        if this.is_none() && other.is_none() {
            return None;
        }
        let mut result = this.cloned().unwrap_or_default();
        if let Some(other) = other {
            result.m.extend(other.m.iter().cloned());
        }
        Some(result)
    }

    /// Equals returns true if both sets contain the same elements.
    /// A nil set differs from a non-nil empty set.
    ///
    /// PORT: call as `Set::equals(a.as_ref(), b.as_ref())`.
    pub fn equals(this: Option<&Self>, other: Option<&Self>) -> bool {
        match (this, other) {
            (None, None) => true,
            (Some(a), Some(b)) => std::ptr::eq(a, b) || a.m == b.m,
            _ => false,
        }
    }

    /// IsSubsetOf returns true if all elements of this set are in other.
    /// A nil set is a subset of every set; a nil other contains nothing.
    ///
    /// PORT: call as `Set::is_subset_of(a.as_ref(), b.as_ref())`.
    pub fn is_subset_of(this: Option<&Self>, other: Option<&Self>) -> bool {
        let Some(this) = this else {
            return true;
        };
        this.m
            .iter()
            .all(|key| other.is_some_and(|o| o.m.contains(key)))
    }

    /// Intersects returns true if the sets share at least one element.
    /// Nil sets never intersect.
    ///
    /// PORT: call as `Set::intersects(a.as_ref(), b.as_ref())`.
    pub fn intersects(this: Option<&Self>, other: Option<&Self>) -> bool {
        match (this, other) {
            (Some(a), Some(b)) => a.m.iter().any(|key| b.m.contains(key)),
            _ => false,
        }
    }
}

impl<T: Eq + Hash> PartialEq for Set<T> {
    fn eq(&self, other: &Self) -> bool {
        self.m == other.m
    }
}

impl<T: Eq + Hash> Eq for Set<T> {}

/// NewSetFromItems creates a Set containing the given items.
pub fn new_set_from_items<T: Eq + Hash>(items: impl IntoIterator<Item = T>) -> Set<T> {
    let mut s = Set::default();
    for item in items {
        s.add(item);
    }
    s
}
