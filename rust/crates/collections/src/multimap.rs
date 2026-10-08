// Ported from tsc/internal/collections/multimap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::hash::Hash;

use indexmap::{Equivalent, IndexMap};
use rustc_hash::FxBuildHasher;

/// MultiMap is a map from keys to lists of values.
///
/// PORT: Go's `M map[K][]V` iterates keys in randomized order; `IndexMap`
/// gives first-seen key insertion order. That is a strict superset of what Go
/// callers can rely on — sites that range over `M`/`Keys()`/`Values()` in Go
/// already must not depend on order, and first-seen order matches the natural
/// intent where grouping order is meaningful.
#[derive(Debug)]
pub struct MultiMap<K, V> {
    pub m: IndexMap<K, Vec<V>, FxBuildHasher>,
}

impl<K, V> Default for MultiMap<K, V> {
    fn default() -> Self {
        Self {
            m: IndexMap::default(),
        }
    }
}

impl<K: Eq + Hash, V> MultiMap<K, V> {
    /// Creates an empty MultiMap (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// NewMultiMapWithSizeHint creates a new MultiMap with a hint for the number of keys it will contain.
    pub fn with_size_hint(hint: usize) -> Self {
        Self {
            m: IndexMap::with_capacity_and_hasher(hint, FxBuildHasher),
        }
    }

    /// Has returns true if the map contains the key.
    pub fn has<Q>(&self, key: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.m.contains_key(key)
    }

    /// Get returns the values for the key.
    ///
    /// PORT: Go returns the nil slice on a miss (`len(nil) == 0`); an empty
    /// slice is returned here for the same effect.
    pub fn get<Q>(&self, key: &Q) -> &[V]
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.m.get(key).map_or(&[], Vec::as_slice)
    }

    /// PORT: not in the Go API — Go callers mutate the slice via `m.M[k]`;
    /// `get_mut` is the in-place equivalent.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut Vec<V>>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.m.get_mut(key)
    }

    /// Add appends value to the list for key, creating the list if necessary.
    pub fn add(&mut self, key: K, value: V) {
        self.m.entry(key).or_default().push(value);
    }

    /// Remove removes the first occurrence of value from the list for key,
    /// deleting the key when the list becomes empty.
    pub fn remove<Q>(&mut self, key: &Q, value: &V)
    where
        V: PartialEq,
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let Some(values) = self.m.get_mut(key) else {
            return;
        };
        let Some(i) = values.iter().position(|v| v == value) else {
            return;
        };
        if values.len() == 1 {
            // Order-preserving removal (see type-level PORT note).
            self.m.shift_remove(key);
        } else {
            values.remove(i);
        }
    }

    /// RemoveAll removes the key and all its values from the map.
    pub fn remove_all<Q>(&mut self, key: &Q)
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.m.shift_remove(key);
    }

    /// Len returns the number of keys in the map.
    pub fn len(&self) -> usize {
        self.m.len()
    }

    /// IsEmpty returns true if the map contains no keys.
    pub fn is_empty(&self) -> bool {
        self.m.is_empty()
    }

    /// Keys returns an iterator over the keys in the map.
    ///
    /// PORT: Go's order is randomized; here it is first-seen key order.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.m.keys()
    }

    /// Values returns an iterator over the value lists in the map.
    ///
    /// PORT: Go's order is randomized; here it is first-seen key order.
    pub fn values(&self) -> impl Iterator<Item = &[V]> {
        self.m.values().map(Vec::as_slice)
    }

    /// Clear removes all keys and values from the map.
    pub fn clear(&mut self) {
        self.m.clear();
    }
}

impl<K: Clone + Eq + Hash, V: Clone> Clone for MultiMap<K, V> {
    fn clone(&self) -> Self {
        Self { m: self.m.clone() }
    }
}

/// GroupBy groups items into a MultiMap keyed by groupId(item).
///
/// PORT: Go's `groupId func(V) K` takes the item by value; here it borrows
/// since the item is stored into the map immediately after.
pub fn group_by<K, V>(
    items: impl IntoIterator<Item = V>,
    mut group_id: impl FnMut(&V) -> K,
) -> MultiMap<K, V>
where
    K: Eq + Hash,
{
    let items = items.into_iter();
    let mut m = MultiMap {
        m: IndexMap::with_capacity_and_hasher(items.size_hint().0, FxBuildHasher),
    };
    for item in items {
        m.add(group_id(&item), item);
    }
    m
}
