// Ported from tsc/internal/collections/syncset.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Borrow;
use std::hash::Hash;

use crate::syncmap::SyncMap;

/// SyncSet is a thread-safe set built on SyncMap.
pub struct SyncSet<T> {
    m: SyncMap<T, ()>, // Go: SyncMap[T, struct{}]
}

impl<T> Default for SyncSet<T> {
    fn default() -> Self {
        Self {
            m: SyncMap::default(),
        }
    }
}

impl<T: Eq + Hash> SyncSet<T> {
    /// Creates an empty SyncSet (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// Has returns true if the set contains the key.
    pub fn has<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.load(key).is_some()
    }

    /// Add adds the key to the set.
    pub fn add(&self, key: T) {
        self.add_if_absent(key);
    }

    /// AddIfAbsent adds the key to the set if it is not already present
    /// using LoadOrStore. It returns true if the key was not already present
    /// (opposite of the return value of LoadOrStore).
    pub fn add_if_absent(&self, key: T) -> bool {
        let (_, loaded) = self.m.load_or_store(key, ());
        !loaded
    }

    /// Delete removes the key from the set.
    pub fn delete<Q>(&self, key: &Q)
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.delete(key);
    }

    /// Range calls f for each key in the set until f returns false.
    ///
    /// PORT: iterates a cloned snapshot — see `SyncMap::range`.
    pub fn range(&self, mut f: impl FnMut(T) -> bool)
    where
        T: Clone,
    {
        self.m.range(|k, ()| f(k));
    }

    /// Size returns the approximate number of items in the map.
    /// Note that this is not a precise count, as the map may be modified
    /// concurrently while this method is running.
    pub fn size(&self) -> usize {
        self.m.size()
    }

    /// IsEmpty returns true if the set contains no keys.
    ///
    /// PORT: Go ranges with an early exit; checking `size() == 0` is equivalent.
    pub fn is_empty(&self) -> bool {
        self.m.size() == 0
    }

    /// ToSlice returns a snapshot of the keys as a slice.
    pub fn to_slice(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.m.keys()
    }

    /// Keys returns a snapshot of the keys in the set.
    ///
    /// PORT: Go returns an `iter.Seq` driven by `Range`; the snapshot Vec is
    /// the owned equivalent.
    pub fn keys(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.m.keys()
    }
}
