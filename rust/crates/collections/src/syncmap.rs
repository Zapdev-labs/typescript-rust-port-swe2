// Ported from tsc/internal/collections/syncmap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Borrow;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use std::sync::RwLock;

use rustc_hash::FxHashMap;

/// SyncMap is a thread-safe map — the Go port's `sync.Map` wrapper.
///
/// PORT: `sync.Map` becomes `RwLock<FxHashMap>`. Deviations forced by Rust:
/// - `load`/`load_or_store`/`range`/`to_map`/`keys`/`clone` return owned
///   clones — references cannot outlive the lock. Go's `any` copies were
///   shallow anyway (pointer-ish `V` should be `Rc`/`Arc`/an id, keeping the
///   clone cheap and the sharing identical).
/// - `range` iterates a snapshot collected under the read lock, then calls `f`
///   without holding it — `sync.Map::Range` does the same internally (it
///   iterates a readOnly snapshot), so callbacks may call back into the map
///   without deadlock.
/// - Iteration order is unspecified, exactly as with `sync.Map`. Go consumers
///   in the wild call `Range`/`Keys`/`ToMap`/`Clone` on these maps (e.g.
///   execute/incremental snapshots) — none may depend on the order, and
///   FxHashMap's order is deterministic per process but arbitrary.
pub struct SyncMap<K, V> {
    m: RwLock<FxHashMap<K, V>>,
}

impl<K, V> Default for SyncMap<K, V> {
    fn default() -> Self {
        Self {
            m: RwLock::new(FxHashMap::default()),
        }
    }
}

impl<K: Eq + Hash, V> SyncMap<K, V> {
    /// Creates an empty SyncMap (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// Load returns the value stored for key, or None if absent.
    ///
    /// PORT: Go returns `(V, bool)` where V may itself be a nil-able type; use
    /// `Option<V>` as the stored type for that (the outer Option is presence).
    pub fn load<Q>(&self, key: &Q) -> Option<V>
    where
        V: Clone,
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.read().unwrap().get(key).cloned()
    }

    /// Store sets the value for key.
    pub fn store(&self, key: K, value: V) {
        self.m.write().unwrap().insert(key, value);
    }

    /// LoadOrStore returns the existing value for key if present, otherwise
    /// stores and returns `value`. The bool is true if the value was loaded.
    pub fn load_or_store(&self, key: K, value: V) -> (V, bool)
    where
        V: Clone,
    {
        let mut m = self.m.write().unwrap();
        match m.entry(key) {
            Entry::Occupied(e) => (e.get().clone(), true),
            Entry::Vacant(e) => {
                e.insert(value.clone());
                (value, false)
            }
        }
    }

    /// Delete removes the key from the map.
    pub fn delete<Q>(&self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.m.write().unwrap().remove(key);
    }

    /// Clear removes all entries from the map.
    pub fn clear(&self) {
        self.m.write().unwrap().clear();
    }

    /// Range calls f for each entry in the map until f returns false.
    ///
    /// PORT: iterates a cloned snapshot — the callback may mutate the map.
    pub fn range(&self, mut f: impl FnMut(K, V) -> bool)
    where
        K: Clone,
        V: Clone,
    {
        let entries: Vec<(K, V)> = self
            .m
            .read()
            .unwrap()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (k, v) in entries {
            if !f(k, v) {
                break;
            }
        }
    }

    /// Size returns the approximate number of items in the map.
    /// Note that this is not a precise count, as the map may be modified
    /// concurrently while this method is running.
    pub fn size(&self) -> usize {
        self.m.read().unwrap().len()
    }

    /// ToMap returns a snapshot of the map as a plain FxHashMap.
    pub fn to_map(&self) -> FxHashMap<K, V>
    where
        K: Clone,
        V: Clone,
    {
        self.m.read().unwrap().clone()
    }

    /// Keys returns a snapshot of the keys in the map.
    ///
    /// PORT: Go returns an `iter.Seq` driven by `Range`; the snapshot Vec is
    /// the owned equivalent (`for k in m.keys()` works identically).
    pub fn keys(&self) -> Vec<K>
    where
        K: Clone,
    {
        self.m.read().unwrap().keys().cloned().collect()
    }
}

impl<K: Clone + Eq + Hash, V: Clone> Clone for SyncMap<K, V> {
    /// Clone returns a snapshot copy of the map.
    fn clone(&self) -> Self {
        Self {
            m: RwLock::new(self.m.read().unwrap().clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TestSyncMapWithNil — PORT: Go uses `SyncMap[string, any]` with nil values;
    // Rust models the nil-able payload as `Option<V>`, so `Some(None)` is
    // "present with nil value".
    #[test]
    fn sync_map_with_nil() {
        let m = SyncMap::<String, Option<i32>>::new();

        let got1 = m.load("foo");
        assert_eq!(got1, None);

        m.store("foo".to_string(), None);

        let got2 = m.load("foo");
        assert_eq!(got2, Some(None));

        let (too, loaded) = m.load_or_store("too".to_string(), None);
        assert!(!loaded);
        assert_eq!(too, None);

        m.range(|_k: String, _v: Option<i32>| true);
    }
}
