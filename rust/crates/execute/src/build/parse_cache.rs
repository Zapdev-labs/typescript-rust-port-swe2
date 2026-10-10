// Ported from tsc/internal/execute/build/parseCache.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Concurrency: Go's `parseCache` guards each entry with `sync.Mutex` so that
// concurrent builders share (and serialize) the parse of a given key. The
// port is sequential — the entry-level mutex collapses to the map's own
// `RwLock` inside `SyncMap`; a store after a compute is the sequential
// equivalent of Go's lock-then-fill.
//
// PORT(deferred): Go uses this cache for `host.resolvedReferences` and
// `host.sourceFiles`. Both values hold `Vec<Node>` arenas
// (`ParsedCommandLine`'s `TsConfigSourceFile`, `ParsedSourceFile`) and are
// `!Send`/`!Sync`, so they cannot live inside `BuildHost`, which must satisfy
// `CompilerHost: Send + Sync`. The caches are therefore not instantiated; see
// `host.rs` for the parse-per-call behaviour this defers. The generic is kept
// for parity (and for any `Send`-able consumer).

use tsc_collections::SyncMap;

/// `type parseCacheEntry[V comparable] struct` — Go keeps `value` behind
/// `mu`; the stored `Option` models Go's "zero value means unparsed".
#[derive(Clone)]
struct ParseCacheEntry<V> {
    value: Option<V>,
}

/// `type parseCache[K comparable, V comparable] struct`.
#[derive(Default)]
pub(crate) struct ParseCache<K, V> {
    entries: SyncMap<K, ParseCacheEntry<V>>,
}

impl<K, V> ParseCache<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    /// `(c *parseCache[K, V]) loadOrStore` — `allowZero` is Go's `allowZero`:
    /// a cached "zero" (absent) value is returned only when the caller allows
    /// it; otherwise the entry is re-parsed and overwritten.
    #[allow(dead_code)]
    pub(crate) fn load_or_store(
        &self,
        key: K,
        parse: impl FnOnce(&K) -> Option<V>,
        allow_zero: bool,
    ) -> Option<V> {
        if let Some(entry) = self.entries.load(&key) {
            if allow_zero || entry.value.is_some() {
                return entry.value;
            }
        }
        let value = parse(&key);
        self.entries.store(
            key,
            ParseCacheEntry {
                value: value.clone(),
            },
        );
        value
    }

    /// `(c *parseCache[K, V]) store`.
    #[allow(dead_code)]
    pub(crate) fn store(&self, key: K, value: Option<V>) {
        self.entries.store(key, ParseCacheEntry { value });
    }

    /// `(c *parseCache[K, V]) delete`.
    #[allow(dead_code)]
    pub(crate) fn delete(&self, key: &K) {
        self.entries.delete(key);
    }

    /// `(c *parseCache[K, V]) reset`.
    #[allow(dead_code)]
    pub(crate) fn reset(&self) {
        self.entries.clear();
    }
}
