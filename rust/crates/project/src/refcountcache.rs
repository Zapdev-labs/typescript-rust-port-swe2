// Ported from tsc/internal/project/refcountcache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex};

use tsc_collections::SyncMap;

/// `refCountCacheEntry` — `mu` becomes `Mutex<RefCountCacheEntry>`: the Go
/// pattern of storing `*entry` and locking it before use is `Arc<Mutex<…>>`.
pub struct RefCountCacheEntry<V> {
    pub value: Option<V>,
    pub ref_count: i32,
}

/// `RefCountCacheOptions`.
#[derive(Clone, Default)]
pub struct RefCountCacheOptions {
    /// DisableDeletion prevents entries from being removed from the cache.
    /// Used for testing.
    pub disable_deletion: bool,
}

/// `RefCountCache[K, V, AcquireArgs]`.
///
/// `parse` is stored as a trait object so the cache stays usable behind
/// `Arc`; `entries` is `collections.SyncMap` exactly as in Go.
pub struct RefCountCache<K, V, AcquireArgs> {
    pub options: RefCountCacheOptions,
    entries: SyncMap<K, Arc<Mutex<RefCountCacheEntry<V>>>>,

    parse: Box<dyn Fn(&K, &AcquireArgs) -> V + Send + Sync>,
}

impl<K, V, AcquireArgs> RefCountCache<K, V, AcquireArgs>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    /// `NewRefCountCache`.
    pub fn new(
        options: RefCountCacheOptions,
        parse: impl Fn(&K, &AcquireArgs) -> V + Send + Sync + 'static,
    ) -> RefCountCache<K, V, AcquireArgs> {
        RefCountCache {
            options,
            entries: SyncMap::new(),
            parse: Box::new(parse),
        }
    }

    /// `Acquire` retrieves or creates a cache entry for the given identity and
    /// hash. If an entry exists with matching identity and hash, its refcount
    /// is incremented and the cached value is returned. Otherwise, parse() is
    /// called to create the value, which is stored and returned with refcount 1.
    ///
    /// The caller is responsible for calling Deref when done with the value.
    pub fn acquire(&self, identity: K, acquire_args: &AcquireArgs) -> V {
        let (entry, loaded) = self.load_or_store_new_locked_entry(identity.clone());
        let mut entry = entry.lock().unwrap();
        if !loaded {
            // New entry - parse the value
            entry.value = Some((self.parse)(&identity, acquire_args));
            return entry.value.as_ref().unwrap().clone();
        }
        entry.value.as_ref().unwrap().clone()
    }

    /// `(c *RefCountCache) Has`.
    pub fn has(&self, identity: &K) -> bool {
        self.entries.load(identity).is_some()
    }

    /// `AcquireExisting` retrieves an existing entry and increments its
    /// reference count. It returns `None` without producing a value when no
    /// live entry exists.
    ///
    /// The caller is responsible for calling Deref when a value is returned.
    pub fn acquire_existing(&self, identity: &K) -> Option<V> {
        let entry = self.entries.load(identity)?;
        let mut entry = entry.lock().unwrap();
        if entry.ref_count <= 0 && !self.options.disable_deletion {
            return None;
        }
        entry.ref_count += 1;
        Some(entry.value.as_ref().unwrap().clone())
    }

    /// `AcquireOrError` retrieves an existing entry (incrementing its refcount)
    /// or produces a new one via `produce`. If `produce` returns an error, no
    /// entry is stored and the error is returned, so callers can cache only
    /// successful results. `produce` runs while holding the new entry's lock,
    /// so concurrent acquisitions of the same identity that miss serialize on it.
    ///
    /// The caller is responsible for calling Deref when a value is returned
    /// without error.
    pub fn acquire_or_error<E>(
        &self,
        identity: K,
        produce: impl FnOnce() -> Result<V, E>,
    ) -> Result<V, E> {
        let (entry, loaded) = self.load_or_store_new_locked_entry(identity.clone());
        let mut entry = entry.lock().unwrap();
        if loaded {
            return Ok(entry.value.as_ref().unwrap().clone());
        }
        match produce() {
            Ok(value) => {
                entry.value = Some(value.clone());
                Ok(value)
            }
            Err(err) => {
                // Undo the speculative entry so failures are not cached.
                entry.ref_count = 0;
                drop(entry);
                self.entries.delete(&identity);
                Err(err)
            }
        }
    }

    /// `Ref` increments the reference count for an existing entry.
    /// Panics if the entry does not exist.
    pub fn ref_(&self, identity: &K) {
        let Some(entry) = self.entries.load(identity) else {
            panic!("cache entry not found")
        };
        let mut entry = entry.lock().unwrap();
        if entry.ref_count <= 0 && !self.options.disable_deletion {
            // Entry was deleted while we were acquiring the lock
            let value = entry.value.clone();
            drop(entry);
            let (new_entry, _) = self.load_or_store_new_locked_entry(identity.clone());
            new_entry.lock().unwrap().value = value;
            return;
        }
        entry.ref_count += 1;
    }

    /// `Deref` decrements the reference count for an entry.
    /// When the refcount reaches zero, the entry is removed from the cache
    /// (unless DisableDeletion is set).
    pub fn deref(&self, identity: &K) {
        let Some(entry) = self.entries.load(identity) else {
            return;
        };
        let mut entry = entry.lock().unwrap();
        entry.ref_count -= 1;
        if entry.ref_count <= 0 && !self.options.disable_deletion {
            drop(entry);
            self.entries.delete(identity);
        }
    }

    /// `loadOrStoreNewLockedEntry` loads an existing entry or creates a new
    /// one. The returned entry's mutex is locked and its refCount is
    /// incremented (or initialized to 1 in the case of a new entry).
    ///
    /// PORT: Rust cannot return the lock guard, so this returns the entry
    /// `Arc`; callers lock it themselves. `loaded == false` means the entry is
    /// freshly stored with `ref_count == 1`; `loaded == true` means the
    /// existing entry's `ref_count` was already incremented.
    fn load_or_store_new_locked_entry(
        &self,
        key: K,
    ) -> (Arc<Mutex<RefCountCacheEntry<V>>>, bool) {
        let entry = Arc::new(Mutex::new(RefCountCacheEntry {
            value: None,
            ref_count: 1,
        }));
        let (existing, loaded) = self.entries.load_or_store(key.clone(), entry.clone());
        if loaded {
            let mut existing_locked = existing.lock().unwrap();
            if existing_locked.ref_count <= 0 && !self.options.disable_deletion {
                // Existing entry was deleted while we were acquiring the lock
                drop(existing_locked);
                return self.load_or_store_new_locked_entry(key);
            }
            existing_locked.ref_count += 1;
            drop(existing_locked);
            return (existing, true);
        }
        (entry, false)
    }
}
