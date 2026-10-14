// Ported from tsc/internal/project/ownercache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex};

use tsc_collections::{Set, SyncMap};

/// `ownerCacheEntry`.
pub struct OwnerCacheEntry<V> {
    pub value: Option<V>,
    pub owners: Set<u64>,
}

/// `OwnerCache` is like [`crate::refcountcache::RefCountCache`], but each
/// entry tracks the set of its owners instead of a count. We use this to
/// associate extended config cache entries with each snapshot that contains
/// them, since the same config can be Acquired multiple times during config
/// parsing while only appearing once in the ParsedCommandLine's list of
/// extended files. When updating this code, check if the same changes should
/// be made to RefCountCache as well.
pub struct OwnerCache<K, V, LoadArgs> {
    entries: SyncMap<K, Arc<Mutex<OwnerCacheEntry<V>>>>,

    is_expired: Option<Box<dyn Fn(&K, &V, &LoadArgs) -> bool + Send + Sync>>,
    parse: Box<dyn Fn(&K, &LoadArgs) -> V + Send + Sync>,
}

impl<K, V, LoadArgs> OwnerCache<K, V, LoadArgs>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    /// `NewOwnerCache`.
    pub fn new(
        parse: impl Fn(&K, &LoadArgs) -> V + Send + Sync + 'static,
        is_expired: Option<impl Fn(&K, &V, &LoadArgs) -> bool + Send + Sync + 'static>,
    ) -> OwnerCache<K, V, LoadArgs> {
        OwnerCache {
            entries: SyncMap::new(),
            is_expired: is_expired.map(|f| Box::new(f) as _),
            parse: Box::new(parse),
        }
    }

    /// Entry count — for verbose cache-statistics logging.
    pub fn entry_count(&self) -> usize {
        let mut n = 0;
        self.entries.range(|_, _| {
            n += 1;
            true
        });
        n
    }

    /// `(c *OwnerCache) LoadAndAcquire`.
    pub fn load_and_acquire(&self, identity: K, owner: u64, load_args: &LoadArgs) -> V {
        let (entry, loaded) = self.load_or_store_locked_entry(identity.clone());
        let mut entry = entry.lock().unwrap();
        if !loaded
            || self
                .is_expired
                .as_ref()
                .is_some_and(|is_expired| {
                    is_expired(&identity, entry.value.as_ref().unwrap(), load_args)
                })
        {
            entry.value = Some((self.parse)(&identity, load_args));
        }
        entry.owners.add(owner);
        entry.value.as_ref().unwrap().clone()
    }

    /// `(c *OwnerCache) Acquire`.
    pub fn acquire(&self, identity: K, owner: u64, value: V) {
        let (entry, loaded) = self.load_or_store_locked_entry(identity);
        let mut entry = entry.lock().unwrap();
        if !loaded {
            entry.value = Some(value);
        }
        entry.owners.add(owner);
    }

    /// `AddOwner` adds an owner to an existing live entry. The entry must
    /// exist and have at least one current owner; callers must ensure the
    /// entry is kept alive (e.g. via snapshot ref counting).
    pub fn add_owner(&self, identity: &K, owner: u64) {
        let Some(entry) = self.entries.load(identity) else {
            panic!("OwnerCache.AddOwner: entry not found")
        };
        let mut entry = entry.lock().unwrap();
        if entry.owners.is_empty() {
            panic!("OwnerCache.AddOwner: entry has no owners");
        }
        entry.owners.add(owner);
    }

    /// `(c *OwnerCache) Has`.
    pub fn has(&self, identity: &K) -> bool {
        self.entries.load(identity).is_some()
    }

    /// `(c *OwnerCache) Release`.
    pub fn release(&self, identity: &K, owner: u64) {
        let Some(entry) = self.entries.load(identity) else {
            return;
        };
        let mut entry = entry.lock().unwrap();
        entry.owners.delete(&owner);
        if entry.owners.is_empty() {
            drop(entry);
            self.entries.delete(identity);
        }
    }

    /// `loadOrStoreLockedEntry` — see [`RefCountCache`] for the PORT note on
    /// returning the `Arc` rather than a held lock guard. `loaded == false`
    /// means the entry was just stored (empty `owners`); `loaded == true`
    /// returns a live existing entry.
    fn load_or_store_locked_entry(&self, key: K) -> (Arc<Mutex<OwnerCacheEntry<V>>>, bool) {
        let entry = Arc::new(Mutex::new(OwnerCacheEntry {
            value: None,
            owners: Set::new(),
        }));
        let (existing, loaded) = self.entries.load_or_store(key.clone(), entry.clone());
        if loaded {
            let existing_locked = existing.lock().unwrap();
            if existing_locked.owners.is_empty() {
                drop(existing_locked);
                return self.load_or_store_locked_entry(key);
            }
            drop(existing_locked);
            return (existing, true);
        }
        (entry, false)
    }
}
