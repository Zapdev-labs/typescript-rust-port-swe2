// Ported from tsc/internal/project/dirty/syncmap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard, Weak};

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_collections::SyncMap as GoSyncMap;

use crate::cloneable::Cloneable;
use crate::entry::EntryState;
use crate::value::Value;

type SyncState<K, V> = Mutex<SyncEntryState<K, V>>;

struct SyncEntryState<K: Eq + Hash + Clone, V: Cloneable> {
    entry: EntryState<K, V>,
    /// `proxyFor` — set when this entry loses a race to become the dirty
    /// entry for a value. Since two threads hold references to two entries
    /// that may try to mutate the same underlying value, all mutations are
    /// routed through the one that actually exists in the dirty map.
    proxy_for: Option<SyncMapEntry<K, V>>,
}

struct SyncEntryShared<K: Eq + Hash + Clone, V: Cloneable> {
    /// `Weak` so the map can be dropped once its outside handles are gone;
    /// entries created while the map lives always upgrade successfully. Go
    /// keeps the map alive via the entry's back-pointer — a `Weak` means
    /// racing `change`/`delete` on an entry whose map was dropped degrades
    /// to local copy-on-write instead (documented deviation; cannot happen
    /// while the `SyncMap` handle is held).
    map: Weak<SyncMapShared<K, V>>,
    /// `mu` — one mutex per entry, exactly like Go's embedded `sync.Mutex`.
    state: SyncState<K, V>,
}

/// `*SyncMapEntry[K, V]` — a handle to one tracked entry.
pub struct SyncMapEntry<K: Eq + Hash + Clone, V: Cloneable> {
    shared: Arc<SyncEntryShared<K, V>>,
}

impl<K: Eq + Hash + Clone, V: Cloneable> Clone for SyncMapEntry<K, V> {
    /// Go `*SyncMapEntry` copy — shares the entry.
    fn clone(&self) -> Self {
        SyncMapEntry {
            shared: Arc::clone(&self.shared),
        }
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable> SyncMapEntry<K, V> {
    fn from_base(map: &Arc<SyncMapShared<K, V>>, key: K, base_value: V) -> SyncMapEntry<K, V> {
        SyncMapEntry {
            shared: Arc::new(SyncEntryShared {
                map: Arc::downgrade(map),
                state: Mutex::new(SyncEntryState {
                    entry: EntryState {
                        key,
                        original: Some(base_value.clone()),
                        value: Some(base_value),
                        dirty: false,
                        delete: false,
                    },
                    proxy_for: None,
                }),
            }),
        }
    }

    fn lock_state(&self) -> MutexGuard<'_, SyncEntryState<K, V>> {
        self.shared.state.lock().unwrap()
    }

    fn upgrade_map(&self) -> Option<Arc<SyncMapShared<K, V>>> {
        self.shared.map.upgrade()
    }

    /// `e.Key()`.
    pub fn key(&self) -> K {
        self.lock_state().entry.key.clone()
    }

    /// `e.Value()` — `None` is the Go zero value (a deleted entry).
    pub fn value(&self) -> Option<V> {
        let st = self.lock_state();
        if let Some(proxy) = &st.proxy_for {
            return proxy.clone().value();
        }
        st.entry.value()
    }

    /// `e.Original()` — `None` is the Go zero value.
    pub fn original(&self) -> Option<V> {
        let st = self.lock_state();
        if let Some(proxy) = &st.proxy_for {
            return proxy.clone().original();
        }
        st.entry.original.clone()
    }

    /// `e.Dirty()`.
    pub fn dirty(&self) -> bool {
        let st = self.lock_state();
        if let Some(proxy) = &st.proxy_for {
            return proxy.clone().dirty();
        }
        st.entry.dirty
    }

    /// `e.Locked(fn)` — runs `fn` against a lock-held [`Value`] view while
    /// holding the entry's mutex.
    pub fn locked(&self, mut f: impl FnMut(&mut dyn Value<V>)) {
        let mut st = self.lock_state();
        if let Some(proxy) = st.proxy_for.clone() {
            drop(st);
            proxy.locked(f);
            return;
        }
        let mut locked = LockedEntry {
            entry: self.clone(),
            state: &mut *st,
        };
        f(&mut locked);
    }

    /// `e.Change(apply)`.
    pub fn change(&self, apply: impl FnOnce(&mut V)) {
        let mut st = self.lock_state();
        if let Some(proxy) = st.proxy_for.clone() {
            drop(st);
            proxy.change(apply);
            return;
        }
        self.change_locked(&mut st, apply);
    }

    /// `e.changeLocked(apply)` — `e`'s mutex must already be held (`st`).
    ///
    /// PORT: Go's `entry.mu.Lock()` on a `LoadOrStore` loser deadlocks when
    /// the winner is `e` itself (Go's mutex is non-reentrant); `Mutex::lock`
    /// deadlocks identically here.
    fn change_locked(&self, st: &mut SyncEntryState<K, V>, apply: impl FnOnce(&mut V)) {
        if st.entry.dirty {
            apply(
                st.entry
                    .value
                    .as_mut()
                    .expect("apply on a dirty entry with no value (Go would pass the zero value)"),
            );
            return;
        }

        let Some(map) = self.upgrade_map() else {
            // Map dropped: degrade to local copy-on-write (Go keeps the map
            // alive through the entry's back-pointer — see `map` field).
            st.entry.value = st
                .entry
                .value
                .as_ref()
                .map(Cloneable::clone_value);
            st.entry.dirty = true;
            apply(
                st.entry
                    .value
                    .as_mut()
                    .expect("apply on an entry with no value (Go would pass the zero value)"),
            );
            return;
        };
        let (entry, loaded) = map
            .dirty
            .load_or_store(st.entry.key.clone(), self.clone());
        if loaded {
            let mut est = entry.lock_state();
            if !est.entry.dirty {
                est.entry.value = est
                    .entry
                    .value
                    .as_ref()
                    .map(Cloneable::clone_value);
                est.entry.dirty = true;
            }
            st.proxy_for = Some(entry.clone());
            st.entry.value = est.entry.value.clone();
            st.entry.dirty = true;
            st.entry.delete = est.entry.delete;
            apply(
                est.entry
                    .value
                    .as_mut()
                    .expect("apply on an entry with no value (Go would pass the zero value)"),
            );
        } else {
            // `entry` is `self`, now stored.
            st.entry.value = st
                .entry
                .value
                .as_ref()
                .map(Cloneable::clone_value);
            st.entry.dirty = true;
            apply(
                st.entry
                    .value
                    .as_mut()
                    .expect("apply on an entry with no value (Go would pass the zero value)"),
            );
        }
    }

    /// `e.ChangeIf(cond, apply)` — `cond` sees the raw stored value (Go
    /// `cond(e.value)`, not `Value()`), wrapped in `Some`; `None` only if the
    /// entry never had a value (Go would pass the zero value).
    pub fn change_if(
        &self,
        cond: impl FnOnce(Option<V>) -> bool,
        apply: impl FnOnce(&mut V),
    ) -> bool {
        let mut st = self.lock_state();
        if let Some(proxy) = st.proxy_for.clone() {
            drop(st);
            return proxy.change_if(cond, apply);
        }
        if cond(st.entry.value.clone()) {
            self.change_locked(&mut st, apply);
            return true;
        }
        false
    }

    /// `e.Delete()`.
    ///
    /// PORT: preserves Go's quirk — when the entry loses the `LoadOrStore`
    /// race, Go sets `e.delete` on the loser without marking the winner's
    /// `delete` and without installing `proxyFor` (unlike `deleteLocked`).
    pub fn delete(&self) {
        let mut st = self.lock_state();
        if let Some(proxy) = st.proxy_for.clone() {
            drop(st);
            proxy.delete();
            return;
        }
        self.delete_locked_raw(&mut st);
    }

    /// The `Delete()` body — Go's public `Delete` (does NOT set `proxyFor`
    /// or mark the winner deleted when losing the race).
    fn delete_locked_raw(&self, st: &mut SyncEntryState<K, V>) {
        if st.entry.dirty {
            st.entry.delete = true;
            return;
        }
        let Some(map) = self.upgrade_map() else {
            st.entry.delete = true;
            return;
        };
        let (entry, loaded) = map
            .dirty
            .load_or_store(st.entry.key.clone(), self.clone());
        if loaded {
            let _est = entry.lock_state();
            st.entry.delete = true;
        } else {
            st.entry.delete = true;
        }
    }

    /// `e.deleteLocked()` — `e`'s mutex must already be held (`st`).
    /// Unlike [`delete_locked_raw`], losing the race installs `proxyFor`
    /// and marks the winner deleted.
    fn delete_locked(&self, st: &mut SyncEntryState<K, V>) {
        if st.entry.dirty {
            st.entry.delete = true;
            return;
        }
        let Some(map) = self.upgrade_map() else {
            st.entry.delete = true;
            return;
        };
        let (entry, loaded) = map
            .dirty
            .load_or_store(st.entry.key.clone(), self.clone());
        if loaded {
            let mut est = entry.lock_state();
            st.proxy_for = Some(entry.clone());
            st.entry.value = est.entry.value.clone();
            st.entry.delete = true;
            st.entry.dirty = est.entry.dirty;
            est.entry.delete = true;
        } else {
            st.entry.delete = true;
        }
    }

    /// `e.DeleteIf(cond)` — `cond` sees the raw stored value (Go
    /// `cond(e.value)`).
    pub fn delete_if(&self, cond: impl FnOnce(Option<V>) -> bool) {
        let mut st = self.lock_state();
        if let Some(proxy) = st.proxy_for.clone() {
            drop(st);
            proxy.delete_if(cond);
            return;
        }
        if cond(st.entry.value.clone()) {
            self.delete_locked(&mut st);
        }
    }

    /// `entry.proxyFor` — exposed for the ported `syncmap_test` race
    /// assertions (the field is unexported in Go).
    #[doc(hidden)]
    pub fn proxy_for(&self) -> Option<SyncMapEntry<K, V>> {
        self.lock_state().proxy_for.clone()
    }

    /// `Arc::ptr_eq` for the Go `entry == proxyFor` pointer comparisons.
    #[doc(hidden)]
    pub fn ptr_eq(&self, other: &SyncMapEntry<K, V>) -> bool {
        Arc::ptr_eq(&self.shared, &other.shared)
    }
}

/// `lockedEntry[K, V]` — the [`Value`] view `Locked` hands out; all methods
/// operate on the already-held lock state (`state`) instead of relocking.
pub struct LockedEntry<'a, K: Eq + Hash + Clone, V: Cloneable> {
    entry: SyncMapEntry<K, V>,
    state: &'a mut SyncEntryState<K, V>,
}

impl<K: Eq + Hash + Clone, V: Cloneable> Value<V> for LockedEntry<'_, K, V> {
    fn value(&self) -> Option<V> {
        // `valueLocked` — checks the delete flag.
        self.state.entry.value()
    }
    fn original(&self) -> Option<V> {
        self.state.entry.original.clone()
    }
    fn dirty(&self) -> bool {
        self.state.entry.dirty
    }
    fn change(&mut self, apply: &mut dyn FnMut(&mut V)) {
        self.entry.change_locked(self.state, apply);
    }
    fn change_if(
        &mut self,
        cond: &mut dyn FnMut(Option<V>) -> bool,
        apply: &mut dyn FnMut(&mut V),
    ) -> bool {
        // Go: `cond(e.e.valueLocked())` — delete-checked value.
        if cond(self.state.entry.value()) {
            self.entry.change_locked(self.state, apply);
            return true;
        }
        false
    }
    fn delete(&mut self) {
        self.entry.delete_locked(self.state);
    }
    fn locked(&mut self, f: &mut dyn FnMut(&mut dyn Value<V>)) {
        f(self);
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable> Value<V> for SyncMapEntry<K, V> {
    fn value(&self) -> Option<V> {
        SyncMapEntry::value(self)
    }
    fn original(&self) -> Option<V> {
        SyncMapEntry::original(self)
    }
    fn dirty(&self) -> bool {
        SyncMapEntry::dirty(self)
    }
    fn change(&mut self, apply: &mut dyn FnMut(&mut V)) {
        SyncMapEntry::change(self, apply);
    }
    fn change_if(
        &mut self,
        cond: &mut dyn FnMut(Option<V>) -> bool,
        apply: &mut dyn FnMut(&mut V),
    ) -> bool {
        SyncMapEntry::change_if(self, cond, apply)
    }
    fn delete(&mut self) {
        SyncMapEntry::delete(self);
    }
    fn locked(&mut self, f: &mut dyn FnMut(&mut dyn Value<V>)) {
        SyncMapEntry::locked(self, f);
    }
}

struct SyncMapShared<K: Eq + Hash + Clone, V: Cloneable> {
    /// Go `base` — immutable after construction; `None` is Go's nil map.
    base: Option<FxHashMap<K, V>>,
    /// `dirty` — `collections.SyncMap[K, *SyncMapEntry[K, V]]`.
    dirty: GoSyncMap<K, SyncMapEntry<K, V>>,
}

/// `SyncMap[K, V]` — a dirty-tracking overlay on a snapshot map, safe for
/// concurrent access.
#[derive(Clone)]
pub struct SyncMap<K: Eq + Hash + Clone, V: Cloneable> {
    shared: Arc<SyncMapShared<K, V>>,
}

impl<K: Eq + Hash + Clone, V: Cloneable> SyncMap<K, V> {
    /// `NewSyncMap(base)` — `None` is Go's nil map.
    pub fn new(base: Option<FxHashMap<K, V>>) -> SyncMap<K, V> {
        SyncMap {
            shared: Arc::new(SyncMapShared {
                base,
                dirty: GoSyncMap::default(),
            }),
        }
    }

    /// `m.Load(key)`.
    pub fn load(&self, key: &K) -> Option<SyncMapEntry<K, V>> {
        if let Some(entry) = self.shared.dirty.load(key) {
            if entry.lock_state().entry.delete {
                return None;
            }
            return Some(entry);
        }
        let val = self.shared.base.as_ref()?.get(key)?.clone();
        Some(SyncMapEntry::from_base(&self.shared, key.clone(), val))
    }

    /// `m.LoadOrStore(key, value)` — `(entry, loaded)`; `None` when the
    /// stored entry is deleted (Go returns `nil, false`).
    pub fn load_or_store(&self, key: K, value: V) -> Option<(SyncMapEntry<K, V>, bool)> {
        // Check for existence in the base map first so the sync map access is atomic.
        if let Some(base_value) = self.shared.base.as_ref().and_then(|b| b.get(&key)).cloned() {
            if let Some(dirty) = self.shared.dirty.load(&key) {
                if dirty.lock_state().entry.delete {
                    return None;
                }
                return Some((dirty, true));
            }
            return Some((
                SyncMapEntry::from_base(&self.shared, key, base_value),
                true,
            ));
        }
        let (entry, loaded) = self.shared.dirty.load_or_store(
            key.clone(),
            SyncMapEntry {
                shared: Arc::new(SyncEntryShared {
                    map: Arc::downgrade(&self.shared),
                    state: Mutex::new(SyncEntryState {
                        entry: EntryState {
                            key,
                            original: None,
                            value: Some(value),
                            dirty: true,
                            delete: false,
                        },
                        proxy_for: None,
                    }),
                }),
            },
        );
        if loaded && entry.lock_state().entry.delete {
            return None;
        }
        Some((entry, loaded))
    }

    /// `m.Delete(key)`.
    pub fn delete(&self, key: &K) {
        let (entry, loaded) = self.shared.dirty.load_or_store(
            key.clone(),
            SyncMapEntry {
                shared: Arc::new(SyncEntryShared {
                    map: Arc::downgrade(&self.shared),
                    state: Mutex::new(SyncEntryState {
                        entry: EntryState {
                            key: key.clone(),
                            original: self
                                .shared
                                .base
                                .as_ref()
                                .and_then(|b| b.get(key))
                                .cloned(),
                            value: None,
                            dirty: false,
                            delete: true,
                        },
                        proxy_for: None,
                    }),
                }),
            },
        );
        if loaded {
            entry.delete();
        }
    }

    /// `m.Range(fn)` — iterates dirty entries first, then base entries not
    /// shadowed by a dirty entry. Deleted dirty entries are skipped.
    ///
    /// PORT: iterates snapshots of `Arc` handles (`collections::SyncMap`'s
    /// `range` already snapshots; the base map is immutable) — `fn` may call
    /// back into the map. Iteration order is unspecified, as in Go.
    pub fn range(&self, mut f: impl FnMut(&SyncMapEntry<K, V>) -> bool) {
        let mut seen_in_dirty: FxHashSet<K> = FxHashSet::default();
        let mut stop = false;
        self.shared.dirty.range(|key, entry| {
            seen_in_dirty.insert(key);
            let deleted = entry.lock_state().entry.delete;
            if !deleted && !f(&entry) {
                stop = true;
                return false;
            }
            true
        });
        if stop {
            return;
        }
        if let Some(base) = &self.shared.base {
            for (key, value) in base {
                if seen_in_dirty.contains(key) {
                    continue; // already processed in dirty entries
                }
                if !f(&SyncMapEntry::from_base(
                    &self.shared,
                    key.clone(),
                    value.clone(),
                )) {
                    break;
                }
            }
        }
    }

    /// `m.Finalize()` — `(result, changed)`; the Go nil map result is `None`.
    pub fn finalize(&self) -> (Option<FxHashMap<K, V>>, bool) {
        self.finalize_with(FinalizationHooks::default())
    }

    /// `m.FinalizeWith(hooks)`.
    ///
    /// PORT: Go returns `m.base` itself when unchanged (shared); here the
    /// base is cloned — contents identical, aliasing not.
    pub fn finalize_with(&self, mut hooks: FinalizationHooks<K, V>) -> (Option<FxHashMap<K, V>>, bool) {
        let mut changed = false;
        let mut result = self.shared.base.clone();
        macro_rules! ensure_cloned {
            () => {
                if !changed {
                    if result.is_none() {
                        result = Some(FxHashMap::default());
                    }
                    changed = true;
                }
            };
        }

        self.shared.dirty.range(|key, entry| {
            let st = entry.lock_state();
            if st.entry.delete {
                ensure_cloned!();
                if let Some(on_delete) = hooks.on_delete.as_mut() {
                    on_delete(key.clone(), st.entry.value.clone());
                }
                result.as_mut().unwrap().remove(&key);
            } else if st.entry.dirty {
                ensure_cloned!();
                if hooks.on_change.is_some() || hooks.on_add.is_some() {
                    let in_base = self
                        .shared
                        .base
                        .as_ref()
                        .is_some_and(|b| b.contains_key(&key));
                    if in_base {
                        if let Some(on_change) = hooks.on_change.as_mut() {
                            on_change(
                                key.clone(),
                                st.entry.original.clone(),
                                st.entry.value.clone(),
                            );
                        }
                    } else if let Some(on_add) = hooks.on_add.as_mut() {
                        on_add(key.clone(), st.entry.value.clone());
                    }
                }
                if let Some(v) = st.entry.value.clone() {
                    result.as_mut().unwrap().insert(key, v);
                }
            }
            true
        });
        (result, changed)
    }
}

/// `OnDelete(key, value)` / `OnAdd(key, value)` hook signature.
pub type FinalizationHook<K, V> = Box<dyn FnMut(K, Option<V>)>;
/// `OnChange(key, oldValue, newValue)` hook signature.
pub type FinalizationChangeHook<K, V> = Box<dyn FnMut(K, Option<V>, Option<V>)>;

/// `FinalizationHooks[K, V]` — optional callbacks fired while finalizing.
///
/// PORT: Go's nil-able `func` fields become `Option<Box<dyn FnMut>>`. Values
/// are passed as `Option<V>` — `None` is Go's zero value (`entry.original`
/// is unset for `Add`-created entries, `entry.value` is unset for
/// `Delete`-created ones).
pub struct FinalizationHooks<K, V> {
    /// `OnDelete(key, value)`.
    pub on_delete: Option<FinalizationHook<K, V>>,
    /// `OnChange(key, oldValue, newValue)`.
    pub on_change: Option<FinalizationChangeHook<K, V>>,
    /// `OnAdd(key, value)`.
    pub on_add: Option<FinalizationHook<K, V>>,
}

impl<K, V> Default for FinalizationHooks<K, V> {
    fn default() -> Self {
        FinalizationHooks {
            on_delete: None,
            on_change: None,
            on_add: None,
        }
    }
}
