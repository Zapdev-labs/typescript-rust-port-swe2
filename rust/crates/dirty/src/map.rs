// Ported from tsc/internal/project/dirty/map.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::hash::Hash;
use std::rc::{Rc, Weak};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::cloneable::Cloneable;
use crate::entry::EntryState;
use crate::value::Value;

/// `Map[K, V]` — a dirty-tracking overlay on a snapshot map, for
/// single-threaded (snapshot-building) use.
///
/// PORT: Go's `*Map`/`*MapEntry` graph (`MapEntry` holds a `*Map` back-pointer
/// and self-registers in `m.dirty`) becomes `Rc`/`RefCell` handles:
/// [`MapEntry`] is a cloneable handle (Go's `*MapEntry`) whose methods are
/// `&self`. `apply` callbacks run while the entry's `RefCell` is mutably
/// borrowed, so an `apply` that calls back into the same entry panics — Go's
/// non-reentrant calls would recurse instead (no consumer does this).
#[derive(Clone)]
pub struct Map<K: Eq + Hash + Clone, V: Cloneable> {
    shared: Rc<MapShared<K, V>>,
}

struct MapShared<K, V> {
    /// Go `base` — `None` is Go's nil map.
    base: RefCell<Option<FxHashMap<K, V>>>,
    dirty: RefCell<FxHashMap<K, Rc<MapEntryShared<K, V>>>>,
}

struct MapEntryShared<K, V> {
    /// `Weak` rather than `Rc` so a `Map` is released once its last outside
    /// handle and its dirty entries are gone; entries always reach the map
    /// through [`Map`]/`MapShared`, so upgrade only fails after the map is
    /// dropped — Go would keep it alive via the back-pointer (documented
    /// deviation; the parent always outlives entries in practice).
    map: Weak<MapShared<K, V>>,
    state: RefCell<EntryState<K, V>>,
}

/// `*MapEntry[K, V]` — a handle to one tracked entry.
pub struct MapEntry<K: Eq + Hash + Clone, V: Cloneable> {
    shared: Rc<MapEntryShared<K, V>>,
}

impl<K: Eq + Hash + Clone, V: Cloneable> Clone for MapEntry<K, V> {
    /// Go `*MapEntry` copy — shares the entry.
    fn clone(&self) -> Self {
        MapEntry {
            shared: Rc::clone(&self.shared),
        }
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable> MapEntry<K, V> {
    fn register(&self) {
        let map = self
            .shared
            .map
            .upgrade()
            .expect("tried to register an entry in a dropped Map");
        map.dirty.borrow_mut().insert(
            self.shared.state.borrow().key.clone(),
            Rc::clone(&self.shared),
        );
    }

    /// `e.Key()`.
    pub fn key(&self) -> K {
        self.shared.state.borrow().key.clone()
    }

    /// `e.Original()` — `None` is the Go zero value (e.g. `Add`-created
    /// entries leave `original` unset).
    pub fn original(&self) -> Option<V> {
        self.shared.state.borrow().original.clone()
    }

    /// `e.Value()` — `None` is the Go zero value (a deleted entry).
    ///
    /// The returned clone has Go assignment semantics (`Clone::clone`).
    /// Unlike Go, mutating through the returned value of a plain (non-handle)
    /// `V` does not write back into the entry — use `change`.
    pub fn value(&self) -> Option<V> {
        self.shared.state.borrow().value()
    }

    /// `e.Dirty()`.
    pub fn dirty(&self) -> bool {
        self.shared.state.borrow().dirty
    }

    /// `e.Change(apply)`.
    pub fn change(&self, apply: impl FnOnce(&mut V)) {
        {
            let mut st = self.shared.state.borrow_mut();
            if st.delete {
                panic!("tried to change a deleted entry");
            }
            if !st.dirty {
                st.value = st.value.as_ref().map(Cloneable::clone_value);
                st.dirty = true;
                drop(st);
                self.register();
            }
        }
        let mut st = self.shared.state.borrow_mut();
        apply(
            st.value
                .as_mut()
                .expect("tried to change an entry with no value (Go would pass the zero value)"),
        );
    }

    /// `e.Replace(newValue)`.
    pub fn replace(&self, new_value: V) {
        {
            let mut st = self.shared.state.borrow_mut();
            if st.delete {
                panic!("tried to change a deleted entry");
            }
            if !st.dirty {
                st.dirty = true;
                drop(st);
                self.register();
            }
        }
        self.shared.state.borrow_mut().value = Some(new_value);
    }

    /// `e.ChangeIf(cond, apply)` — `cond` sees `Value()`, so a deleted entry
    /// presents `None` (the Go zero value).
    pub fn change_if(
        &self,
        cond: impl FnOnce(Option<V>) -> bool,
        apply: impl FnOnce(&mut V),
    ) -> bool {
        if cond(self.value()) {
            self.change(apply);
            return true;
        }
        false
    }

    /// `e.Delete()`.
    pub fn delete(&self) {
        if !self.shared.state.borrow().dirty {
            self.register();
        }
        self.shared.state.borrow_mut().delete = true;
    }

    /// `e.Locked(fn)` — the unsynchronized implementation calls `fn` with the
    /// entry as its own [`Value`] view.
    pub fn locked(&self, mut f: impl FnMut(&mut dyn Value<V>)) {
        let mut h = EntryRef { e: self };
        f(&mut h);
    }
}

/// Borrow adapter so `&MapEntry` (Go's `*MapEntry`, `&self` methods) satisfies
/// the `&mut self` [`Value`] view inside `locked`.
struct EntryRef<'a, K: Eq + Hash + Clone, V: Cloneable> {
    e: &'a MapEntry<K, V>,
}

impl<K: Eq + Hash + Clone, V: Cloneable> Value<V> for EntryRef<'_, K, V> {
    fn value(&self) -> Option<V> {
        self.e.value()
    }
    fn original(&self) -> Option<V> {
        self.e.original()
    }
    fn dirty(&self) -> bool {
        self.e.dirty()
    }
    fn change(&mut self, apply: &mut dyn FnMut(&mut V)) {
        self.e.change(apply);
    }
    fn change_if(
        &mut self,
        cond: &mut dyn FnMut(Option<V>) -> bool,
        apply: &mut dyn FnMut(&mut V),
    ) -> bool {
        self.e.change_if(cond, apply)
    }
    fn delete(&mut self) {
        MapEntry::delete(self.e);
    }
    fn locked(&mut self, f: &mut dyn FnMut(&mut dyn Value<V>)) {
        f(self);
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable> Map<K, V> {
    /// `NewMap(base)` — `None` is Go's nil map.
    pub fn new(base: Option<FxHashMap<K, V>>) -> Map<K, V> {
        Map {
            shared: Rc::new(MapShared {
                base: RefCell::new(base),
                dirty: RefCell::new(FxHashMap::default()),
            }),
        }
    }

    /// `m.Get(key)`.
    pub fn get(&self, key: &K) -> Option<MapEntry<K, V>> {
        if let Some(entry) = self.shared.dirty.borrow().get(key) {
            if entry.state.borrow().delete {
                return None;
            }
            return Some(MapEntry {
                shared: Rc::clone(entry),
            });
        }
        let base = self.shared.base.borrow();
        let value = base.as_ref()?.get(key)?.clone();
        Some(MapEntry {
            shared: Rc::new(MapEntryShared {
                map: Rc::downgrade(&self.shared),
                state: RefCell::new(EntryState {
                    key: key.clone(),
                    original: Some(value.clone()),
                    value: Some(value),
                    dirty: false,
                    delete: false,
                }),
            }),
        })
    }

    /// `m.Add(key, value)` — registers a fresh dirty entry without checking
    /// the base map.
    pub fn add(&self, key: K, value: V) {
        self.shared.dirty.borrow_mut().insert(
            key.clone(),
            Rc::new(MapEntryShared {
                map: Rc::downgrade(&self.shared),
                state: RefCell::new(EntryState {
                    key,
                    original: None,
                    value: Some(value),
                    dirty: true,
                    delete: false,
                }),
            }),
        );
    }

    /// `m.Change(key, apply)` — panics on a missing entry, like Go.
    pub fn change(&self, key: &K, apply: impl FnOnce(&mut V)) {
        match self.get(key) {
            Some(entry) => entry.change(apply),
            None => panic!("tried to change a non-existent entry"),
        }
    }

    /// `m.TryDelete(key)`.
    pub fn try_delete(&self, key: &K) -> bool {
        match self.get(key) {
            Some(entry) => {
                entry.delete();
                true
            }
            None => false,
        }
    }

    /// `m.Delete(key)` — panics on a missing entry, like Go.
    pub fn delete(&self, key: &K) {
        if !self.try_delete(key) {
            panic!("tried to delete a non-existent entry");
        }
    }

    /// `m.Range(fn)` — iterates dirty entries first, then base entries not
    /// shadowed by a dirty entry. Deleted dirty entries are skipped.
    ///
    /// PORT: iterates a snapshot of `Rc` handles (Go iterates the map
    /// directly); `fn` may call back into the map without tripping the
    /// `RefCell`. Iteration order is unspecified, as in Go.
    pub fn range(&self, mut f: impl FnMut(&MapEntry<K, V>) -> bool) {
        let mut seen_in_dirty: FxHashSet<K> = FxHashSet::default();
        let dirty_entries: Vec<Rc<MapEntryShared<K, V>>> =
            self.shared.dirty.borrow().values().cloned().collect();
        for entry in dirty_entries {
            seen_in_dirty.insert(entry.state.borrow().key.clone());
            let deleted = entry.state.borrow().delete;
            if !deleted {
                let handle = MapEntry {
                    shared: Rc::clone(&entry),
                };
                if !f(&handle) {
                    return;
                }
            }
        }
        let base_entries: Vec<(K, V)> = self
            .shared
            .base
            .borrow()
            .as_ref()
            .map(|b| b.iter().map(|(k, v)| (k.clone(), v.clone())).collect())
            .unwrap_or_default();
        for (key, value) in base_entries {
            if seen_in_dirty.contains(&key) {
                continue; // already processed in dirty entries
            }
            let handle = MapEntry {
                shared: Rc::new(MapEntryShared {
                    map: Rc::downgrade(&self.shared),
                    state: RefCell::new(EntryState {
                        key,
                        original: Some(value.clone()),
                        value: Some(value),
                        dirty: false,
                        delete: false,
                    }),
                }),
            };
            if !f(&handle) {
                break;
            }
        }
    }

    /// `m.Clear()`.
    pub fn clear(&self) {
        *self.shared.dirty.borrow_mut() = FxHashMap::default();
        *self.shared.base.borrow_mut() = Some(FxHashMap::default());
    }

    /// `m.Finalize()` — `(result, changed)`; the Go nil map result is `None`.
    ///
    /// PORT: Go returns `m.base` itself when unchanged (the caller shares it);
    /// here the map is cloned — the contents are identical, the aliasing is
    /// not.
    pub fn finalize(&self) -> (Option<FxHashMap<K, V>>, bool) {
        let dirty = self.shared.dirty.borrow();
        if dirty.is_empty() {
            return (self.shared.base.borrow().clone(), false);
        }
        let mut result = self.shared.base.borrow().clone().unwrap_or_default();
        for (key, entry) in dirty.iter() {
            let st = entry.state.borrow();
            if st.delete {
                result.remove(key);
            } else {
                // Non-deleted dirty entries always carry a value (created by
                // `Add`/`get`/`replace`), but Go tolerates the zero value.
                result.insert(
                    key.clone(),
                    st.value
                        .clone()
                        .expect("dirty entry with no value (Go would store the zero value)"),
                );
            }
        }
        (Some(result), true)
    }
}
