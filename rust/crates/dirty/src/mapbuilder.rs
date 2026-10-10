// Ported from tsc/internal/project/dirty/mapbuilder.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::hash::Hash;

use rustc_hash::{FxHashMap, FxHashSet};

/// `MapBuilder[K, VBase, VBuilder]` — accumulates `Set`/`Delete`/`Clear`
/// mutations against a base map and materializes the result with `build`.
///
/// PORT: Go's `base`/`dirty`/`deleted` maps (nil-able) become `Option`/empty
/// collections — `None` is Go's nil map. `func(VBase) VBuilder`/`func(VBuilder)
/// VBase` become generic `F`/`G` (pass function items like `core::identity`).
pub struct MapBuilder<K: Eq + Hash + Clone, VBase, VBuilder, F, G>
where
    F: Fn(VBase) -> VBuilder,
    G: Fn(VBuilder) -> VBase,
{
    base: Option<FxHashMap<K, VBase>>,
    dirty: FxHashMap<K, VBuilder>,
    deleted: FxHashSet<K>,

    /// Go stores this but never calls it — kept for API parity.
    #[allow(dead_code)]
    to_builder: F,
    build: G,
}

impl<K: Eq + Hash + Clone, VBase: Clone, VBuilder: Clone, F, G> MapBuilder<K, VBase, VBuilder, F, G>
where
    F: Fn(VBase) -> VBuilder,
    G: Fn(VBuilder) -> VBase,
{
    /// `NewMapBuilder(base, toBuilder, build)` — `None` is Go's nil base map.
    pub fn new(base: Option<FxHashMap<K, VBase>>, to_builder: F, build: G) -> Self {
        MapBuilder {
            base,
            dirty: FxHashMap::default(),
            deleted: FxHashSet::default(),
            to_builder,
            build,
        }
    }

    /// `mb.Set(key, value)`.
    pub fn set(&mut self, key: K, value: VBuilder) {
        self.dirty.insert(key.clone(), value);
        self.deleted.remove(&key);
    }

    /// `mb.Delete(key)`.
    pub fn delete(&mut self, key: &K) {
        self.deleted.insert(key.clone());
        self.dirty.remove(key);
    }

    /// `mb.Clear()` — marks every base key deleted and drops pending writes.
    pub fn clear(&mut self) {
        self.dirty = FxHashMap::default();
        self.deleted = FxHashSet::default();
        if let Some(base) = &self.base {
            self.deleted.extend(base.keys().cloned());
        }
    }

    /// `mb.Has(key)`.
    pub fn has(&self, key: &K) -> bool {
        if self.deleted.contains(key) {
            return false;
        }
        if self.dirty.contains_key(key) {
            return true;
        }
        self.base
            .as_ref()
            .is_some_and(|base| base.contains_key(key))
    }

    /// `mb.Build()` — returns the base map unchanged when nothing was
    /// touched; `None` is Go's nil map result.
    ///
    /// PORT: Go returns `mb.base` itself (shared); here it is cloned — the
    /// contents are identical, the aliasing is not.
    pub fn build(&self) -> Option<FxHashMap<K, VBase>> {
        if self.dirty.is_empty() && self.deleted.is_empty() {
            return self.base.clone();
        }
        let mut result = self.base.clone().unwrap_or_default();
        for key in &self.deleted {
            result.remove(key);
        }
        for (key, value) in &self.dirty {
            result.insert(key.clone(), (self.build)(value.clone()));
        }
        Some(result)
    }
}
