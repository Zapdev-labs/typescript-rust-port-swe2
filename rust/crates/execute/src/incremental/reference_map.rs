// Ported from tsc/internal/execute/incremental/referencemap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::OnceCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_collections::{Set, SyncMap};
use tsc_tspath::PathKey;

/// `type referenceMap struct` — forward references plus a lazily built
/// referenced-by index (`referenceBy sync.Once`).
///
/// PORT: the lazily built `referencedBy` index uses `OnceCell` (the Go
/// `sync.Once` is only for lazy initialization); values are `Rc<Set>` since
/// the stored reference sets are shared with `references`.
#[derive(Default)]
pub struct ReferenceMap {
    references: SyncMap<PathKey, Rc<Set<PathKey>>>,
    referenced_by: OnceCell<FxHashMap<PathKey, Set<PathKey>>>,
}

impl ReferenceMap {
    /// `(*referenceMap) storeReferences`.
    pub fn store_references(&self, path: PathKey, refs: Option<Rc<Set<PathKey>>>) {
        // PORT: Go stores nil-able `*Set`; a nil set is stored as an empty
        // set's absence here — callers only `storeReferences` when the
        // computed set is non-nil.
        if let Some(refs) = refs {
            self.references.store(path, refs);
        }
    }

    /// `(*referenceMap) getReferences`.
    pub fn get_references(&self, path: &PathKey) -> Option<Rc<Set<PathKey>>> {
        self.references.load(path)
    }

    /// `(*referenceMap) getPathsWithReferences`.
    pub fn get_paths_with_references(&self) -> Vec<PathKey> {
        self.references.keys()
    }

    /// `(*referenceMap) getReferencedBy`.
    pub fn get_referenced_by(&self, path: &PathKey) -> Vec<PathKey> {
        let referenced_by = self.referenced_by.get_or_init(|| {
            let mut referenced_by = FxHashMap::<PathKey, Set<PathKey>>::default();
            self.references.range(|key, value| {
                for ref_path in value.keys().iter() {
                    referenced_by
                        .entry(ref_path.clone())
                        .or_default()
                        .add(key.clone());
                }
                true
            });
            referenced_by
        });
        match referenced_by.get(path) {
            Some(refs) => refs.keys().iter().cloned().collect(),
            None => Vec::new(),
        }
    }
}
