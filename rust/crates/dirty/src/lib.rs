// tsc-dirty — port of tsc/internal/project/dirty @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Ordered-map-style dirty tracking used by the project/snapshot builder:
// copy-on-write overlays (`Map`, `SyncMap`, `Box`, `MapBuilder`) that record
// changed/deleted entries against a base map and materialize the result in
// `Finalize`.
//
// PORT notes:
// - Go's `Cloneable[T]` interface (`Clone() T`) becomes [`Cloneable`];
//   `Clone::clone` plays Go's assignment semantics (shallow for handle
//   types), `clone_value` is Go's `Clone()` (fresh independent copy).
// - Go's zero-value returns (nil pointers/maps) become `Option` — `None` is
//   the Go zero value everywhere (`Value()`, `Original()`, nil base maps).
// - `*MapEntry`/`*SyncMapEntry` aliasing becomes `Rc<RefCell>`/`Arc<Mutex>`
//   handles; `sync.Mutex` becomes `std::sync::Mutex`; `collections.SyncMap`
//   becomes `tsc_collections::SyncMap`. See each type's docs.

mod boxed;
mod cloneable;
mod entry;
mod map;
mod mapbuilder;
mod syncmap;
mod util;
mod value;

#[cfg(test)]
mod syncmap_test;

pub use boxed::Box;
pub use cloneable::{Cloneable, CloneableMap};
pub use map::{Map, MapEntry};
pub use mapbuilder::MapBuilder;
pub use syncmap::{
    FinalizationChangeHook, FinalizationHook, FinalizationHooks, LockedEntry, SyncMap,
    SyncMapEntry,
};
pub use util::clone_map_if_nil;
pub use value::Value;
