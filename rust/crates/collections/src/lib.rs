// Ported from tsc/internal/collections @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod cow;
pub mod multimap;
pub mod ordered_map;
pub mod ordered_set;
pub mod set;
pub mod syncmap;
pub mod syncset;

// Flat re-exports so call sites mirror Go's `collections.X` as
// `collections::X`.
pub use cow::{CopyOnWriteMap, CopyOnWriteSet};
pub use multimap::{MultiMap, group_by};
pub use ordered_map::{MapEntry, OrderedMap, diff_ordered_maps, diff_ordered_maps_func};
pub use ordered_set::OrderedSet;
pub use set::{Set, new_set_from_items};
pub use syncmap::SyncMap;
pub use syncset::SyncSet;
