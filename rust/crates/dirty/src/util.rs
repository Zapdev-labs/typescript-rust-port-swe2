// Ported from tsc/internal/project/dirty/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::cloneable::Cloneable;

/// `CloneMapIfNil(dirty, original, getMap)` — returns the dirty map if it
/// exists, else a clone of the original map, else a fresh empty map.
///
/// PORT: Go's nil-able `*T` receivers become `Option<&T>`; nil-able `map[K]V`
/// results become `Option<M>` where `M` is the map representation the caller
/// stores (e.g. [`crate::CloneableMap`], or `FxHashMap` via [`Cloneable`]).
/// `make(map[K]V)` becomes `M::default()`. Go returns the dirty map itself
/// (shared) — with a handle type like `CloneableMap` that sharing is
/// preserved; for plain `FxHashMap` the returned map is the same value.
pub fn clone_map_if_nil<T, M>(
    dirty: Option<&T>,
    original: Option<&T>,
    get_map: impl Fn(Option<&T>) -> Option<M>,
) -> M
where
    M: Cloneable + Default,
{
    match get_map(dirty) {
        Some(m) => m,
        None => match original {
            None => M::default(),
            Some(o) => get_map(Some(o))
                .map(|m| Cloneable::clone_value(&m))
                .unwrap_or_default(),
        },
    }
}
