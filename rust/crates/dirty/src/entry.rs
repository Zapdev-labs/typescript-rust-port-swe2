// Ported from tsc/internal/project/dirty/entry.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! The shared `mapEntry[K, V]` state embedded by both `MapEntry` and
//! `SyncMapEntry` in Go. Fields that Go leaves at their zero value (a nil
//! pointer for `original`, a nil `value` for delete-created entries) are
//! `Option`s here — `None` is the Go zero value.

/// `mapEntry[K, V]` — the common dirty-tracking state.
pub(crate) struct EntryState<K, V> {
    pub(crate) key: K,
    /// Go `original` — `None` when the entry was created by `Add`/`Delete`
    /// (Go leaves the field at its zero value, typically nil).
    pub(crate) original: Option<V>,
    /// Go `value` — `None` when the entry was created by `SyncMap::delete`
    /// for a key absent from the base map (Go leaves the field at its zero
    /// value, typically nil).
    pub(crate) value: Option<V>,
    pub(crate) dirty: bool,
    pub(crate) delete: bool,
}

impl<K, V: Clone> EntryState<K, V> {
    /// `e.Value()` — the current value, or the Go zero value (`None`) when the
    /// entry is deleted or the value was never populated.
    pub(crate) fn value(&self) -> Option<V> {
        if self.delete {
            return None;
        }
        self.value.clone()
    }
}
