// Ported from tsc/internal/project/dirty/interfaces.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `Value[T]` — Go's `Value` interface: the read/write view handed to
/// `Locked` callbacks (and stored by consumers as `dirty.Value[T]`).
///
/// PORT: Go's nil-able `V` results (`Value()`/`Original()` return the zero
/// value — nil for pointer types — for deleted or unpopulated entries)
/// become `Option<V>`: `None` is the Go zero value. `func(T)` parameters
/// become `&mut dyn FnMut(&mut V)`; `cond func(T) bool` becomes
/// `&mut dyn FnMut(Option<V>) -> bool` since the entry's stored value may
/// itself be the Go zero value.
///
/// Implementors: [`crate::Box`], [`crate::MapEntry`],
/// [`crate::SyncMapEntry`], and `LockedEntry` (the lock-held view
/// `SyncMapEntry::locked` hands out).
pub trait Value<V> {
    /// `Value()` — `None` is the Go zero value (deleted/unpopulated entry).
    fn value(&self) -> Option<V>;
    /// `Original()` — the snapshot's base value; `None` when the entry never
    /// had one (Go zero value).
    fn original(&self) -> Option<V>;
    /// `Dirty()`.
    fn dirty(&self) -> bool;
    /// `Change(apply)` — clones-on-write on first change, then applies the
    /// mutation to the entry's live value.
    fn change(&mut self, apply: &mut dyn FnMut(&mut V));
    /// `ChangeIf(cond, apply)`.
    fn change_if(
        &mut self,
        cond: &mut dyn FnMut(Option<V>) -> bool,
        apply: &mut dyn FnMut(&mut V),
    ) -> bool;
    /// `Delete()`.
    fn delete(&mut self);
    /// `Locked(fn)` — runs `f` with a [`Value`] view while holding the
    /// entry's lock (a no-op wrapper for the unsynchronized implementations).
    fn locked(&mut self, f: &mut dyn FnMut(&mut dyn Value<V>));
}
