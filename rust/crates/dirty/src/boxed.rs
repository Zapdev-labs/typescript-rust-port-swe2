// Ported from tsc/internal/project/dirty/box.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;

use crate::cloneable::Cloneable;
use crate::value::Value;

/// `Box[T]` — dirty tracking for a single cloneable value.
///
/// PORT: Go's `*Box` methods mutate through the pointer; here the mutable
/// fields live in a `RefCell` so methods stay `&self` like their Go
/// counterparts. Go's zero-value `T` returns (`Value()` on a deleted box)
/// become `Option<T>`; store `Option<…>` as `T` itself to model a nil-able
/// payload (e.g. Go's `dirty.Box[*Project]` is `Box<Option<Shared<Project>>>`
/// here).
pub struct Box<T: Cloneable> {
    original: T,
    inner: RefCell<BoxInner<T>>,
}

struct BoxInner<T> {
    value: T,
    dirty: bool,
    delete: bool,
}

impl<T: Cloneable> Box<T> {
    /// `NewBox(original)`.
    pub fn new(original: T) -> Box<T> {
        Box {
            original: original.clone(),
            inner: RefCell::new(BoxInner {
                value: original,
                dirty: false,
                delete: false,
            }),
        }
    }

    /// `b.Value()` — `None` is the Go zero value (a deleted box).
    ///
    /// The returned clone has Go assignment semantics (`Clone::clone`): for
    /// handle types it shares the pointee exactly like Go returning `b.value`.
    pub fn value(&self) -> Option<T> {
        let inner = self.inner.borrow();
        if inner.delete {
            return None;
        }
        Some(inner.value.clone())
    }

    /// `b.Original()` — a Go-assignment copy of the snapshot's base value.
    pub fn original(&self) -> Option<T> {
        Some(self.original.clone())
    }

    /// `b.Dirty()`.
    pub fn dirty(&self) -> bool {
        self.inner.borrow().dirty
    }

    /// `b.Set(value)`.
    pub fn set(&self, value: T) {
        let mut inner = self.inner.borrow_mut();
        inner.value = value;
        inner.delete = false;
        inner.dirty = true;
    }

    /// `b.Change(apply)` — clones-on-write (`Clone()`) on first change, then
    /// runs `apply` against the live value.
    pub fn change(&self, apply: impl FnOnce(&mut T)) {
        let mut inner = self.inner.borrow_mut();
        if !inner.dirty {
            inner.value = Cloneable::clone_value(&inner.value);
            inner.dirty = true;
        }
        apply(&mut inner.value);
    }

    /// `b.ChangeIf(cond, apply)`.
    ///
    /// PORT: Go's `cond(b.value)` sees the raw value (not `Value()`), so `cond`
    /// always receives `Some` — it runs even when the box is deleted, matching
    /// Go.
    pub fn change_if(
        &self,
        cond: impl FnOnce(Option<T>) -> bool,
        apply: impl FnOnce(&mut T),
    ) -> bool {
        let raw = self.inner.borrow().value.clone();
        if cond(Some(raw)) {
            self.change(apply);
            return true;
        }
        false
    }

    /// `b.Delete()`.
    pub fn delete(&self) {
        self.inner.borrow_mut().delete = true;
    }

    /// `b.Locked(fn)` — the unsynchronized implementation simply calls `fn`
    /// with the box as its own [`Value`] view.
    pub fn locked(&self, mut f: impl FnMut(&mut dyn Value<T>)) {
        let mut h = BoxRef { b: self };
        f(&mut h);
    }

    /// `b.Finalize()` — `(Value(), dirty || delete)`; `None` is the Go zero
    /// value.
    pub fn finalize(&self) -> (Option<T>, bool) {
        let inner = self.inner.borrow();
        (
            if inner.delete {
                None
            } else {
                Some(inner.value.clone())
            },
            inner.dirty || inner.delete,
        )
    }
}

/// `Box` does not implement [`Value`] directly because its methods take
/// `&self` (Go's pointer receiver) while the trait takes `&mut self`; the
/// borrow adapter below bridges the two for [`Box::locked`].
struct BoxRef<'a, T: Cloneable> {
    b: &'a Box<T>,
}

impl<T: Cloneable> Value<T> for BoxRef<'_, T> {
    fn value(&self) -> Option<T> {
        self.b.value()
    }
    fn original(&self) -> Option<T> {
        self.b.original()
    }
    fn dirty(&self) -> bool {
        self.b.dirty()
    }
    fn change(&mut self, apply: &mut dyn FnMut(&mut T)) {
        self.b.change(apply);
    }
    fn change_if(
        &mut self,
        cond: &mut dyn FnMut(Option<T>) -> bool,
        apply: &mut dyn FnMut(&mut T),
    ) -> bool {
        self.b.change_if(cond, apply)
    }
    fn delete(&mut self) {
        self.b.delete();
    }
    fn locked(&mut self, f: &mut dyn FnMut(&mut dyn Value<T>)) {
        f(self);
    }
}
