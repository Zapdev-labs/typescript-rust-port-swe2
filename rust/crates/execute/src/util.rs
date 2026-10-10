// Shared helpers for the execute port.

/// `Defer` — runs a closure on drop, the mechanical port of Go's `defer`.
/// Used heavily for `defer tr.Push(...)()`, `defer profileSession.Stop()`,
/// `defer entry.mu.Unlock()`, and testing hooks.
pub struct Defer<F: FnOnce()> {
    f: Option<F>,
}

impl<F: FnOnce()> Defer<F> {
    pub fn new(f: F) -> Defer<F> {
        Defer { f: Some(f) }
    }
}

impl<F: FnOnce()> Drop for Defer<F> {
    fn drop(&mut self) {
        if let Some(f) = self.f.take() {
            f();
        }
    }
}

/// `defer!(expr)` — convenience macro mirroring `defer expr` in Go: the
/// expression runs when the binding goes out of scope.
#[macro_export]
macro_rules! defer {
    ($e:expr) => {
        let _defer = $crate::util::Defer::new(move || {
            $e;
        });
    };
}
