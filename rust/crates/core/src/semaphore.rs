// Ported from tsc/internal/core/semaphore.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's `release func()` return value becomes a RAII `SemaphoreGuard`
// (Drop == release; `release(self)` is the explicit form). Go's buffered
// channel becomes `Mutex<usize> + Condvar`. `TryAcquire(ctx)` returns
// `Option<SemaphoreGuard>` (None == !acquired); there is no channel+select
// equivalent, so cancellation is polled between short condvar waits — the
// observable difference is up to ~1ms of wakeup latency on cancellation.

use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use crate::context::Context;

/// The `release func()` returned by Go's `Semaphore.Acquire`. Dropping the
/// guard releases the slot.
pub struct SemaphoreGuard(Option<Arc<SemaphoreState>>);

impl SemaphoreGuard {
    /// The returned closure is no longer needed: just drop the guard, or call
    /// `release()` for the explicit Go-style spelling.
    pub fn release(self) {}
}

impl Drop for SemaphoreGuard {
    fn drop(&mut self) {
        if let Some(state) = self.0.take() {
            let mut used = state.used.lock().unwrap();
            debug_assert!(*used > 0, "semaphore release without acquire");
            *used -= 1;
            drop(used);
            state.available.notify_one();
        }
    }
}

struct SemaphoreState {
    capacity: usize,
    used: Mutex<usize>,
    available: Condvar,
}

pub trait Semaphore {
    /// `Acquire() (release func())`
    fn acquire(&self) -> SemaphoreGuard;
    /// `TryAcquire(ctx) (release func(), acquired bool)`
    fn try_acquire(&self, ctx: &Context) -> Option<SemaphoreGuard>;
}

#[derive(Clone, Copy, Default)]
pub struct UnlimitedSemaphore;

impl Semaphore for UnlimitedSemaphore {
    fn acquire(&self) -> SemaphoreGuard {
        SemaphoreGuard(None)
    }

    fn try_acquire(&self, _ctx: &Context) -> Option<SemaphoreGuard> {
        Some(SemaphoreGuard(None))
    }
}

#[derive(Clone)]
pub struct LimitedSemaphore {
    state: Arc<SemaphoreState>,
}

pub fn new_limited_semaphore(max_concurrency: i32) -> LimitedSemaphore {
    if max_concurrency <= 0 {
        panic!("maxConcurrency must be positive");
    }
    LimitedSemaphore {
        state: Arc::new(SemaphoreState {
            capacity: max_concurrency as usize,
            used: Mutex::new(0),
            available: Condvar::new(),
        }),
    }
}

impl Semaphore for LimitedSemaphore {
    fn acquire(&self) -> SemaphoreGuard {
        let mut used = self.state.used.lock().unwrap();
        while *used >= self.state.capacity {
            used = self.state.available.wait(used).unwrap();
        }
        *used += 1;
        SemaphoreGuard(Some(self.state.clone()))
    }

    fn try_acquire(&self, ctx: &Context) -> Option<SemaphoreGuard> {
        // PORT: `select { case ch <- ...: / <-ctx.Done(): }` — poll the
        // context between bounded waits on the availability condvar.
        let mut used = self.state.used.lock().unwrap();
        loop {
            if *used < self.state.capacity {
                *used += 1;
                return Some(SemaphoreGuard(Some(self.state.clone())));
            }
            if ctx.is_cancelled() {
                return None;
            }
            let (guard, _timeout) = self
                .state
                .available
                .wait_timeout(used, Duration::from_millis(1))
                .unwrap();
            used = guard;
        }
    }
}
