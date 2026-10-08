// Ported from tsc/internal/core/workgroup.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go closures capture freely; Rust `thread::spawn` requires
// `'static` work items, so `queue`/`go` take `Send + 'static` closures —
// callers move `Arc`s/owned data in. `sync.WaitGroup` becomes an
// `Inflight` (Mutex<usize> + Condvar). `errgroup.Group` (which cancels a
// derived context and returns the first error) becomes an
// `Arc<Mutex<Option<E>>>` first-error store — Go's derived context is
// discarded (`g, _ := errgroup.WithContext(ctx)`), so `ctx` is accepted for
// signature parity but does not stop running tasks, matching Go.

use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use crate::context::Context;
use crate::semaphore::{LimitedSemaphore, Semaphore};

pub trait WorkGroup {
    /// Queue queues a function to run. It may be invoked immediately, or deferred until RunAndWait.
    /// It is not safe to call Queue after RunAndWait has returned.
    fn queue(&self, f: Box<dyn FnOnce() + Send + 'static>);

    /// RunAndWait runs all queued functions, blocking until they have all completed.
    fn run_and_wait(&self);
}

// PORT: Go returns the interface `WorkGroup`; `Box<dyn WorkGroup>` is the
// Rust equivalent.
pub fn new_work_group(single_threaded: bool) -> Box<dyn WorkGroup> {
    if single_threaded {
        return Box::new(SingleThreadedWorkGroup::new());
    }
    Box::new(ParallelWorkGroup::new())
}

/// The `sync.WaitGroup`-equivalent inflight counter.
struct Inflight {
    count: Mutex<usize>,
    idle: Condvar,
}

impl Inflight {
    fn new() -> Self {
        Inflight {
            count: Mutex::new(0),
            idle: Condvar::new(),
        }
    }

    fn add(&self) {
        *self.count.lock().unwrap() += 1;
    }

    fn done(&self) {
        let mut count = self.count.lock().unwrap();
        *count -= 1;
        if *count == 0 {
            self.idle.notify_all();
        }
    }

    fn wait(&self) {
        let mut count = self.count.lock().unwrap();
        while *count != 0 {
            count = self.idle.wait(count).unwrap();
        }
    }
}

struct ParallelWorkGroup {
    done: AtomicBool,
    inflight: Arc<Inflight>,
}

impl ParallelWorkGroup {
    fn new() -> Self {
        ParallelWorkGroup {
            done: AtomicBool::new(false),
            inflight: Arc::new(Inflight::new()),
        }
    }
}

impl WorkGroup for ParallelWorkGroup {
    fn queue(&self, f: Box<dyn FnOnce() + Send + 'static>) {
        if self.done.load(Ordering::SeqCst) {
            panic!("Queue called after RunAndWait returned");
        }

        self.inflight.add();
        let inflight = self.inflight.clone();
        thread::spawn(move || {
            // PORT: a panic in a queued fn propagates as a thread panic, like
            // a Go goroutine panic (the inflight counter still decrements so
            // run_and_wait does not hang).
            let result = catch_unwind(AssertUnwindSafe(f));
            inflight.done();
            if let Err(payload) = result {
                resume_unwind(payload);
            }
        });
    }

    fn run_and_wait(&self) {
        self.inflight.wait();
        self.done.store(true, Ordering::SeqCst);
    }
}

struct SingleThreadedWorkGroup {
    done: AtomicBool,
    fns: Mutex<Vec<Box<dyn FnOnce() + Send + 'static>>>,
}

impl SingleThreadedWorkGroup {
    fn new() -> Self {
        SingleThreadedWorkGroup {
            done: AtomicBool::new(false),
            fns: Mutex::new(Vec::new()),
        }
    }
}

impl WorkGroup for SingleThreadedWorkGroup {
    fn queue(&self, f: Box<dyn FnOnce() + Send + 'static>) {
        if self.done.load(Ordering::SeqCst) {
            panic!("Queue called after RunAndWait returned");
        }

        self.fns.lock().unwrap().push(f);
    }

    fn run_and_wait(&self) {
        // PORT: Go pops from the back (LIFO); Vec::pop does the same.
        while let Some(f) = self.fns.lock().unwrap().pop() {
            f();
        }
        self.done.store(true, Ordering::SeqCst);
    }
}

// ThrottleGroup is like errgroup.Group but with global concurrency limiting via a semaphore.
//
// PORT: `ThrottleGroup` is Clone (the shared state is Arc'd) — Go's
// `*ThrottleGroup` pointer is shared the same way. Manual impl so the
// Clone bound does not leak onto E.
pub struct ThrottleGroup<E> {
    semaphore: LimitedSemaphore,
    errors: Arc<Mutex<Option<E>>>,
    inflight: Arc<Inflight>,
}

impl<E> Clone for ThrottleGroup<E> {
    fn clone(&self) -> Self {
        ThrottleGroup {
            semaphore: self.semaphore.clone(),
            errors: self.errors.clone(),
            inflight: self.inflight.clone(),
        }
    }
}

// NewThrottleGroup creates a new ThrottleGroup with the given context and semaphore for concurrency limiting.
//
// PORT: `_ctx` is accepted for parity; Go's `errgroup.WithContext(ctx)`
// derives a child context that is discarded (`_`), so cancelling ctx has no
// effect on the group in Go either. Errors are reported through
// `Result<(), E>` where Go returns `error`.
impl<E: Send + 'static> ThrottleGroup<E> {
    pub fn new(_ctx: &Context, semaphore: LimitedSemaphore) -> Self {
        ThrottleGroup {
            semaphore,
            errors: Arc::new(Mutex::new(None)),
            inflight: Arc::new(Inflight::new()),
        }
    }

    // Go runs the given function in a new goroutine, but first acquires a slot from the semaphore.
    // The semaphore slot is released when the function completes.
    //
    // PORT: `fn func() error` becomes `FnOnce() -> Result<(), E>`.
    pub fn go(&self, f: impl FnOnce() -> Result<(), E> + Send + 'static) {
        self.inflight.add();
        let semaphore = self.semaphore.clone();
        let errors = self.errors.clone();
        let inflight = self.inflight.clone();
        thread::spawn(move || {
            let result = catch_unwind(AssertUnwindSafe(|| {
                // Acquire semaphore slot - this will block until a slot is available
                // Release semaphore slot when done
                let _guard = semaphore.acquire();
                f()
            }));
            inflight.done();
            match result {
                Ok(Ok(())) => {}
                Ok(Err(e)) => {
                    // errgroup records the first error.
                    let mut errors = errors.lock().unwrap();
                    if errors.is_none() {
                        *errors = Some(e);
                    }
                }
                Err(payload) => resume_unwind(payload),
            }
        });
    }

    // Wait waits for all goroutines to complete and returns the first error encountered, if any.
    pub fn wait(&self) -> Result<(), E> {
        self.inflight.wait();
        self.errors.lock().unwrap().take().map_or(Ok(()), Err)
    }
}

// PORT: free-function form matching Go's `NewThrottleGroup` constructor.
pub fn new_throttle_group<E: Send + 'static>(
    ctx: &Context,
    semaphore: LimitedSemaphore,
) -> ThrottleGroup<E> {
    ThrottleGroup::new(ctx, semaphore)
}
