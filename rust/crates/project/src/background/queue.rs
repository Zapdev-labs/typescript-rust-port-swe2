// Ported from tsc/internal/project/background/queue.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Condvar, Mutex, RwLock};
use std::thread;

use tsc_core::context::Context;

/// The `sync.WaitGroup`-equivalent inflight counter (mirrors
/// `tsc_core`'s private `Inflight`).
#[derive(Default)]
struct Inflight {
    count: Mutex<usize>,
    idle: Condvar,
}

impl Inflight {
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

/// `type Queue struct` — manages background tasks execution.
///
/// PORT: Go's `Enqueue` runs `fn` on a goroutine; `Queue` methods take `&self`,
/// so the spawned tasks borrow shared `Arc` state instead.
#[derive(Default)]
pub struct Queue {
    wg: Arc<Inflight>,
    closed: RwLock<bool>,
}

/// `func NewQueue() *Queue`
pub fn new_queue() -> Queue {
    Queue::default()
}

impl Queue {
    /// `func (q *Queue) Enqueue(ctx context.Context, fn func(context.Context))`
    pub fn enqueue(&self, ctx: &Context, f: impl FnOnce(&Context) + Send + 'static) {
        {
            let closed = self.closed.read().unwrap();
            if *closed {
                return;
            }

            // Don't start new tasks if context is already cancelled
            if ctx.is_cancelled() {
                return;
            }

            self.wg.add();
        }

        let wg = self.wg.clone();
        let ctx = ctx.clone();
        thread::spawn(move || {
            // Check context again before executing
            if !ctx.is_cancelled() {
                f(&ctx);
            }
            wg.done();
        });
    }

    /// `func (q *Queue) Wait()`
    ///
    /// Waits for all active tasks to complete. It does not prevent new tasks
    /// from being enqueued while waiting.
    pub fn wait(&self) {
        self.wg.wait();
    }

    /// `func (q *Queue) Close()`
    pub fn close(&self) {
        {
            let mut closed = self.closed.write().unwrap();
            *closed = true;
        }
        self.wg.wait();
    }
}
