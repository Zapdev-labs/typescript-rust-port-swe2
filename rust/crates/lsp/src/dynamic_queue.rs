// Ported from tsc/internal/lsp/dynamic_queue.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's pair of buffered channels (`idle`/`ready chan
// *dynamicQueueState`, each capacity 1 — exactly one holds the queue state
// at a time, so possession of the state is the mutual-exclusion token)
// becomes `Mutex<Option<DynamicQueueState>>`: `None` while a caller has the
// state checked out, `Some` while it is parked, with
// `state.items.is_empty()` recording which channel Go sent it back on
// (empty == `idle`, non-empty == `ready`). The `select` over channel
// receives and `<-ctx.Done()` becomes a `Condvar::wait_timeout` loop
// polling `ctx.is_cancelled()` — the same ~1ms cancellation wakeup latency
// as `core::Semaphore::try_acquire`. `ctx.Err()` maps to
// `tsc_ipc::Error::ContextCanceled` (the ported `Context` has no deadline
// support, so `DeadlineExceeded` cannot occur).

use std::collections::VecDeque;
use std::sync::{Condvar, Mutex};
use std::time::Duration;

use tsc_core::context::Context;
use tsc_ipc::Error;

/// Cancellation poll interval while a waiter is blocked on the queue state
/// (Go wakes instantly on `<-ctx.Done()`; see `core::Semaphore::try_acquire`).
const CANCEL_POLL: Duration = Duration::from_millis(1);

/// `dynamicQueueState[T]` — the single token holding the queue's items.
struct DynamicQueueState<T> {
    /// `items []T` — FIFO; `pop_front` is Go's `state.items[0]`/`[1:]`.
    items: VecDeque<T>,
}

/// `dynamicQueue[T]` — a rate-limited work queue (the server's
/// `requestQueue`/`outgoingQueue`).
///
/// Inspired by Brian C. Mills' "Rethinking Classical Concurrency Patterns" talk:
/// https://www.youtube.com/watch?v=5zXAHh5tJqQ
///
/// This queue is a state machine, where each state is a channel, "idle" or
/// "ready". Only one caller ever has the actual state struct at a time. The
/// get function will wait until the "ready" channel holds the state. Putting
/// an item means grabbing the state from any channel, modifying it, and
/// putting it back on the "ready" channel. Since this is all managed via
/// contexts, any method can be cancelled while waiting for the state.
pub(crate) struct DynamicQueue<T> {
    /// `idle`/`ready` — `None` while the state is checked out by a caller.
    state: Mutex<Option<DynamicQueueState<T>>>,
    /// Broadcast on every channel-send (`q.idle <- state` / `q.ready <- state`).
    state_available: Condvar,
}

/// `newDynamicQueue`.
pub(crate) fn new_dynamic_queue<T>() -> DynamicQueue<T> {
    // `q.idle <- &dynamicQueueState[T]{}`.
    DynamicQueue {
        state: Mutex::new(Some(DynamicQueueState {
            items: VecDeque::new(),
        })),
        state_available: Condvar::new(),
    }
}

impl<T> DynamicQueue<T> {
    /// `Put`.
    pub(crate) fn put(&self, ctx: &Context, item: T) -> Result<(), Error> {
        // `if err := ctx.Err(); err != nil { return err }`.
        if ctx.is_cancelled() {
            return Err(Error::ContextCanceled);
        }

        let mut state = self.get_any(ctx)?;

        state.items.push_back(item);
        // `q.ready <- state` — the send cannot block: only one state token
        // exists and this call holds it.
        *self.state.lock().unwrap() = Some(state);
        self.state_available.notify_all();
        Ok(())
    }

    /// `Get`.
    pub(crate) fn get(&self, ctx: &Context) -> Result<T, Error> {
        if ctx.is_cancelled() {
            return Err(Error::ContextCanceled);
        }

        let mut state = self.get_ready(ctx)?;

        // `item := state.items[0]; state.items = state.items[1:]`.
        let item = state.items.pop_front().expect("ready state is non-empty");

        // `q.idle <- state` when empty, `q.ready <- state` otherwise — the
        // emptiness of `items` stands in for which channel Go sent it on.
        *self.state.lock().unwrap() = Some(state);
        self.state_available.notify_all();
        Ok(item)
    }

    /// `getAny` — `select { <-q.idle / <-q.ready / <-ctx.Done() }`.
    fn get_any(&self, ctx: &Context) -> Result<DynamicQueueState<T>, Error> {
        let mut guard = self.state.lock().unwrap();
        loop {
            if let Some(state) = guard.take() {
                return Ok(state);
            }
            if ctx.is_cancelled() {
                return Err(Error::ContextCanceled);
            }
            let (g, _) = self
                .state_available
                .wait_timeout(guard, CANCEL_POLL)
                .unwrap();
            guard = g;
        }
    }

    /// `getReady` — `select { <-q.ready / <-ctx.Done() }`.
    fn get_ready(&self, ctx: &Context) -> Result<DynamicQueueState<T>, Error> {
        let mut guard = self.state.lock().unwrap();
        loop {
            if guard.as_ref().is_some_and(|state| !state.items.is_empty()) {
                return Ok(guard.take().unwrap());
            }
            if ctx.is_cancelled() {
                return Err(Error::ContextCanceled);
            }
            let (g, _) = self
                .state_available
                .wait_timeout(guard, CANCEL_POLL)
                .unwrap();
            guard = g;
        }
    }
}
