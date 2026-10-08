// Ported from tsc/internal/fswatch/debounce.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! `debounce` batches filesystem events for one backend. Each watcher owns one
//! debounce instance, created lazily on first subscribe and living for the
//! process lifetime. The background thread costs nothing when idle.
//!
//! Per-backend (rather than process-wide) isolation means a slow user
//! callback on one backend cannot starve event delivery on the others.
//!
//! PORT: Go's channel latch (`waitCh` closed on first trigger, `triggerCh`
//! replaced per trigger) becomes a `Mutex`+`Condvar` pair: `notified` plays
//! the role of the closed `waitCh`, and `trigger_epoch` plays the role of the
//! replaced `triggerCh` (a wait observes an epoch bump exactly when Go would
//! observe the captured channel close). Semantics are unchanged: the first
//! trigger after idle fires callbacks immediately when more than
//! `MAX_WAIT_TIME` has elapsed since the last fire (in particular the very
//! first trigger, matching Go's zero `lastTime`), otherwise callbacks fire
//! once `MIN_WAIT_TIME` passes with no new trigger.

use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;

pub(crate) const MIN_WAIT_TIME: Duration = Duration::from_millis(50);
pub(crate) const MAX_WAIT_TIME: Duration = Duration::from_millis(500);

/// `debounce` — the batching engine. Callbacks are registered under a key
/// (the owning `DirWatch`'s key) and fired together once per coalescing
/// window.
pub(crate) struct Debounce {
    state: Mutex<DebounceState>,
    latch: Mutex<Latch>,
    cond: Condvar,
}

struct DebounceState {
    callbacks: FxHashMap<String, Arc<dyn Fn() + Send + Sync>>,
    last_time: Option<Instant>,
}

struct Latch {
    notified: bool,
    trigger_epoch: u64,
}

impl Debounce {
    /// `newDebounce` — spawns the debounce thread.
    pub(crate) fn new() -> Arc<Debounce> {
        let d = Arc::new(Debounce {
            state: Mutex::new(DebounceState {
                callbacks: FxHashMap::default(),
                last_time: None,
            }),
            latch: Mutex::new(Latch {
                notified: false,
                trigger_epoch: 0,
            }),
            cond: Condvar::new(),
        });
        let loop_debounce = Arc::clone(&d);
        std::thread::spawn(move || loop_debounce.run_loop());
        d
    }

    /// `add` registers a callback under key.
    pub(crate) fn add(&self, key: &str, cb: Arc<dyn Fn() + Send + Sync>) {
        self.state
            .lock()
            .unwrap()
            .callbacks
            .insert(key.to_owned(), cb);
    }

    /// `remove` deregisters the callback for key.
    pub(crate) fn remove(&self, key: &str) {
        self.state.lock().unwrap().callbacks.remove(key);
    }

    /// `trigger` wakes the debounce loop.
    pub(crate) fn trigger(&self) {
        let mut latch = self.latch.lock().unwrap();
        latch.notified = true;
        latch.trigger_epoch += 1;
        self.cond.notify_all();
    }

    /// `loop` — the debounce thread body.
    fn run_loop(&self) {
        loop {
            self.latch_wait();
            self.notify_if_ready();
        }
    }

    /// `notifyIfReady` — fires immediately when more than `MAX_WAIT_TIME` has
    /// elapsed since the last fire (including the first trigger ever, where
    /// Go's zero `lastTime` yields an infinite gap); otherwise waits out the
    /// `MIN_WAIT_TIME` coalescing window.
    fn notify_if_ready(&self) {
        let now = Instant::now();
        let fire_now = {
            let mut state = self.state.lock().unwrap();
            match state.last_time {
                Some(last) if now.saturating_duration_since(last) <= MAX_WAIT_TIME => false,
                _ => {
                    state.last_time = Some(now);
                    true
                }
            }
        };
        if fire_now {
            self.fire_callbacks();
        } else {
            self.coalesce_wait();
        }
    }

    /// `coalesceWait` — waits `MIN_WAIT_TIME`; a new trigger restarts the
    /// loop (the epoch bump is Go's closed `triggerCh`).
    fn coalesce_wait(&self) {
        let epoch = self.latch.lock().unwrap().trigger_epoch;
        let deadline = Instant::now() + MIN_WAIT_TIME;
        let mut latch = self.latch.lock().unwrap();
        loop {
            if latch.trigger_epoch != epoch {
                // New event triggered; fire on the next tick.
                return;
            }
            let now = Instant::now();
            let Some(remaining) = deadline.checked_duration_since(now) else {
                break;
            };
            let (guard, timeout) = self.cond.wait_timeout(latch, remaining).unwrap();
            latch = guard;
            if latch.trigger_epoch != epoch {
                return;
            }
            if timeout.timed_out() {
                break;
            }
        }
        drop(latch);
        self.fire_callbacks();
    }

    /// `fireCallbacks` snapshots and invokes all registered callbacks.
    fn fire_callbacks(&self) {
        let cbs: Vec<Arc<dyn Fn() + Send + Sync>> = {
            let mut state = self.state.lock().unwrap();
            state.last_time = Some(Instant::now());
            state.callbacks.values().cloned().collect()
        };

        self.latch_reset();

        for cb in cbs {
            cb();
        }
    }

    /// `latchWait` — blocks until the next trigger (`waitCh` close).
    fn latch_wait(&self) {
        let mut latch = self.latch.lock().unwrap();
        while !latch.notified {
            latch = self.cond.wait(latch).unwrap();
        }
    }

    /// `latchReset` — re-arms the wait gate after firing (`notified=false`
    /// plus a fresh `waitCh` in Go).
    fn latch_reset(&self) {
        self.latch.lock().unwrap().notified = false;
    }
}
