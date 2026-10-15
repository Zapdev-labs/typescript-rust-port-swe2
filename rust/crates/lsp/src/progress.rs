// Ported from tsc/internal/lsp @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `ch chan progressEvent` (buffered 64) → `mpsc::sync_channel(64)`;
//   `go p.run()` → `std::thread::spawn` on an `Arc` clone. Rust has no
//   `select`, so the run loop's `select { <-p.ch / <-delay.C /
//   <-done() }` becomes `recv_timeout` bounded by the earlier of the
//   delay deadline and a `done` poll (`is_cancelled()`), and the sends in
//   `start`/`finish` become `try_send` + `wait_cancelled_timeout` retries —
//   the same poll shape
//   as `Semaphore::try_acquire`/`AsyncConn::call`. Wake-up latency on
//   shutdown is ≤ `DONE_POLL_INTERVAL` instead of select-instant.
// - `delay *time.Timer` → `Option<Instant>`: `stopDelay()` clears the
//   option, and a deadline is cleared on firing (a Go `Timer.C` drains
//   after one send and can never signal again).
// - `args []any` → `Vec<String>` (pre-stringified), matching
//   `diagnostics::Message::localize` and the sibling
//   `project::Client::progress_start` signature.
// - `message *diagnostics.Message` → `&'static diagnostics::Message`:
//   diagnostics live in `pub static`s, and `&'static` is the only
//   `Send`-able borrow across the channel boundary.
// - `p.delay <= 0` → `delay.is_zero()`: `Duration` cannot be negative.
// - Go's `done` select arm is deterministic here (checked at the top of
//   each loop) where Go picks randomly among ready cases; both orderings
//   are legal Go behavior.
//
// PORT(sibling): this file expects the `crate::server::Server` port to
// expose `background_ctx: tsc_core::context::Context`, `get_locale()`
// (the `tsc_project::client::Client` impl),
// `send_notification(&lsproto::NotificationInfo<P>, P)`, and
// `send_client_request_fire_and_forget(&lsproto::RequestInfo<P, R>, P)`.
// Reconcile with the sibling server.rs port.

use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};

use tsc_collections::OrderedMap;
use tsc_core::context::Context;
use tsc_core::core::first_or_nil_seq;
use tsc_diagnostics as diagnostics;
use tsc_lsproto as lsproto;
use tsc_project::client::Client as _;

use crate::server::Server;

/// `select`/`send` wake-up granularity for `done()` — see header.
const DONE_POLL_INTERVAL: Duration = Duration::from_millis(10);

/// `type progressEvent struct`
struct ProgressEvent {
    message: diagnostics::Message,
    args: Vec<String>,
    finish: bool,
}

/// `type progressReporter interface` — the LSP transport operations needed
/// by [`ProjectLoadingProgress`] so the progress logic can be tested
/// without a full `Server` instance.
///
/// PORT: `done() <-chan struct{}` becomes `done() -> &Context` — the ported
/// `Context` carries the same cancellation signal via `is_cancelled()` /
/// `wait_cancelled()` that the closed channel provided.
pub(crate) trait ProgressReporter: Send + Sync {
    /// `done` — cancelled when the server is shutting down.
    fn done(&self) -> &Context;
    /// `localize` — converts a diagnostic message to a display string.
    fn localize(&self, msg: &diagnostics::Message, args: &[String]) -> String;
    /// `createWorkDoneProgress` — asks the client to create a progress token.
    fn create_work_done_progress(&self, token: &str);
    /// `sendProgress` — sends a `$/progress` notification.
    fn send_progress(&self, token: &str, value: lsproto::WorkDoneProgressBeginOrReportOrEnd);
}

/// `type serverProgressReporter struct` — adapts `*Server` to
/// [`ProgressReporter`].
struct ServerProgressReporter {
    server: Arc<Server>,
}

impl ProgressReporter for ServerProgressReporter {
    fn done(&self) -> &Context {
        &self.server.background_ctx
    }

    fn localize(&self, msg: &diagnostics::Message, args: &[String]) -> String {
        msg.localize(&self.server.get_locale(), args)
    }

    fn create_work_done_progress(&self, token: &str) {
        let _ = self.server.send_client_request_fire_and_forget(
            &lsproto::WINDOW_WORK_DONE_PROGRESS_CREATE_INFO,
            Some(lsproto::WorkDoneProgressCreateParams {
                token: lsproto::IntegerOrString {
                    integer: None,
                    string: Some(token.to_string()),
                },
            }),
        );
    }

    fn send_progress(&self, token: &str, value: lsproto::WorkDoneProgressBeginOrReportOrEnd) {
        let _ = self.server.send_notification(
            &lsproto::PROGRESS_INFO,
            Some(lsproto::ProgressParams {
                token: lsproto::IntegerOrString {
                    integer: None,
                    string: Some(token.to_string()),
                },
                value,
            }),
        );
    }
}

/// `type projectLoadingProgress struct` — manages LSP WorkDoneProgress
/// indicators for long-running operations. A single persistent thread
/// processes start/finish events, maintains a ref-counted map of active
/// operations, and sends progress messages in order.
///
/// To avoid flickering on fast operations, the indicator is not shown
/// until `delay` has elapsed since the first start event. If all
/// operations complete before then, no progress UI is displayed.
///
/// `start`/`finish` may block if the internal buffer (64 events) is full,
/// but will bail out if the server's background context is cancelled.
pub(crate) struct ProjectLoadingProgress {
    reporter: Arc<dyn ProgressReporter>,
    /// `ch chan progressEvent` — the send half; the receive half moved to
    /// `run`'s thread.
    tx: mpsc::SyncSender<ProgressEvent>,
    /// `delay` — time to wait before showing progress UI.
    delay: Duration,
}

/// `func newProjectLoadingProgress(server *Server, delay time.Duration) *projectLoadingProgress`
pub(crate) fn new_project_loading_progress(
    server: &Arc<Server>,
    delay: Duration,
) -> Arc<ProjectLoadingProgress> {
    new_project_loading_progress_from_reporter(
        Arc::new(ServerProgressReporter {
            server: server.clone(),
        }),
        delay,
    )
}

/// `func newProjectLoadingProgressFromReporter(reporter progressReporter, delay time.Duration) *projectLoadingProgress`
pub(crate) fn new_project_loading_progress_from_reporter(
    reporter: Arc<dyn ProgressReporter>,
    delay: Duration,
) -> Arc<ProjectLoadingProgress> {
    let (tx, rx) = mpsc::sync_channel(64);
    let p = Arc::new(ProjectLoadingProgress {
        reporter,
        tx,
        delay,
    });
    // `go p.run()` — detached like the goroutine; the run thread holds its
    // own `Arc` and exits on `done` (or when `p` drops and the channel
    // disconnects).
    let run = Arc::clone(&p);
    std::thread::spawn(move || run.run(rx));
    p
}

impl ProjectLoadingProgress {
    /// `func (p *projectLoadingProgress) start(message *diagnostics.Message, args ...any)`
    pub(crate) fn start(&self, message: diagnostics::Message, args: &[String]) {
        self.send_event(ProgressEvent {
            message,
            args: args.to_vec(),
            finish: false,
        });
    }

    /// `func (p *projectLoadingProgress) finish(message *diagnostics.Message, args ...any)`
    pub(crate) fn finish(&self, message: diagnostics::Message, args: &[String]) {
        self.send_event(ProgressEvent {
            message,
            args: args.to_vec(),
            finish: true,
        });
    }

    /// `select { case p.ch <- ev: / <-p.reporter.done(): }` — the channel
    /// send becomes `try_send` retries (`SyncSender::send_timeout` is
    /// unstable), with `done` polled via `wait_cancelled_timeout` between
    /// attempts while the buffer is full — the condvar wakes instantly on
    /// cancellation (Rust channels have no select).
    fn send_event(&self, ev: ProgressEvent) {
        let mut ev = ev;
        loop {
            match self.tx.try_send(ev) {
                Ok(()) => return,
                Err(mpsc::TrySendError::Full(e)) => ev = e,
                // Go's channel is never closed; `self` owns the only sender.
                Err(mpsc::TrySendError::Disconnected(_)) => return,
            }
            // Buffer full: server shutting down → drop the event.
            if self
                .reporter
                .done()
                .wait_cancelled_timeout(DONE_POLL_INTERVAL)
            {
                return;
            }
        }
    }

    /// `func (p *projectLoadingProgress) run()` — the persistent worker that
    /// processes all progress events. It owns all mutable state: no
    /// external synchronization needed.
    fn run(&self, rx: mpsc::Receiver<ProgressEvent>) {
        let mut loading: OrderedMap<String, i32> = OrderedMap::new();
        let mut token = String::new(); // current token; empty if no progress active
        let mut token_id = 0;
        let mut begun = false; // whether "begin" has been sent for the current token

        // `delay *time.Timer` + `stopDelay()` → `delay_deadline`/`None`.
        let mut delay_deadline: Option<Instant> = None;
        let mut delay_fired = false; // true after the delay timer fires

        loop {
            // `case <-p.reporter.done()` — polled. `stopDelay()` needs no
            // work here: the deadline is a bare `Instant`, not a resource.
            if self.reporter.done().is_cancelled() {
                return;
            }

            // `delayC()` — the deadline, capped at the `done` poll
            // interval so shutdown is still observed while armed.
            let timeout = match delay_deadline {
                Some(d) => d
                    .saturating_duration_since(Instant::now())
                    .min(DONE_POLL_INTERVAL),
                None => DONE_POLL_INTERVAL,
            };

            match rx.recv_timeout(timeout) {
                // `case ev := <-p.ch:`
                Ok(ev) => {
                    let text = self.reporter.localize(&ev.message, &ev.args);
                    if !ev.finish {
                        let count = loading.get_or_zero(text.as_str());
                        loading.set(text.clone(), count + 1);
                        if token.is_empty() {
                            token_id += 1;
                            token = format!("tsgo-loading-{token_id}");
                            begun = false;
                            if self.delay.is_zero() {
                                delay_fired = true;
                                self.reporter.create_work_done_progress(&token);
                            } else {
                                delay_fired = false;
                                delay_deadline = Some(Instant::now() + self.delay);
                            }
                        }
                        if delay_fired {
                            begun = self.begin_or_report(&token, &text, begun);
                        }
                    } else {
                        let count = loading.get_or_zero(text.as_str());
                        if count <= 1 {
                            loading.delete(text.as_str());
                        } else {
                            loading.set(text.clone(), count - 1);
                        }
                        if token.is_empty() {
                            continue;
                        }
                        if loading.size() == 0 {
                            if begun {
                                self.reporter.send_progress(
                                    &token,
                                    lsproto::WorkDoneProgressBeginOrReportOrEnd {
                                        end: Some(lsproto::WorkDoneProgressEnd {
                                            kind: lsproto::StringLiteralEnd,
                                            message: None,
                                        }),
                                        ..Default::default()
                                    },
                                );
                            }
                            // `stopDelay()`.
                            delay_deadline = None;
                            token.clear();
                        } else if delay_fired {
                            let first = first_or_nil_seq(Some(loading.keys()))
                                .cloned()
                                .unwrap_or_default();
                            self.reporter.send_progress(
                                &token,
                                lsproto::WorkDoneProgressBeginOrReportOrEnd {
                                    report: Some(lsproto::WorkDoneProgressReport {
                                        kind: lsproto::StringLiteralReport,
                                        cancellable: None,
                                        message: Some(first),
                                        percentage: None,
                                    }),
                                    ..Default::default()
                                },
                            );
                        }
                    }
                }

                // `case <-delayC():` — a `Timeout` that reached the delay
                // deadline; earlier poll wake-ups just re-check `done`.
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    let Some(deadline) = delay_deadline else {
                        continue;
                    };
                    if Instant::now() < deadline {
                        continue;
                    }
                    // The Go timer channel is drained by this receive and
                    // can never fire again.
                    delay_deadline = None;
                    delay_fired = true;
                    if !token.is_empty() && loading.size() > 0 {
                        self.reporter.create_work_done_progress(&token);
                        let first = first_or_nil_seq(Some(loading.keys()))
                            .cloned()
                            .unwrap_or_default();
                        begun = self.begin_or_report(&token, &first, begun);
                    }
                }

                // Go's `ch` is never closed; here `self` owns the only
                // sender, so this is unreachable until after `run` exits —
                // treated as `done` (server shutdown).
                Err(mpsc::RecvTimeoutError::Disconnected) => return,
            }
        }
    }

    /// `func (p *projectLoadingProgress) beginOrReport(token, text string, begun bool) bool`
    ///
    /// Sends `WorkDoneProgressBegin` if not yet begun, otherwise sends
    /// `WorkDoneProgressReport`. Returns `true` to indicate begun state.
    fn begin_or_report(&self, token: &str, text: &str, begun: bool) -> bool {
        if !begun {
            let title = self.reporter.localize(&diagnostics::Loading, &[]);
            self.reporter.send_progress(
                token,
                lsproto::WorkDoneProgressBeginOrReportOrEnd {
                    begin: Some(lsproto::WorkDoneProgressBegin {
                        kind: lsproto::StringLiteralBegin,
                        title,
                        cancellable: None,
                        message: Some(text.to_string()),
                        percentage: None,
                    }),
                    ..Default::default()
                },
            );
        } else {
            self.reporter.send_progress(
                token,
                lsproto::WorkDoneProgressBeginOrReportOrEnd {
                    report: Some(lsproto::WorkDoneProgressReport {
                        kind: lsproto::StringLiteralReport,
                        cancellable: None,
                        message: Some(text.to_string()),
                        percentage: None,
                    }),
                    ..Default::default()
                },
            );
        }
        true
    }
}
