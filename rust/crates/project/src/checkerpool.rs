// Ported from tsc/internal/project/checkerpool.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;
use tsc_ast::NodeId;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_checker::checker_core::Checker;
use tsc_compiler::checker_pool::{DoneFn, sort_and_deduplicate_diagnostics};
use tsc_core::context::{Context, CheckerLifetime, get_checker_lifetime, get_request_id};
use tsc_core::semaphore::{LimitedSemaphore, Semaphore, SemaphoreGuard, new_limited_semaphore};

/// `checkerHeldAnonymous` — sentinel stored in `held_by` when a checker is
/// held by a caller that has no request ID (e.g., `context.Background()`).
const CHECKER_HELD_ANONYMOUS: &str = "<anonymous>";

/// `CheckerPoolOptions`.
#[derive(Clone, Copy, Default)]
pub struct CheckerPoolOptions {
    /// `MaxCheckers` controls the total number of checker slots per project
    /// (1 dedicated diagnostics checker + N-1 query checkers). Minimum 2.
    /// Zero uses the default (4).
    pub max_checkers: usize,
    /// `IdleTimeout` controls how long an idle checker is kept
    /// before being disposed. Zero uses the default (30s).
    pub idle_timeout: Duration,
}

/// `checkerPool` manages three categories of type checkers for a project:
///
///   - Diagnostics (index 0): A single checker for LSP diagnostics, providing
///     consistent walk order. Idle-cleaned.
///   - Temporary (indices 1+): Ephemeral query checkers for LSP operations.
///     Idle-cleaned after a configurable timeout.
///   - API: A single checker for API operations, providing stable
///     instance identity for reference equality on type/symbol handles.
///     Never idle-cleaned.
///
/// PORT: checkers are `Rc<RefCell<Checker>>` — not `Send` — so the whole
/// pool is `Rc`/interior-mutability based and single-threaded. Two Go
/// mechanics that relied on goroutines become lazy equivalents:
///
///   - `cleanupTimer` (`time.AfterFunc`) becomes `cleanup_deadline`: idle
///     checkers are disposed on the next pool operation after the deadline
///     rather than asynchronously.
///   - `context.AfterFunc` request-affinity cleanup becomes lazy pruning of
///     associations whose request context reports `is_cancelled`, evaluated
///     on each acquisition. Go disables affinity for never-cancellable
///     contexts (`ctx.Done() == nil`); `tsc_core::Context` cannot detect
///     that, so affinity stays enabled — background contexts simply have no
///     request ID and register no association, matching Go's effective
///     behavior.
///
/// The Go channel semaphores (`chan struct{}`) become `LimitedSemaphore`
/// counting gates. `acquire` blocks when exhausted — on a single thread a
/// fully-held semaphore deadlocks just as a Go goroutine that can never be
/// woken would.
#[derive(Clone)]
pub struct CheckerPool {
    /// `Rc<PoolShared>` — release closures clone it to reach back into the
    /// pool, like Go's captured `*checkerPool` pointer.
    shared: Rc<PoolShared>,
}

struct PoolShared {
    opts: CheckerPoolOptions,
    program: Rc<dyn tsc_checker::checker_types::Program>,

    /// `discarded` is set when the pool's program has been replaced. The pool
    /// remains fully functional but stops its idle-cleanup timer so that
    /// query checkers are not disposed until the pool is GC'd.
    discarded: Cell<bool>,

    /// `checkers[0]` is the diagnostics checker.
    /// `checkers[1:]` are ephemeral query checkers.
    /// All are idle-cleaned.
    checkers: RefCell<Vec<Option<Rc<RefCell<Checker>>>>>,
    /// `heldBy[i]` is the requestID holding checker i, `checkerHeldAnonymous`, or "" if not held.
    held_by: RefCell<Vec<String>>,
    /// file → query checker index (1+)
    file_associations: RefCell<FxHashMap<NodeId, usize>>,
    /// requestID → (checker index, request context for lazy AfterFunc cleanup)
    request_associations: RefCell<FxHashMap<String, (usize, Context)>>,

    /// `lastReleased` tracks when each checker was last released.
    last_released: RefCell<Vec<Option<Instant>>>,

    /// `cleanup_deadline` is when the earliest idle checker expires —
    /// the lazy form of Go's `cleanupTimer`.
    cleanup_deadline: Cell<Option<Instant>>,

    /// `persistentChecker` is the API checker. It is never idle-cleaned,
    /// providing stable instance identity for API clients.
    persistent_checker: RefCell<Option<Rc<RefCell<Checker>>>>,
    persistent_held: Cell<bool>,

    diag_sem: LimitedSemaphore,
    query_sem: LimitedSemaphore,
    persistent_sem: LimitedSemaphore,

    log: RefCell<Box<dyn Fn(&str)>>,
    global_diag_accumulated: RefCell<Vec<DiagnosticRef>>,
    global_diag_changed: Cell<bool>,
    /// per-checker count of globals last seen
    global_diag_checker_count: RefCell<Vec<usize>>,
}

/// `newCheckerPool`.
///
/// PORT: `program` is the `Rc<dyn checker_types::Program>` handle the
/// checker constructor erases into; `log` is a `Box<dyn Fn(&str)>`.
pub fn new_checker_pool(
    mut opts: CheckerPoolOptions,
    program: Rc<dyn tsc_checker::checker_types::Program>,
    log: Option<Box<dyn Fn(&str)>>,
) -> CheckerPool {
    if opts.max_checkers == 0 {
        opts.max_checkers = 4;
    } else if opts.max_checkers < 2 {
        opts.max_checkers = 2; // at least 1 diagnostics + 1 query checker
    }
    if opts.idle_timeout.is_zero() {
        opts.idle_timeout = Duration::from_secs(30);
    }
    let query_slots = (opts.max_checkers - 1) as i32;
    CheckerPool {
        shared: Rc::new(PoolShared {
            program,
            opts,
            discarded: Cell::new(false),
            checkers: RefCell::new(vec![None; opts.max_checkers]),
            held_by: RefCell::new(vec![String::new(); opts.max_checkers]),
            file_associations: RefCell::new(FxHashMap::default()),
            request_associations: RefCell::new(FxHashMap::default()),
            last_released: RefCell::new(vec![None; opts.max_checkers]),
            cleanup_deadline: Cell::new(None),
            persistent_checker: RefCell::new(None),
            persistent_held: Cell::new(false),
            diag_sem: new_limited_semaphore(1),
            query_sem: new_limited_semaphore(query_slots),
            persistent_sem: new_limited_semaphore(1),
            log: RefCell::new(log.unwrap_or_else(|| Box::new(|_msg: &str| {}))),
            global_diag_accumulated: RefCell::new(Vec::new()),
            global_diag_changed: Cell::new(false),
            global_diag_checker_count: RefCell::new(vec![0; opts.max_checkers]),
        }),
    }
}

/// `holdTag` returns the value to store in `held_by` for the given request ID.
fn hold_tag(request_id: &str) -> String {
    if request_id.is_empty() {
        CHECKER_HELD_ANONYMOUS.to_string()
    } else {
        request_id.to_string()
    }
}

impl PoolShared {
    fn log(&self, msg: &str) {
        (self.log.borrow())(msg);
    }

    /// Lazy equivalent of `context.AfterFunc` cleanup plus the idle-checker
    /// timer: prune request associations whose context is done, and dispose
    /// expired idle checkers once the cleanup deadline has passed.
    fn housekeeping(self: &Rc<Self>) {
        self.request_associations
            .borrow_mut()
            .retain(|_, (_, ctx)| !ctx.is_cancelled());
        if let Some(deadline) = self.cleanup_deadline.get() {
            if Instant::now() >= deadline {
                self.cleanup_idle_checkers();
            }
        }
    }

    /// `tryReacquireForRequest` checks whether the given request has an idle
    /// associated checker. `guard` is a semaphore slot already claimed by the
    /// caller. Returns `Ok((checker, release))` if the checker was reclaimed
    /// (the guard moves into the release); `Err(guard)` if the caller must
    /// proceed with normal acquisition — it keeps the slot.
    ///
    /// Request affinity is only a preference for an idle checker, not
    /// permission to reuse a held checker: concurrent acquisitions can share
    /// the same request ID.
    fn try_reacquire_for_request(
        self: &Rc<Self>,
        request_id: &str,
        guard: SemaphoreGuard,
        is_diag: bool,
    ) -> Result<(Rc<RefCell<Checker>>, DoneFn), SemaphoreGuard> {
        if request_id.is_empty() {
            return Err(guard);
        }

        let association = {
            let request_associations = self.request_associations.borrow();
            request_associations.get(request_id).map(|(index, _)| *index)
        };
        let Some(index) = association else {
            return Err(guard);
        };

        // Validate that the associated index matches the expected category.
        // Index 0 is for diagnostics; indices 1+ are for queries.
        if (is_diag && index != 0) || (!is_diag && index == 0) {
            self.request_associations.borrow_mut().remove(request_id);
            return Err(guard);
        }

        let c = self.checkers.borrow()[index].clone();
        let Some(c) = c else {
            self.request_associations.borrow_mut().remove(request_id);
            return Err(guard);
        };

        if self.held_by.borrow()[index].is_empty() {
            self.held_by.borrow_mut()[index] = request_id.to_string();
            return Ok((c.clone(), self.create_release(request_id, index, &c, guard)));
        }

        Err(guard)
    }

    /// `getDiagnosticsChecker` returns the dedicated diagnostics checker (index 0).
    /// Creates it on first use. Blocks on `diag_sem` if it's currently in use.
    fn get_diagnostics_checker(
        self: &Rc<Self>,
        ctx: &Context,
        request_id: &str,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        const DIAG_INDEX: usize = 0;

        let guard = self.diag_sem.acquire();
        match self.try_reacquire_for_request(request_id, guard, true) {
            Ok((c, release)) => return (c, release),
            Err(guard) => {
                // Token consumed — proceed with normal acquisition.
                self.housekeeping();

                if self.checkers.borrow()[DIAG_INDEX].is_none() {
                    self.log("checkerpool: Creating diagnostics checker");
                    let c = Rc::new(RefCell::new(Checker::new_checker(
                        self.program.clone(),
                        None,
                    )));
                    self.checkers.borrow_mut()[DIAG_INDEX] = Some(c);
                }

                let c = self.checkers.borrow()[DIAG_INDEX].clone().unwrap();
                self.held_by.borrow_mut()[DIAG_INDEX] = hold_tag(request_id);
                self.log(&format!(
                    "checkerpool: Acquired diagnostics checker for request {}",
                    hold_tag(request_id)
                ));
                if !request_id.is_empty() {
                    let mut associations = self.request_associations.borrow_mut();
                    if !associations.contains_key(request_id) {
                        associations
                            .insert(request_id.to_string(), (DIAG_INDEX, ctx.clone()));
                    }
                }
                (c.clone(), self.create_release(request_id, DIAG_INDEX, &c, guard))
            }
        }
    }

    /// `getQueryChecker` returns an ephemeral query checker from indices 1+.
    /// Uses request affinity, then file affinity, then finds/creates.
    /// Blocks on `query_sem` if all query slots are in use.
    fn get_query_checker(
        self: &Rc<Self>,
        ctx: &Context,
        request_id: &str,
        file: Option<NodeId>,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        let guard = self.query_sem.acquire();
        match self.try_reacquire_for_request(request_id, guard, false) {
            Ok((c, release)) => return (c, release),
            Err(guard) => {
                // Token consumed — proceed with normal acquisition.
                self.housekeeping();

                // Try file affinity.
                if let Some(file) = file {
                    let index = self.file_associations.borrow().get(&file).copied();
                    if let Some(index) = index {
                        if index > 0 {
                            let c = self.checkers.borrow()[index].clone();
                            if let Some(c) = c {
                                if self.held_by.borrow()[index].is_empty() {
                                    self.held_by.borrow_mut()[index] = hold_tag(request_id);
                                    if !request_id.is_empty() {
                                        let mut associations =
                                            self.request_associations.borrow_mut();
                                        if !associations.contains_key(request_id) {
                                            associations.insert(
                                                request_id.to_string(),
                                                (index, ctx.clone()),
                                            );
                                        }
                                    }
                                    return (
                                        c.clone(),
                                        self.create_release(request_id, index, &c, guard),
                                    );
                                }
                            }
                        }
                    }
                }

                // Find any available query checker or create one.
                let (c, index) = self.find_or_create_query_checker_locked();
                self.held_by.borrow_mut()[index] = hold_tag(request_id);
                self.log(&format!(
                    "checkerpool: Acquired query checker {} for request {}",
                    index,
                    hold_tag(request_id)
                ));
                if !request_id.is_empty() {
                    let mut associations = self.request_associations.borrow_mut();
                    if !associations.contains_key(request_id) {
                        associations.insert(request_id.to_string(), (index, ctx.clone()));
                    }
                }
                if let Some(file) = file {
                    self.file_associations.borrow_mut().insert(file, index);
                }
                (c.clone(), self.create_release(request_id, index, &c, guard))
            }
        }
    }

    /// `findOrCreateQueryCheckerLocked` returns an idle query checker or creates one
    /// in the first empty slot. The semaphore guarantees at least one slot is
    /// available.
    fn find_or_create_query_checker_locked(&self) -> (Rc<RefCell<Checker>>, usize) {
        // Prefer an existing idle checker.
        for i in 1..self.checkers.borrow().len() {
            if let Some(c) = &self.checkers.borrow()[i] {
                if self.held_by.borrow()[i].is_empty() {
                    return (c.clone(), i);
                }
            }
        }
        // Create in the first empty slot.
        for i in 1..self.checkers.borrow().len() {
            if self.checkers.borrow()[i].is_none() {
                self.log(&format!("checkerpool: Creating query checker {i}"));
                let c = Rc::new(RefCell::new(Checker::new_checker(
                    self.program.clone(),
                    None,
                )));
                self.checkers.borrow_mut()[i] = Some(c.clone());
                return (c, i);
            }
        }
        panic!("checkerpool: no available query slot despite holding semaphore token")
    }

    /// `getPersistentChecker`.
    fn get_persistent_checker(self: &Rc<Self>) -> (Rc<RefCell<Checker>>, DoneFn) {
        let guard = self.persistent_sem.acquire();

        if self.persistent_checker.borrow().is_none() {
            self.log("checkerpool: Creating persistent checker");
            *self.persistent_checker.borrow_mut() = Some(Rc::new(RefCell::new(
                Checker::new_checker(self.program.clone(), None),
            )));
        }

        let c = self.persistent_checker.borrow().clone().unwrap();
        self.persistent_held.set(true);

        let this = self.clone();
        let released = Rc::new(Cell::new(false));
        (
            c.clone(),
            Box::new(move || {
                if released.replace(true) {
                    return; // sync.OnceFunc
                }
                this.persistent_held.set(false);
                if c.borrow().was_canceled() {
                    // A canceled checker panics on reuse, so drop it; the next API
                    // acquisition will create a fresh persistent checker.
                    this.log("checkerpool: Persistent checker was canceled, disposing");
                    if let Some(current) = this.persistent_checker.borrow().as_ref() {
                        if Rc::ptr_eq(current, &c) {
                            *this.persistent_checker.borrow_mut() = None;
                        }
                    }
                }
                drop(guard);
            }),
        )
    }

    /// `createRelease` — the `func()` returned with each checker. `FnOnce`
    /// enforces `sync.OnceFunc`'s single-call semantics at the type level;
    /// the `released` flag keeps it idempotent if a caller drops it twice
    /// through other means.
    fn create_release(
        self: &Rc<Self>,
        request_id: &str,
        index: usize,
        c: &Rc<RefCell<Checker>>,
        guard: SemaphoreGuard,
    ) -> DoneFn {
        let c = c.clone();
        let released = Rc::new(Cell::new(false));
        let this = self.clone();
        let request_id = request_id.to_string();
        Box::new(move || {
            if released.replace(true) {
                return; // sync.OnceFunc
            }

            if c.borrow().was_canceled() {
                // Canceled checkers must be disposed.
                this.log(&format!(
                    "checkerpool: Checker {} for request {} was canceled, disposing",
                    index,
                    hold_tag(&request_id)
                ));
                this.dispose_checker_locked(index, &c);
            } else {
                // Query checkers can produce incidental errors while serializing types.
                if index == 0 {
                    this.merge_global_diagnostics_from_checker_locked(index, &c);
                }
                this.held_by.borrow_mut()[index] = String::new();
                this.last_released.borrow_mut()[index] = Some(Instant::now());
                if !this.discarded.get() {
                    this.schedule_cleanup_locked();
                }
                // If discarded, skip scheduling cleanup — checkers stay alive
                // until the pool is garbage collected so that API clients can
                // continue resolving type/symbol handles.
            }

            // Release the semaphore slot (Go received from the channel).
            drop(guard);
        })
    }

    /// `scheduleCleanupLocked` sets the earliest pending checker-expiration
    /// deadline among all currently idle, unheld checkers (the lazy form of
    /// Go's cleanup timer reset). Must NOT be called on discarded pools.
    fn schedule_cleanup_locked(&self) {
        let mut earliest_deadline: Option<Instant> = None;
        for i in 0..self.checkers.borrow().len() {
            if self.checkers.borrow()[i].is_none()
                || !self.held_by.borrow()[i].is_empty()
                || self.last_released.borrow()[i].is_none()
            {
                continue;
            }
            let deadline = self.last_released.borrow()[i].unwrap() + self.opts.idle_timeout;
            if earliest_deadline.is_none_or(|earliest| deadline < earliest) {
                earliest_deadline = Some(deadline);
            }
        }
        self.cleanup_deadline.set(earliest_deadline);
    }

    /// `cleanupIdleCheckers` disposes checkers that have been idle for longer
    /// than the idle timeout. The API checker is separate and never
    /// idle-cleaned.
    fn cleanup_idle_checkers(&self) {
        // The timer callback may already have been in flight when Discard()
        // stopped it. Bail out without rescheduling so a discarded pool
        // doesn't keep itself alive.
        if self.discarded.get() {
            return;
        }
        let now = Instant::now();
        for i in 0..self.checkers.borrow().len() {
            let Some(c) = self.checkers.borrow()[i].clone() else {
                continue;
            };
            if !self.held_by.borrow()[i].is_empty() {
                continue;
            }
            let Some(last_released) = self.last_released.borrow()[i] else {
                continue;
            };
            let idle = now.duration_since(last_released);
            if idle >= self.opts.idle_timeout {
                self.log(&format!(
                    "checkerpool: Disposing idle checker {i} (idle {idle:?})"
                ));
                self.dispose_checker_locked(i, &c);
            }
        }
        // Reschedule for any remaining idle-but-not-yet-expired checkers.
        self.schedule_cleanup_locked();
    }

    /// `disposeCheckerLocked` removes a checker from the pool and clears all
    /// associations (file and request) that reference it.
    fn dispose_checker_locked(&self, index: usize, c: &Rc<RefCell<Checker>>) {
        tsc_debug::assert_!(
            self.checkers.borrow()[index]
                .as_ref()
                .is_some_and(|stored| Rc::ptr_eq(stored, c))
        );
        self.checkers.borrow_mut()[index] = None;
        self.held_by.borrow_mut()[index] = String::new();
        self.global_diag_checker_count.borrow_mut()[index] = 0;
        self.last_released.borrow_mut()[index] = None;
        self.file_associations
            .borrow_mut()
            .retain(|_, idx| *idx != index);
        self.request_associations
            .borrow_mut()
            .retain(|_, (idx, _)| *idx != index);
    }

    /// `mergeGlobalDiagnosticsFromCheckerLocked` checks if the given checker
    /// has produced new global diagnostics since the last time we looked,
    /// and if so merges them into the accumulated set.
    fn merge_global_diagnostics_from_checker_locked(
        &self,
        index: usize,
        c: &Rc<RefCell<Checker>>,
    ) {
        let globals = c.borrow_mut().get_global_diagnostics();
        if globals.len() == self.global_diag_checker_count.borrow()[index] {
            return;
        }
        self.global_diag_checker_count.borrow_mut()[index] = globals.len();
        let before = self.global_diag_accumulated.borrow().len();
        {
            let mut accumulated = self.global_diag_accumulated.borrow_mut();
            accumulated.extend(globals);
            *accumulated = sort_and_deduplicate_diagnostics(std::mem::take(&mut accumulated));
        }
        if self.global_diag_accumulated.borrow().len() != before {
            self.global_diag_changed.set(true);
        }
    }
}

impl CheckerPool {
    /// `GetChecker`.
    pub fn get_checker(
        &self,
        ctx: &Context,
        file: Option<NodeId>,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        let lifetime = get_checker_lifetime(ctx);
        let request_id = get_request_id(ctx);

        match lifetime {
            CheckerLifetime::Diagnostics => {
                self.shared.get_diagnostics_checker(ctx, request_id)
            }
            CheckerLifetime::Api => self.shared.get_persistent_checker(),
            _ => self.shared.get_query_checker(ctx, request_id, file),
        }
    }

    /// `GetGlobalDiagnostics` returns the global diagnostics accumulated from
    /// the dedicated diagnostics checker across its instances during this
    /// pool's lifetime.
    pub fn get_global_diagnostics(&self) -> Vec<DiagnosticRef> {
        self.shared.global_diag_accumulated.borrow().clone()
    }

    /// `TakeNewGlobalDiagnostics` reports whether new global diagnostics have
    /// been accumulated since the last call, and resets the flag.
    pub fn take_new_global_diagnostics(&self) -> bool {
        self.shared.global_diag_changed.replace(false)
    }

    /// `Discard` signals that this pool's program has been replaced. The pool
    /// remains functional but stops its idle-cleanup timer so that checkers
    /// are not disposed until the pool is GC'd. The API checker is unaffected
    /// since it is never idle-cleaned.
    pub fn discard(&self) {
        if self.shared.discarded.get() {
            return; // already discarded
        }
        self.shared.log("checkerpool: Discarding pool, stopping idle cleanup");
        self.shared.discarded.set(true);
        self.shared.cleanup_deadline.set(None);
    }
}

/// `var _ compiler.CheckerPool = (*checkerPool)(nil)`
impl tsc_compiler::checker_pool::CheckerPool for CheckerPool {
    fn get_checker(&self, ctx: Context, file: Option<NodeId>) -> (Rc<RefCell<Checker>>, DoneFn) {
        CheckerPool::get_checker(self, &ctx, file)
    }
}
