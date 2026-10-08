// Ported from tsc/internal/core/context.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's stdlib `context.Context` is an interface carrying (a) an
// immutable WithValue chain and (b) a cancellation signal via Done(). The
// Rust port is a concrete `Context` with the same two capabilities: a
// TypeId-keyed value chain (unexported Go key types become marker structs)
// and a cancel-token tree (SPEC §5.5 — `AtomicBool` + `Condvar` wakeup in
// place of `Done()` channels). Callers needing Go's `<-ctx.Done()` should
// use `wait_cancelled()` or poll `is_cancelled()`; see
// `Semaphore::try_acquire` for the select-style usage.

use std::any::{Any, TypeId};
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex, Weak};

/// A typed context key — Go's unexported key types become zero-sized markers
/// keyed by TypeId. Define `pub struct FooKey;` + `ContextKey::<FooKey, V>::new()`.
pub struct ContextKey<K, V>(PhantomData<fn() -> (K, V)>);

impl<K, V> ContextKey<K, V> {
    pub const fn new() -> Self {
        ContextKey(PhantomData)
    }
}

impl<K, V> Default for ContextKey<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

struct ValueNode {
    parent: Option<Arc<ValueNode>>,
    key: TypeId,
    value: Box<dyn Any + Send + Sync>,
}

struct CancelState {
    parent: Option<Arc<CancelState>>,
    cancelled: AtomicBool,
    // PORT: Go's `Done()` channel broadcast becomes a per-state Condvar plus
    // recursive propagation into live children.
    children: Mutex<Vec<Weak<CancelState>>>,
    wait_lock: Mutex<()>,
    wait_cvar: Condvar,
}

impl CancelState {
    fn is_cancelled(&self) -> bool {
        if self.cancelled.load(Ordering::Acquire) {
            return true;
        }
        match &self.parent {
            Some(parent) => parent.is_cancelled(),
            None => false,
        }
    }

    fn cancel(&self) {
        if self.cancelled.swap(true, Ordering::AcqRel) {
            return;
        }
        self.wait_cvar.notify_all();
        for weak in self.children.lock().unwrap().iter() {
            if let Some(child) = weak.upgrade() {
                child.cancel();
            }
        }
    }
}

/// The function type returned by [`Context::with_cancel`]; call it to cancel
/// the returned context and all its descendants.
pub struct CancelFunc(Arc<CancelState>);

impl CancelFunc {
    pub fn cancel(&self) {
        self.0.cancel();
    }
}

/// `context.Context` — a cancellation token plus an immutable value chain.
#[derive(Clone)]
pub struct Context {
    cancel: Arc<CancelState>,
    values: Option<Arc<ValueNode>>,
}

impl Default for Context {
    fn default() -> Self {
        Self::background()
    }
}

impl Context {
    /// `context.Background()` / `context.TODO()`.
    pub fn background() -> Context {
        Context {
            cancel: Arc::new(CancelState {
                parent: None,
                cancelled: AtomicBool::new(false),
                children: Mutex::new(Vec::new()),
                wait_lock: Mutex::new(()),
                wait_cvar: Condvar::new(),
            }),
            values: None,
        }
    }

    /// `context.WithCancel(parent)` — the returned `CancelFunc` cancels this
    /// context and its descendants.
    pub fn with_cancel(&self) -> (Context, CancelFunc) {
        let state = Arc::new(CancelState {
            parent: Some(self.cancel.clone()),
            cancelled: AtomicBool::new(self.cancel.cancelled.load(Ordering::Acquire)),
            children: Mutex::new(Vec::new()),
            wait_lock: Mutex::new(()),
            wait_cvar: Condvar::new(),
        });
        self.cancel
            .children
            .lock()
            .unwrap()
            .push(Arc::downgrade(&state));
        let ctx = Context {
            cancel: state.clone(),
            values: self.values.clone(),
        };
        (ctx, CancelFunc(state))
    }

    /// `ctx.Err() != nil` — true once this context or any ancestor is cancelled.
    pub fn is_cancelled(&self) -> bool {
        self.cancel.is_cancelled()
    }

    /// `<-ctx.Done()` — blocks until this context or any ancestor is cancelled.
    /// Returns immediately if already cancelled.
    pub fn wait_cancelled(&self) {
        let mut guard = self.cancel.wait_lock.lock().unwrap();
        while !self.is_cancelled() {
            guard = self.cancel.wait_cvar.wait(guard).unwrap();
        }
    }

    /// `context.WithValue(ctx, key, value)` — returns a new context whose
    /// value chain shadows `self`'s.
    pub fn with_value<K: 'static, V: Any + Send + Sync>(
        &self,
        _key: ContextKey<K, V>,
        value: V,
    ) -> Context {
        Context {
            cancel: self.cancel.clone(),
            values: Some(Arc::new(ValueNode {
                parent: self.values.clone(),
                key: TypeId::of::<K>(),
                value: Box::new(value),
            })),
        }
    }

    /// `ctx.Value(key)` — walks the value chain; `None` if absent.
    pub fn value<K: 'static, V: Any>(&self, _key: ContextKey<K, V>) -> Option<&V> {
        let mut node = self.values.as_deref();
        while let Some(n) = node {
            if n.key == TypeId::of::<K>() {
                // The ContextKey<K, V> type links key and value types, so this
                // downcast always succeeds for the stored type.
                return n.value.downcast_ref::<V>();
            }
            node = n.parent.as_deref();
        }
        None
    }
}

struct RequestIdKey;
struct CheckerLifetimeKey;

const REQUEST_ID_KEY: ContextKey<RequestIdKey, String> = ContextKey::new();
const CHECKER_LIFETIME_KEY: ContextKey<CheckerLifetimeKey, CheckerLifetime> = ContextKey::new();

pub fn with_request_id(ctx: &Context, id: String) -> Context {
    ctx.with_value(REQUEST_ID_KEY, id)
}

pub fn get_request_id(ctx: &Context) -> &str {
    ctx.value(REQUEST_ID_KEY).map_or("", String::as_str)
}

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(i32)]
pub enum CheckerLifetime {
    #[default]
    Temporary = 0,
    Diagnostics = 1,
    Api = 2,
}

pub fn with_checker_lifetime(ctx: &Context, lifetime: CheckerLifetime) -> Context {
    ctx.with_value(CHECKER_LIFETIME_KEY, lifetime)
}

pub fn get_checker_lifetime(ctx: &Context) -> CheckerLifetime {
    ctx.value(CHECKER_LIFETIME_KEY)
        .copied()
        .unwrap_or(CheckerLifetime::Temporary)
}
