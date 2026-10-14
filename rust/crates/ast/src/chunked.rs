//! A chunked slab arena: stable element addresses without per-element
//! heap allocation.
//!
//! Elements are pushed into fixed-capacity inner `Vec`s (`CHUNK`). An
//! inner Vec never grows past its initial capacity, so its buffer never
//! moves and element pointers stay valid for the arena's lifetime — the
//! same contract the `Rc<UnsafeCell<Vec<Box<T>>>>` arenas provided, but
//! with amortized allocation instead of one `Box` per element. Used by
//! `TypeArena` (`tsc-checker`) and `SymbolArena` (this crate).

use std::cell::UnsafeCell;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

const CHUNK: usize = 1024;

pub struct Chunked<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
    /// Parallel-append mode (scoped-thread bind): `alloc` hands out dense
    /// indices from `par_cursor` and writes element storage through a raw
    /// pointer — no per-element lock. Chunk *creation* still takes
    /// `par_lock` (once per CHUNK allocations); `par_chunks_ready`
    /// publishes grown chunks to lock-free readers. The outer `chunks`
    /// Vec is pre-reserved by `enter_parallel` so it cannot realloc
    /// mid-scope, and workers only read/write slots they allocated.
    /// `exit_parallel` repairs each inner Vec's `len` (element writes
    /// bypass it) so drops run correctly.
    par_enabled: AtomicBool,
    par_lock: Mutex<()>,
    par_cursor: AtomicUsize,
    par_chunks_ready: AtomicUsize,
}

impl<T> Default for Chunked<T> {
    fn default() -> Self {
        Chunked {
            chunks: Vec::new(),
            len: 0,
            par_enabled: AtomicBool::new(false),
            par_lock: Mutex::new(()),
            par_cursor: AtomicUsize::new(0),
            par_chunks_ready: AtomicUsize::new(0),
        }
    }
}

#[allow(unsafe_code)] // slab internals index chunks unchecked for speed
impl<T> Chunked<T> {
    /// Append `v`, returning its dense index.
    pub fn push(&mut self, v: T) -> usize {
        if self.chunks.last().is_none_or(|c| c.len() == CHUNK) {
            self.chunks.push(Vec::with_capacity(CHUNK));
        }
        let chunk = self.chunks.last_mut().expect("non-empty after push");
        debug_assert!(chunk.len() < chunk.capacity());
        chunk.push(v);
        let id = self.len;
        self.len += 1;
        id
    }

    /// Element pointer — stable: the inner Vec was created with
    /// `with_capacity(CHUNK)` and never exceeds that capacity.
    #[inline]
    pub fn get(&self, i: usize) -> *const T {
        debug_assert!(i < self.len);
        unsafe { self.chunks.get_unchecked(i / CHUNK).as_ptr().add(i % CHUNK) }
    }

    /// Mutable element pointer — same stability contract as `get`.
    #[inline]
    pub fn get_mut(&mut self, i: usize) -> *mut T {
        debug_assert!(i < self.len);
        unsafe { self.chunks.get_unchecked_mut(i / CHUNK).as_mut_ptr().add(i % CHUNK) }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// Shared handle (`Clone` shares the same backing slab) matching the
/// `Rc<UnsafeCell<..>>` shape of the arenas it replaces. `Arc` so the
/// scoped-thread parallel bind can clone handles inside workers — the
/// `UnsafeCell` contents are still single-threaded except under the
/// `par_enabled` protocol (see `Chunked::par_lock`).
pub struct ChunkedArena<T> {
    inner: Arc<UnsafeCell<Chunked<T>>>,
}

impl<T> Clone for ChunkedArena<T> {
    fn clone(&self) -> Self {
        ChunkedArena {
            inner: self.inner.clone(),
        }
    }
}

impl<T> Default for ChunkedArena<T> {
    fn default() -> Self {
        ChunkedArena {
            inner: Arc::new(UnsafeCell::new(Chunked::default())),
        }
    }
}

#[allow(unsafe_code)] // single-threaded pipeline; UnsafeCell reaches the slab
impl<T> ChunkedArena<T> {
    /// Append `v`, returning its dense index. `&self` — interior
    /// mutability like the Box-arena `alloc` it replaces. Under
    /// `enter_parallel` the push is serialized by `par_lock`.
    #[inline]
    pub fn alloc(&self, v: T) -> usize {
        // SAFETY: single-threaded aliasing contract as the arena callers it
        // serves; parallel mode serializes pushes on `par_lock` and the
        // outer `chunks` Vec is pre-reserved so it cannot realloc.
        unsafe {
            let inner = &mut *self.inner.get();
            if inner.par_enabled.load(Ordering::Relaxed) {
                // Lock-free append: grab a dense index, ensure its chunk
                // exists, write through the spare-capacity pointer. The
                // inner Vec's `len` is repaired at `exit_parallel`.
                let idx = inner.par_cursor.fetch_add(1, Ordering::Relaxed);
                let c = idx / CHUNK;
                if c >= inner.par_chunks_ready.load(Ordering::Acquire) {
                    let _g = inner.par_lock.lock().unwrap();
                    while c >= inner.chunks.len() {
                        inner.chunks.push(Vec::with_capacity(CHUNK));
                    }
                    inner
                        .par_chunks_ready
                        .store(inner.chunks.len(), Ordering::Release);
                }
                inner
                    .chunks
                    .get_unchecked_mut(c)
                    .as_mut_ptr()
                    .add(idx % CHUNK)
                    .write(v);
                idx
            } else {
                inner.push(v)
            }
        }
    }

    /// Enable parallel `alloc` for a scoped-thread phase and pre-reserve
    /// the outer chunk vector so `chunks` cannot realloc mid-scope —
    /// `get`/`get_mut` read `chunks` lock-free, which is only sound while
    /// its buffer is stable. `extra` is a worst-case upper bound on new
    /// elements expected during the phase.
    pub fn enter_parallel(&self, extra_elements: usize) {
        unsafe {
            let inner = &mut *self.inner.get();
            let chunks_needed = (inner.len + extra_elements).div_ceil(CHUNK) + 2;
            if inner.chunks.capacity() < chunks_needed {
                inner.chunks.reserve(chunks_needed - inner.chunks.capacity());
            }
            inner.par_cursor.store(inner.len, Ordering::Relaxed);
            inner
                .par_chunks_ready
                .store(inner.chunks.len(), Ordering::Relaxed);
            inner.par_enabled.store(true, Ordering::Release);
        }
    }

    /// End the parallel-append phase. Must run after all workers have
    /// joined: repairs each inner Vec's `len` (parallel writes bypassed
    /// it) so later drops and `push` boundary checks see the real fill.
    pub fn exit_parallel(&self) {
        unsafe {
            let inner = &mut *self.inner.get();
            let total = inner.par_cursor.load(Ordering::Relaxed);
            for (i, chunk) in inner.chunks.iter_mut().enumerate() {
                let filled = total.saturating_sub(i * CHUNK).min(CHUNK);
                debug_assert!(filled >= chunk.len());
                chunk.set_len(filled);
            }
            inner.len = total;
            inner.par_enabled.store(false, Ordering::Release);
        }
    }

    /// Stable element pointer.
    #[inline]
    pub fn get(&self, i: usize) -> *const T {
        unsafe { (*self.inner.get()).get(i) }
    }

    /// Stable mutable element pointer.
    #[inline]
    pub fn get_mut(&self, i: usize) -> *mut T {
        unsafe { (*self.inner.get()).get_mut(i) }
    }

    pub fn len(&self) -> usize {
        unsafe { (*self.inner.get()).len() }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Stable identity token distinguishing arena instances.
    pub fn arena_id(&self) -> usize {
        Arc::as_ptr(&self.inner) as usize
    }
}
