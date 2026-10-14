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
use std::rc::Rc;

const CHUNK: usize = 1024;

pub struct Chunked<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
}

impl<T> Default for Chunked<T> {
    fn default() -> Self {
        Chunked {
            chunks: Vec::new(),
            len: 0,
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
/// `Rc<UnsafeCell<..>>` shape of the arenas it replaces.
pub struct ChunkedArena<T> {
    inner: Rc<UnsafeCell<Chunked<T>>>,
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
            inner: Rc::new(UnsafeCell::new(Chunked::default())),
        }
    }
}

#[allow(unsafe_code)] // single-threaded pipeline; UnsafeCell reaches the slab
impl<T> ChunkedArena<T> {
    /// Append `v`, returning its dense index. `&self` — interior
    /// mutability like the Box-arena `alloc` it replaces.
    #[inline]
    pub fn alloc(&self, v: T) -> usize {
        // SAFETY: same single-threaded aliasing contract as the arena
        // callers it serves (see `SymbolArena`/`TypeArena` docs).
        unsafe { (*self.inner.get()).push(v) }
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
        Rc::as_ptr(&self.inner) as usize
    }
}
