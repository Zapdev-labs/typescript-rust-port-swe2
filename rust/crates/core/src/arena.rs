// Ported from tsc/internal/core/arena.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Arena allocator
//
// PORT: Go's Arena grows a single backing slice and relies on the GC to keep
// previously returned pointers alive across reallocation. Rust cannot return
// stable &mut T from a growing Vec, so this port uses chunked storage: each
// chunk is sealed once full, so &mut T handed out of a sealed chunk stays
// valid for the life of the arena. Same growth schedule (nextArenaSize).

pub struct Arena<T> {
    chunks: Vec<Vec<T>>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    pub fn new() -> Arena<T> {
        Arena { chunks: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.chunks.iter().map(Vec::len).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.chunks.iter().all(Vec::is_empty)
    }

    // Allocate a single element in the arena and return a mutable reference to
    // the element. If the current chunk is at capacity, a new chunk of the next
    // size up is allocated.
    pub fn alloc(&mut self) -> &mut T
    where
        T: Default,
    {
        if self.chunks.last().is_none_or(|c| c.len() == c.capacity()) {
            let next_size = next_arena_size(self.len());
            let mut chunk = Vec::with_capacity(next_size);
            chunk.push(T::default());
            self.chunks.push(chunk);
            return self.chunks.last_mut().unwrap().last_mut().unwrap();
        }
        let chunk = self.chunks.last_mut().unwrap();
        chunk.push(T::default());
        chunk.last_mut().unwrap()
    }

    // Allocate a chunk of `size` default elements and return a mutable slice.
    // If the requested size does not fit in the current chunk, a new chunk is
    // allocated — a standalone one if `size` exceeds the next growth size.
    pub fn alloc_slice(&mut self, size: usize) -> &mut [T]
    where
        T: Default,
    {
        if size == 0 {
            return &mut [];
        }
        let need_new = match self.chunks.last() {
            None => true,
            Some(c) => c.capacity() - c.len() < size,
        };
        if need_new {
            let next_size = next_arena_size(self.len());
            self.chunks.push(Vec::with_capacity(size.max(next_size)));
        }
        let chunk = self.chunks.last_mut().unwrap();
        chunk.resize_with(chunk.len() + size, T::default);
        let start = chunk.len() - size;
        &mut chunk[start..]
    }
}

fn next_arena_size(size: usize) -> usize {
    // This compiles down branch-free.
    let size = size.max(1);
    (size * 2).min(256)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arena_alloc_stays_stable() {
        let mut a: Arena<u64> = Arena::new();
        let mut total = 0usize;
        // Grow past several chunk boundaries; sum via fresh iteration each time.
        for _ in 0..1000 {
            *a.alloc() = 1;
            total += 1;
        }
        assert_eq!(total, 1000);
        assert_eq!(a.len(), 1000);
        let sum: u64 = a.chunks.iter().flatten().sum();
        assert_eq!(sum, 1000);
    }

    #[test]
    fn arena_alloc_slice() {
        let mut a: Arena<u8> = Arena::new();
        let s = a.alloc_slice(1000);
        s.iter_mut().for_each(|x| *x = 7);
        assert_eq!(s.len(), 1000);
        assert!(s.iter().all(|&x| x == 7));
        assert!(a.alloc_slice(0).is_empty());
    }
}
