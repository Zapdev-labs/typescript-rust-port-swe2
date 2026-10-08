// Ported from tsc/internal/core/linkstore.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Links store
//
// PORT: Go stores *V pointers allocated from an Arena in a map; the arena
// exists only to amortize allocation. Rust stores Box<V> per entry —
// semantically identical (stable address, lazy zero-init), one alloc per
// entry instead of chunked. V: Default plays the role of Go zero values.

use std::collections::HashMap;

pub struct LinkStore<K, V> {
    entries: HashMap<K, Box<V>>,
}

impl<K, V> Default for LinkStore<K, V> {
    fn default() -> Self {
        Self { entries: HashMap::new() }
    }
}

impl<K: Eq + std::hash::Hash, V: Default> LinkStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&mut self, key: K) -> &mut V {
        self.entries.entry(key).or_default()
    }

    pub fn has(&self, key: &K) -> bool {
        self.entries.contains_key(key)
    }

    pub fn try_get(&mut self, key: &K) -> Option<&mut V> {
        self.entries.get_mut(key).map(|b| &mut **b)
    }
}

const PAGE_SHIFT: u32 = 8;
const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
const PAGE_MASK: u64 = PAGE_SIZE as u64 - 1;
const MAX_PAGE_COUNT: u64 = 65536;

// Implements a sparse-array-like structure for storing elements keyed by
// dense uint64 keys. Elements are stored in fixed-size pages of 256 entries
// and an index of pages is maintained in an array for lower valued page
// indices and a map for higher valued page indices.
//
// PORT: pages are boxed fixed arrays. Entries are Default-initialized in
// bulk when a page is allocated (Go allocates zeroed [256]V), so `V: Default`
// is required and get() may return an element the caller never wrote —
// identical visibility to Go.
pub struct PagedLinkStore<V> {
    page_map: HashMap<u64, Box<[V; PAGE_SIZE]>>, // Page map for page indices above maxPageCount
    page_list: Vec<Option<Box<[V; PAGE_SIZE]>>>, // Page table for page indices below maxPageCount
}

impl<V> Default for PagedLinkStore<V> {
    fn default() -> Self {
        Self { page_map: HashMap::new(), page_list: Vec::new() }
    }
}

impl<V: Default> PagedLinkStore<V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&mut self, key: u64) -> &mut V {
        let page_index = key >> PAGE_SHIFT;
        let page: &mut Box<[V; PAGE_SIZE]> = if page_index < MAX_PAGE_COUNT {
            let idx = page_index as usize;
            if idx >= self.page_list.len() {
                self.page_list.resize_with(idx + 1, || None);
            }
            self.page_list[idx].get_or_insert_with(|| Box::new(std::array::from_fn(|_| V::default())))
        } else {
            self.page_map
                .entry(page_index)
                .or_insert_with(|| Box::new(std::array::from_fn(|_| V::default())))
        };
        &mut page[(key & PAGE_MASK) as usize]
    }

    pub fn try_get(&mut self, key: u64) -> Option<&mut V> {
        let page_index = key >> PAGE_SHIFT;
        let page: Option<&mut Box<[V; PAGE_SIZE]>> = if page_index < MAX_PAGE_COUNT {
            self.page_list.get_mut(page_index as usize)?.as_mut()
        } else {
            self.page_map.get_mut(&page_index)
        };
        page.map(|p| &mut p[(key & PAGE_MASK) as usize])
    }

    pub fn has(&self, key: u64) -> bool {
        let page_index = key >> PAGE_SHIFT;
        if page_index < MAX_PAGE_COUNT {
            matches!(self.page_list.get(page_index as usize), Some(Some(_)))
        } else {
            self.page_map.contains_key(&page_index)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn link_store_lazy_alloc() {
        let mut s: LinkStore<u32, Vec<i32>> = LinkStore::new();
        assert!(!s.has(&1));
        s.get(1).push(42);
        assert!(s.has(&1));
        assert_eq!(s.try_get(&1).unwrap()[0], 42);
        assert!(s.try_get(&2).is_none());
        assert!(!s.has(&2)); // try_get does not allocate
    }

    #[test]
    fn paged_link_store() {
        let mut s: PagedLinkStore<u32> = PagedLinkStore::new();
        *s.get(0) = 10;
        *s.get(255) = 20;
        *s.get(256) = 30; // second page
        *s.get(u64::MAX) = 40; // page map path
        assert_eq!(*s.try_get(0).unwrap(), 10);
        assert_eq!(*s.try_get(255).unwrap(), 20);
        assert_eq!(*s.try_get(256).unwrap(), 30);
        assert_eq!(*s.try_get(u64::MAX).unwrap(), 40);
        assert!(s.has(300));
        // has() is page-granular like Go's TryGet!=nil: key 511 shares page 1
        // with key 256, so it reports present even though never written.
        assert!(s.has(511));
        assert!(!s.has(65536)); // page 256, never allocated
        assert!(s.try_get(99999).is_none());
    }
}
