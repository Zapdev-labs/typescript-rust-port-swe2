// Ported from tsc/internal/collections/ordered_set.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::hash::Hash;

use indexmap::Equivalent;

use crate::ordered_map::OrderedMap;

/// OrderedSet an insertion ordered set.
#[derive(Debug)]
pub struct OrderedSet<T> {
    m: OrderedMap<T, ()>, // Go: OrderedMap[T, struct{}]
}

impl<T> Default for OrderedSet<T> {
    fn default() -> Self {
        Self {
            m: OrderedMap::default(),
        }
    }
}

impl<T: Eq + Hash> OrderedSet<T> {
    /// Creates an empty OrderedSet (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// NewOrderedSetWithSizeHint creates a new OrderedSet with a hint for the number of elements it will contain.
    pub fn with_size_hint(hint: usize) -> Self {
        Self {
            m: OrderedMap::with_size_hint(hint),
        }
    }

    /// Add adds a value to the set.
    pub fn add(&mut self, value: T) {
        self.m.set(value, ());
    }

    /// Has returns true if the set contains the value.
    pub fn has<Q>(&self, value: &Q) -> bool
    where
        Q: Hash + Equivalent<T> + ?Sized,
    {
        self.m.has(value)
    }

    /// Delete removes a value from the set.
    pub fn delete<Q>(&mut self, value: &Q) -> bool
    where
        Q: Hash + Equivalent<T> + ?Sized,
    {
        self.m.delete(value).is_some()
    }

    /// Values returns an iterator over the values in the set.
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.m.keys()
    }

    /// Clear removes all elements from the set.
    /// The space allocated for the set will be reused.
    pub fn clear(&mut self) {
        self.m.clear();
    }

    /// Size returns the number of elements in the set.
    pub fn size(&self) -> usize {
        self.m.size()
    }

    /// IsEmpty returns true if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.m.is_empty()
    }
}

impl<T: Clone + Eq + Hash> Clone for OrderedSet<T> {
    /// Clone returns a shallow copy of the set.
    fn clone(&self) -> Self {
        Self { m: self.m.clone() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TestOrderedSet
    #[test]
    fn ordered_set() {
        let mut s = OrderedSet::<i32>::new();

        s.add(1);
        s.add(2);
        s.add(3);

        assert!(s.has(&1));
        assert!(s.has(&2));
        assert!(s.has(&3));

        assert!(s.delete(&2));

        let values: Vec<i32> = s.values().copied().collect();
        assert_eq!(values.len(), 2);
        assert!(values.is_sorted());

        s.clear();

        assert_eq!(s.size(), 0);
        assert!(!s.has(&1));
        assert!(!s.has(&2));
        assert!(!s.has(&3));

        let s2 = s.clone();
        assert!(!std::ptr::eq(&s, &s2));
        assert_eq!(s2.size(), 0);
    }

    // TestOrderedSetWithSizeHint — Go measures allocations via
    // testing.AllocsPerRun; there is no Rust equivalent.
    #[test]
    fn ordered_set_with_size_hint() {
        const N: usize = 1024;
        let mut m = OrderedSet::<i32>::with_size_hint(N);
        for i in 0..N {
            m.add(i as i32);
        }
        assert_eq!(m.size(), N);
    }
}
