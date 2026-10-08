// Ported from tsc/internal/collections/ordered_map.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

use indexmap::{Equivalent, IndexMap};
use rustc_hash::FxBuildHasher;
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// OrderedMap is an insertion ordered map.
///
/// PORT: Go stores `keys []K` + `mp map[K]V`; `IndexMap` provides identical
/// semantics — insertion-ordered iteration, in-place value replacement on a
/// re-`set`, and order-preserving removal via `shift_remove`. Go's embedded
/// `noCopy` marker is unneeded: Rust never copies structs implicitly.
#[derive(Debug)]
pub struct OrderedMap<K, V> {
    mp: IndexMap<K, V, FxBuildHasher>,
}

impl<K, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        Self {
            mp: IndexMap::default(),
        }
    }
}

/// MapEntry is a key-value pair used to construct an OrderedMap.
#[derive(Debug)]
pub struct MapEntry<K, V> {
    pub key: K,
    pub value: V,
}

impl<K: Eq + Hash, V> OrderedMap<K, V> {
    /// Creates an empty OrderedMap (the Go zero value).
    pub fn new() -> Self {
        Self::default()
    }

    /// NewOrderedMapWithSizeHint creates a new OrderedMap with a hint for the number of elements it will contain.
    pub fn with_size_hint(hint: usize) -> Self {
        Self {
            mp: IndexMap::with_capacity_and_hasher(hint, FxBuildHasher),
        }
    }

    /// NewOrderedMapFromList creates an OrderedMap from a list of MapEntry items.
    pub fn from_list(items: impl IntoIterator<Item = MapEntry<K, V>>) -> Self {
        let items = items.into_iter();
        let mut mp = Self::with_size_hint(items.size_hint().0);
        for item in items {
            mp.set(item.key, item.value);
        }
        mp
    }

    /// Set sets a key-value pair in the map.
    pub fn set(&mut self, key: K, value: V) {
        // IndexMap::insert keeps the original position when overwriting an
        // existing key, exactly like Go's `mp[key] = value` after the
        // presence-check-guarded `keys` append.
        self.mp.insert(key, value);
    }

    /// Get retrieves a value from the map.
    ///
    /// PORT: Go returns `(V, bool)`; Rust returns `Option<&V>`. The key is
    /// borrowed, so e.g. `&str` works against `OrderedMap<String, _>`.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.mp.get(key)
    }

    /// PORT: not in the Go API. Go callers mutate values through pointers or
    /// map assignment; `get_mut` is the Rust equivalent for in-place mutation.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.mp.get_mut(key)
    }

    /// GetOrZero retrieves a value from the map, or returns the zero value of the value type if the key is not present.
    pub fn get_or_zero<Q>(&self, key: &Q) -> V
    where
        V: Default + Clone,
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.mp.get(key).cloned().unwrap_or_default()
    }

    /// EntryAt retrieves the key-value pair at the specified index.
    ///
    /// PORT: Go returns `(K, V, bool)` copies; Rust returns `Option<(&K, &V)>`.
    pub fn entry_at(&self, index: usize) -> Option<(&K, &V)> {
        self.mp.get_index(index)
    }

    /// Has returns true if the map contains the key.
    pub fn has<Q>(&self, key: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.mp.contains_key(key)
    }

    /// Delete removes a key-value pair from the map.
    ///
    /// PORT: Go splices the key out of the keys slice, preserving the order of
    /// the remaining keys; `shift_remove` is the exact IndexMap equivalent.
    pub fn delete<Q>(&mut self, key: &Q) -> Option<V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.mp.shift_remove(key)
    }

    /// Keys returns an iterator over the keys in the map.
    /// A slice of the keys can be obtained by calling `.copied().collect()` / `.cloned().collect()`.
    ///
    /// PORT: Go's iterator is a live view that also enumerates items inserted
    /// during iteration; a Rust iterator borrows the map, so mutation during
    /// iteration is impossible — collect the keys first at such call sites.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.mp.keys()
    }

    /// Values returns an iterator over the values in the map.
    /// A slice of the values can be obtained by calling `.cloned().collect()`.
    ///
    /// PORT: same live-view caveat as `keys`.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.mp.values()
    }

    /// PORT: not in the Go API — mutable counterpart of `values` for in-place
    /// updates (Go callers write back through `Set` or pointers).
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.mp.values_mut()
    }

    /// Entries returns an iterator over the key-value pairs in the map.
    ///
    /// PORT: same live-view caveat as `keys`.
    pub fn entries(&self) -> impl Iterator<Item = (&K, &V)> {
        self.mp.iter()
    }

    /// PORT: not in the Go API — mutable counterpart of `entries`.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&K, &mut V)> {
        self.mp.iter_mut()
    }

    /// Clear removes all key-value pairs from the map.
    /// The space allocated for the map will be reused.
    pub fn clear(&mut self) {
        self.mp.clear();
    }

    /// Size returns the number of key-value pairs in the map.
    pub fn size(&self) -> usize {
        self.mp.len()
    }

    /// IsEmpty returns true if the map contains no key-value pairs.
    pub fn is_empty(&self) -> bool {
        self.mp.is_empty()
    }

    /// EqualFunc compares keys in insertion order and values using equal.
    /// A nil map differs from a non-nil empty map; backing-storage allocation is ignored.
    ///
    /// PORT: Go's possibly-nil `*OrderedMap` receivers/arguments map to
    /// `Option<&OrderedMap>` — call as
    /// `OrderedMap::equal_func(a.as_ref(), b.as_ref(), eq)`.
    pub fn equal_func(
        this: Option<&Self>,
        other: Option<&Self>,
        equal: impl Fn(&V, &V) -> bool,
    ) -> bool {
        let (Some(a), Some(b)) = (this, other) else {
            // m == other when both nil; m == nil || other == nil otherwise.
            return this.is_none() && other.is_none();
        };
        if std::ptr::eq(a, b) {
            return true;
        }
        a.mp.len() == b.mp.len()
            && a.mp.keys().eq(b.mp.keys())
            && a.mp
                .iter()
                .all(|(k, v)| b.get(k).is_some_and(|v2| equal(v, v2)))
    }
}

impl<K: Clone + Eq + Hash, V: Clone> Clone for OrderedMap<K, V> {
    /// Clone returns a shallow copy of the map.
    fn clone(&self) -> Self {
        Self {
            mp: self.mp.clone(),
        }
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for OrderedMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(items: I) -> Self {
        let items = items.into_iter();
        let mut m = Self::with_size_hint(items.size_hint().0);
        for (k, v) in items {
            m.set(k, v);
        }
        m
    }
}

impl<'a, K: Eq + Hash, V> IntoIterator for &'a OrderedMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = indexmap::map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.mp.iter()
    }
}

// TODO(port): OrderedMap JSON marshal/unmarshal — needs tsc-json
// (Go MarshalJSONTo/UnmarshalJSONFrom are implemented against the internal
// json package; the serde impls below provide the equivalent JSON object
// round-trip in the interim).
//
// PORT: Go's resolveKeyName accepts string, encoding.TextMarshaler, and
// integer keys. serde map keys cover the same shapes: strings and integers
// serialize as JSON object keys (serde_json renders integer keys in decimal,
// matching strconv.FormatInt/FormatUint).

impl<K, V> Serialize for OrderedMap<K, V>
where
    K: Serialize + Eq + Hash,
    V: Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.mp.len()))?;
        for (k, v) in &self.mp {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }
}

// By convention, to approximate the behavior of Unmarshal itself,
// Unmarshalers implement UnmarshalJSON([]byte("null")) as a no-op.
// https://pkg.go.dev/encoding/json#Unmarshaler
// TODO: reconsider
//
// PORT: serde deserialization constructs a fresh map, so the no-op becomes an
// empty map (equivalent for a zero-value target). Non-object values error,
// as in Go ("cannot unmarshal non-object JSON value into Map").
impl<'de, K, V> Deserialize<'de> for OrderedMap<K, V>
where
    K: Deserialize<'de> + Eq + Hash,
    V: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct OrderedMapVisitor<K, V>(PhantomData<fn() -> OrderedMap<K, V>>);

        impl<'de, K, V> Visitor<'de> for OrderedMapVisitor<K, V>
        where
            K: Deserialize<'de> + Eq + Hash,
            V: Deserialize<'de>,
        {
            type Value = OrderedMap<K, V>;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a JSON object")
            }

            fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
                let mut m = OrderedMap::with_size_hint(access.size_hint().unwrap_or(0));
                while let Some((key, value)) = access.next_entry()? {
                    m.set(key, value);
                }
                Ok(m)
            }

            fn visit_unit<E>(self) -> Result<Self::Value, E> {
                Ok(OrderedMap::new())
            }

            fn visit_none<E>(self) -> Result<Self::Value, E> {
                Ok(OrderedMap::new())
            }

            fn visit_some<D: Deserializer<'de>>(
                self,
                deserializer: D,
            ) -> Result<Self::Value, D::Error> {
                deserializer.deserialize_map(self)
            }
        }

        // deserialize_option routes `null` to visit_none (the no-op) and any
        // other value to visit_some → deserialize_map → visit_map or error.
        deserializer.deserialize_option(OrderedMapVisitor(PhantomData))
    }
}

pub fn diff_ordered_maps<K, V>(
    m1: Option<&OrderedMap<K, V>>,
    m2: Option<&OrderedMap<K, V>>,
    on_added: impl FnMut(&K, &V),
    on_removed: impl FnMut(&K, &V),
    on_modified: impl FnMut(&K, &V, &V),
) where
    K: Eq + Hash,
    V: PartialEq,
{
    diff_ordered_maps_func(m1, m2, |a, b| a == b, on_added, on_removed, on_modified);
}

/// DiffOrderedMapsFunc calls onAdded for keys only in m2, onRemoved for keys
/// only in m1, and onModified for keys in both whose values differ per
/// equalValues. Iteration is in insertion order for both maps.
///
/// PORT: Go's callbacks take copies; Rust callbacks borrow the entries.
pub fn diff_ordered_maps_func<K: Eq + Hash, V>(
    m1: Option<&OrderedMap<K, V>>,
    m2: Option<&OrderedMap<K, V>>,
    equal_values: impl Fn(&V, &V) -> bool,
    mut on_added: impl FnMut(&K, &V),
    mut on_removed: impl FnMut(&K, &V),
    mut on_modified: impl FnMut(&K, &V, &V),
) {
    if let Some(m2) = m2 {
        for (k, v2) in m2.entries() {
            if m1.is_none_or(|m1| m1.get(k).is_none()) {
                on_added(k, v2);
            }
        }
    }
    if let Some(m1) = m1 {
        for (k, v1) in m1.entries() {
            match m2.and_then(|m2| m2.get(k)) {
                Some(v2) if !equal_values(v1, v2) => on_modified(k, v1, v2),
                Some(_) => {}
                None => on_removed(k, v1),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pad_int(n: i32) -> String {
        format!("{n:>10}")
    }

    // strings.EqualFold — the test data is ASCII-only.
    #[allow(clippy::ptr_arg)] // must match the `Fn(&V, &V)` callback shape where V = String
    fn equal_fold(a: &String, b: &String) -> bool {
        a.eq_ignore_ascii_case(b)
    }

    // TestOrderedMapEqualFunc
    #[test]
    fn ordered_map_equal_func() {
        let zero = OrderedMap::<i32, String>::new();
        let allocated = OrderedMap::<i32, String>::with_size_hint(0);
        let ordered = OrderedMap::from_list(vec![
            MapEntry {
                key: 1,
                value: "a".to_string(),
            },
            MapEntry {
                key: 2,
                value: "b".to_string(),
            },
        ]);
        let reversed = OrderedMap::from_list(vec![
            MapEntry {
                key: 2,
                value: "b".to_string(),
            },
            MapEntry {
                key: 1,
                value: "a".to_string(),
            },
        ]);
        let uppercase = OrderedMap::from_list(vec![
            MapEntry {
                key: 1,
                value: "A".to_string(),
            },
            MapEntry {
                key: 2,
                value: "B".to_string(),
            },
        ]);
        let mut different = ordered.clone();
        different.set(2, "c".to_string());
        let mut cleared = ordered.clone();
        cleared.clear();
        let ordered_clone = ordered.clone();

        type OM = OrderedMap<i32, String>;
        let cases: &[(&str, Option<&OM>, Option<&OM>, bool)] = &[
            ("nil", None, None, true),
            ("nil versus empty", None, Some(&zero), false),
            ("empty allocation", Some(&zero), Some(&allocated), true),
            ("cleared allocation", Some(&zero), Some(&cleared), true),
            ("same", Some(&ordered), Some(&ordered), true),
            ("clone", Some(&ordered), Some(&ordered_clone), true),
            ("different order", Some(&ordered), Some(&reversed), false),
            ("different values", Some(&ordered), Some(&different), false),
            ("different length", Some(&zero), Some(&ordered), false),
            ("custom equality", Some(&ordered), Some(&uppercase), true),
        ];
        for (name, a, b, expected) in cases.iter().copied() {
            assert_eq!(
                OrderedMap::equal_func(a, b, equal_fold),
                expected,
                "case {name}"
            );
            assert_eq!(
                OrderedMap::equal_func(b, a, equal_fold),
                expected,
                "case {name} reversed"
            );
        }
    }

    // TestOrderedMap
    #[test]
    fn ordered_map() {
        let mut m = OrderedMap::<i32, String>::new();

        assert!(!m.has(&1));

        const N: i32 = 1000;
        const START: i32 = 1;
        const END: i32 = START + N;

        // Seed the map with ascending keys and values for easier testing.
        for i in START..END {
            m.set(i, pad_int(i));
        }

        assert_eq!(m.size(), N as usize);

        // Attempt to overwrite existing keys in reverse order.
        for i in (START..END).rev() {
            m.set(i, pad_int(i));
        }

        assert_eq!(m.size(), N as usize);

        for i in START..END {
            let v = m.get(&i).unwrap();
            assert_eq!(*v, pad_int(i));
        }

        for (k, v) in m.entries() {
            assert_eq!(*v, pad_int(*k));
        }

        let keys: Vec<i32> = m.keys().copied().collect();
        assert_eq!(keys.len(), N as usize);
        assert!(keys.is_sorted());

        let values: Vec<String> = m.values().cloned().collect();
        assert_eq!(values.len(), N as usize);
        assert!(values.is_sorted());

        let first_key = *m.keys().next().unwrap();
        assert_eq!(first_key, START);

        let first_value = m.values().next().unwrap().clone();
        assert_eq!(first_value, pad_int(START));

        let (first_key, first_value) = m.entries().next().unwrap();
        assert_eq!(*first_key, START);
        assert_eq!(*first_value, pad_int(START));

        for i in (START + 1)..END {
            let v = m.delete(&i).unwrap();
            assert_eq!(v, pad_int(i));
            assert!(!m.has(&i));

            assert!(m.get(&i).is_none());
            assert!(m.delete(&i).is_none());
        }

        assert_eq!(m.size(), 1);
        assert!(m.has(&START));

        let v = m.delete(&START).unwrap();
        assert_eq!(v, pad_int(START));

        assert_eq!(m.size(), 0);
    }

    // TestOrderedMapClone
    #[test]
    fn ordered_map_clone() {
        let mut m = OrderedMap::<i32, String>::new();
        m.set(1, "one".to_string());
        m.set(2, "two".to_string());

        let clone = m.clone();

        assert!(!std::ptr::eq(&m, &clone));
        assert_eq!(clone.size(), 2);
        assert_eq!(clone.keys().copied().collect::<Vec<_>>(), vec![1, 2]);
        assert_eq!(
            clone.values().map(String::as_str).collect::<Vec<_>>(),
            vec!["one", "two"]
        );

        assert_eq!(clone.get(&1).map(String::as_str), Some("one"));

        m.delete(&1);

        assert_eq!(m.size(), 1);
        assert_eq!(clone.size(), 2);
        assert_eq!(clone.keys().copied().collect::<Vec<_>>(), vec![1, 2]);
        assert_eq!(
            clone.values().map(String::as_str).collect::<Vec<_>>(),
            vec!["one", "two"]
        );
    }

    // TestOrderedMapClear
    #[test]
    fn ordered_map_clear() {
        let mut m = OrderedMap::<i32, String>::new();
        m.set(1, "one".to_string());
        m.set(2, "two".to_string());

        m.clear();

        assert_eq!(m.size(), 0);
    }

    // TestOrderedMapWithSizeHint — Go measures allocations via
    // testing.AllocsPerRun; there is no Rust equivalent. The hint is passed
    // through to IndexMap::with_capacity_and_hasher.
    #[test]
    fn ordered_map_with_size_hint() {
        const N: usize = 1024;
        let mut m = OrderedMap::<i32, i32>::with_size_hint(N);
        for i in 0..N {
            m.set(i as i32, i as i32);
        }
        assert_eq!(m.size(), N);
    }

    // TestOrderedMapUnmarshalJSON — PORT: Go exercises the internal json
    // package; here the serde impls are tested via serde_json. The object
    // key ordering and `null`-as-no-op semantics are preserved.
    #[test]
    fn ordered_map_unmarshal_json() {
        let m: OrderedMap<String, serde_json::Value> =
            serde_json::from_str(r#"{"a": 1, "b": "two", "c": { "d": 4 } }"#).unwrap();
        assert_eq!(m.size(), 3);
        assert_eq!(m.get_or_zero("a"), serde_json::json!(1));
        // Insertion order is preserved.
        assert_eq!(
            m.keys().map(String::as_str).collect::<Vec<_>>(),
            vec!["a", "b", "c"]
        );

        // `null` is a no-op (fresh map stays empty).
        let m: OrderedMap<String, serde_json::Value> = serde_json::from_str("null").unwrap();
        assert_eq!(m.size(), 0);

        // Non-object values are an error (Go: "cannot unmarshal non-object JSON value into Map").
        assert!(serde_json::from_str::<OrderedMap<String, serde_json::Value>>("\"foo\"").is_err());

        // Invalid key type errors (Go: error containing "unmarshal").
        assert!(
            serde_json::from_str::<OrderedMap<i32, serde_json::Value>>(r#"{"a": 1, "b": "two"}"#)
                .is_err()
        );
    }

    // Serialize round-trip preserving insertion order.
    #[test]
    fn ordered_map_serialize_json() {
        let mut m = OrderedMap::<i32, i32>::new();
        m.set(2, 20);
        m.set(1, 10);
        assert_eq!(serde_json::to_string(&m).unwrap(), r#"{"2":20,"1":10}"#);
        let back: OrderedMap<i32, i32> =
            serde_json::from_str(&serde_json::to_string(&m).unwrap()).unwrap();
        assert!(OrderedMap::equal_func(Some(&m), Some(&back), |a, b| a == b));
    }
}
