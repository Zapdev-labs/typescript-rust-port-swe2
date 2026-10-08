// Ported from tsc/internal/project/dirty/syncmap_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;

use crate::cloneable::Cloneable;
use crate::syncmap::SyncMap;

/// `testValue` is a simple cloneable type for testing — Go's `*testValue`
/// pointer becomes an `Arc<Mutex>` handle so entries can be shared across
/// threads exactly like Go's shared pointer.
#[derive(Debug)]
struct TestData {
    data: String,
}

#[derive(Debug)]
struct TestVal(Arc<Mutex<TestData>>);

impl TestVal {
    fn new(data: &str) -> TestVal {
        TestVal(Arc::new(Mutex::new(TestData {
            data: data.to_owned(),
        })))
    }

    fn get(&self) -> String {
        self.0.lock().unwrap().data.clone()
    }

    fn set(&self, data: &str) {
        self.0.lock().unwrap().data = data.to_owned();
    }
}

impl Clone for TestVal {
    /// Go `*testValue` assignment — shares the pointee.
    fn clone(&self) -> Self {
        TestVal(Arc::clone(&self.0))
    }
}

impl Cloneable for TestVal {
    /// `v.Clone()` — a fresh pointee.
    fn clone_value(&self) -> Self {
        TestVal(Arc::new(Mutex::new(TestData {
            data: self.get(),
        })))
    }
}

fn new_base(entries: &[(&str, &str)]) -> FxHashMap<String, TestVal> {
    entries
        .iter()
        .map(|(k, v)| ((*k).to_owned(), TestVal::new(v)))
        .collect()
}

// `proxy for race condition`
#[test]
fn sync_map_proxy_for_race() {
    // Create a sync map with a base value
    let base = new_base(&[("key1", "original")]);
    let sync_map = SyncMap::new(Some(base));

    // Load the same entry from multiple goroutines to simulate race condition
    let mut entry1 = None;
    let mut entry2 = None;
    std::thread::scope(|s| {
        s.spawn(|| {
            entry1 = sync_map.load(&"key1".to_owned());
            assert!(entry1.is_some(), "entry1 should be loaded");
        });
        s.spawn(|| {
            entry2 = sync_map.load(&"key1".to_owned());
            assert!(entry2.is_some(), "entry2 should be loaded");
        });
    });
    let entry1 = entry1.unwrap();
    let entry2 = entry2.unwrap();

    // Both entries should exist and have the same initial value
    assert_eq!("original", entry1.value().unwrap().get());
    assert_eq!("original", entry2.value().unwrap().get());
    assert!(!entry1.dirty());
    assert!(!entry2.dirty());

    // Now try to change both entries concurrently to trigger the proxy mechanism.
    // (This change doesn't actually have to be concurrent to test the proxy behavior,
    // but might exercise concurrency safety in -race mode.)
    std::thread::scope(|s| {
        let e1 = entry1.clone();
        let e2 = entry2.clone();
        s.spawn(move || {
            e1.change(|v| v.set("changed_by_entry1"));
        });
        s.spawn(move || {
            e2.change(|v| v.set("changed_by_entry2"));
        });
    });

    // After the race, one entry should have proxyFor set and both should reflect the same final state
    // The exact final value depends on which goroutine wins the race, but both entries should be consistent
    let final_value1 = entry1.value().unwrap().get();
    let final_value2 = entry2.value().unwrap().get();
    assert_eq!(
        final_value1, final_value2,
        "both entries should have the same final value"
    );

    // Both entries should be marked as dirty
    assert!(entry1.dirty());
    assert!(entry2.dirty());

    // At least one entry should have proxyFor set (the one that lost the race)
    let has_proxy = entry1.proxy_for().is_some() || entry2.proxy_for().is_some();
    assert!(has_proxy, "at least one entry should have proxyFor set");

    // If entry1 has a proxy, it should point to entry2, and vice versa
    if let Some(proxy) = entry1.proxy_for() {
        assert!(
            proxy.ptr_eq(&entry2),
            "entry1 should proxy to entry2"
        );
    }
    if let Some(proxy) = entry2.proxy_for() {
        assert!(
            proxy.ptr_eq(&entry1),
            "entry2 should proxy to entry1"
        );
    }
}

// `proxy operations delegation`
#[test]
fn sync_map_proxy_delegation() {
    let base = new_base(&[("key1", "original")]);
    let sync_map = SyncMap::new(Some(base));

    // Load two entries for the same key
    let entry1 = sync_map.load(&"key1".to_owned()).unwrap();
    let entry2 = sync_map.load(&"key1".to_owned()).unwrap();

    // Force one to become a proxy by making them both dirty in sequence
    entry1.change(|v| v.set("changed_by_entry1"));
    entry2.change(|v| v.set("changed_by_entry2"));

    // Determine which is the proxy and which is the target
    let (proxy, target) = if entry1.proxy_for().is_some() {
        (entry1, entry2)
    } else {
        (entry2, entry1)
    };

    // Test that proxy operations are delegated to the target
    // Change through proxy should affect target
    proxy.change(|v| v.set("changed_through_proxy"));
    assert_eq!("changed_through_proxy", target.value().unwrap().get());
    assert_eq!("changed_through_proxy", proxy.value().unwrap().get());

    // ChangeIf through proxy should work
    let changed = proxy.change_if(
        |v| v.is_some_and(|v| v.get() == "changed_through_proxy"),
        |v| v.set("conditional_change"),
    );
    assert!(changed);
    assert_eq!("conditional_change", target.value().unwrap().get());
    assert_eq!("conditional_change", proxy.value().unwrap().get());

    // Dirty status should be consistent
    assert_eq!(target.dirty(), proxy.dirty());

    // Locked operations should work through proxy
    proxy.locked(|v| {
        v.change(&mut |val| val.set("locked_change"));
    });
    assert_eq!("locked_change", target.value().unwrap().get());
    assert_eq!("locked_change", proxy.value().unwrap().get());
}

// `proxy delete operations`
#[test]
fn sync_map_proxy_delete() {
    let base = new_base(&[("key1", "original")]);
    let sync_map = SyncMap::new(Some(base));

    // Load two entries and make one a proxy
    let entry1 = sync_map.load(&"key1".to_owned()).unwrap();
    let entry2 = sync_map.load(&"key1".to_owned()).unwrap();

    entry1.change(|v| v.set("modified"));
    entry2.change(|v| v.set("modified2"));

    // Determine which is the proxy
    let proxy = if entry1.proxy_for().is_some() {
        entry1
    } else {
        entry2
    };

    // Delete through proxy should affect target
    proxy.delete();

    // Both should reflect the deletion
    let exists = sync_map.load(&"key1".to_owned()).is_some();
    assert!(!exists, "key should be deleted from sync map");

    // DeleteIf through proxy should work
    let base2 = new_base(&[("key2", "test")]);
    let sync_map2 = SyncMap::new(Some(base2));

    let entry3 = sync_map2.load(&"key2".to_owned()).unwrap();
    let entry4 = sync_map2.load(&"key2".to_owned()).unwrap();

    entry3.change(|v| v.set("modified"));
    entry4.change(|v| v.set("modified2"));

    let proxy2 = if entry3.proxy_for().is_some() {
        entry3
    } else {
        entry4
    };

    proxy2.delete_if(|v| {
        v.is_some_and(|v| v.get() == "modified2" || v.get() == "modified")
    });

    let exists2 = sync_map2.load(&"key2".to_owned()).is_some();
    assert!(!exists2, "key2 should be deleted conditionally");
}

// `no proxy when no race`
#[test]
fn sync_map_no_proxy_without_race() {
    let base = new_base(&[("key1", "original")]);
    let sync_map = SyncMap::new(Some(base));

    // Load and modify a single entry - no race condition
    let entry = sync_map.load(&"key1".to_owned()).unwrap();

    entry.change(|v| v.set("changed"));

    // Should not have a proxy since there was no race
    assert!(
        entry.proxy_for().is_none(),
        "entry should not have proxyFor when no race occurs"
    );
    assert!(entry.dirty());
    assert_eq!("changed", entry.value().unwrap().get());
}
