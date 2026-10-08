// Ported from tsc/internal/project/logging/logtree_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::logger::Logger;
use crate::logtree::LogTree;

/// `TestLogTreeImplementsLogger` — the Go test is a compile-time interface
/// assertion (`var _ testLogger = &LogTree{}`); the trait bound is the Rust
/// equivalent.
#[test]
fn log_tree_implements_logger() {
    fn assert_logger<T: Logger>(_: &T) {}
    let tree = LogTree::new_log_tree("test".to_owned());
    assert_logger(&tree);
}

/// `TestLogTree` — an empty test in Go; a smoke check that a tree renders.
#[test]
fn log_tree_renders() {
    let tree = LogTree::new_log_tree("test".to_owned());
    tree.log(format_args!("hello"));
    let child = tree.fork("forked");
    child.log(format_args!("child message"));
    let out = tree.to_string();
    assert!(out.contains("======== test ========"));
    assert!(out.contains("hello"));
    assert!(out.contains("child message"));
}
