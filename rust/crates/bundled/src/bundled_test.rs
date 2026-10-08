// Ported from tsc/internal/bundled/bundled_test.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763
use std::sync::Arc;

use tsc_vfs::osvfs;

use crate::*;

#[test]
fn test_testing_lib_path() {
    let p = testing_lib_path();
    assert!(
        std::fs::metadata(p.as_string()).is_ok(),
        "testing lib path {:?} should exist",
        p.as_string()
    );
    let libdts = p.resolve_file("lib.d.ts");
    assert!(std::fs::metadata(libdts.as_string()).is_ok());
}

#[test]
fn test_embedded_libs() {
    let fs: Arc<dyn tsc_vfs::Vfs> = wrap_fs(osvfs::fs());
    let mut files = fs.get_accessible_entries(&lib_path()).files;
    files.sort();
    assert_eq!(
        files,
        LIB_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>()
    );
}
