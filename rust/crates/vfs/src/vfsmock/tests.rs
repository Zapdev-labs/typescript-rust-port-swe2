// Ported from tsc/internal/vfs/vfsmock/wrapper_test.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_tspath::CaseSensitivity;

use super::wrap;
use crate::vfstest;

/// Go's TestWrap uses reflection to assert every exported func field is set
/// by Wrap. In Rust the fields are `Option<Box<dyn Fn>>`; assert each is Some.
#[test]
fn test_wrap() {
    let wrapper = wrap(vfstest::from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseSensitive,
    ));

    assert!(
        wrapper.append_file_func.is_some(),
        "field append_file_func should not be zero; update wrap"
    );
    assert!(
        wrapper.case_sensitivity_func.is_some(),
        "field case_sensitivity_func should not be zero; update wrap"
    );
    assert!(
        wrapper.chtimes_func.is_some(),
        "field chtimes_func should not be zero; update wrap"
    );
    assert!(
        wrapper.directory_exists_func.is_some(),
        "field directory_exists_func should not be zero; update wrap"
    );
    assert!(
        wrapper.file_exists_func.is_some(),
        "field file_exists_func should not be zero; update wrap"
    );
    assert!(
        wrapper.get_accessible_entries_func.is_some(),
        "field get_accessible_entries_func should not be zero; update wrap"
    );
    assert!(
        wrapper.read_file_func.is_some(),
        "field read_file_func should not be zero; update wrap"
    );
    assert!(
        wrapper.realpath_func.is_some(),
        "field realpath_func should not be zero; update wrap"
    );
    assert!(
        wrapper.remove_func.is_some(),
        "field remove_func should not be zero; update wrap"
    );
    assert!(
        wrapper.stat_func.is_some(),
        "field stat_func should not be zero; update wrap"
    );
    assert!(
        wrapper.write_file_func.is_some(),
        "field write_file_func should not be zero; update wrap"
    );
}
