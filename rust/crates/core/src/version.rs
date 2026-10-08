// Ported from tsc/internal/core/version.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::LazyLock;

// This is a var so it can be overridden by ldflags.
// PORT: Rust has no `-X ldflags` equivalent; the version is a const.
const VERSION: &str = "7.1.0-dev";

pub fn version() -> &'static str {
    VERSION
}

// PORT: Go's package-init `var` becomes a lazily-initialized static.
static VERSION_MAJOR_MINOR: LazyLock<String> = LazyLock::new(|| {
    let mut seen_major = false;
    let i = VERSION.find(|r: char| {
        if r == '.' {
            if seen_major {
                return true;
            }
            seen_major = true;
        }
        false
    });
    match i {
        // strings.IndexFunc returns a byte index.
        None => panic!("invalid version string: {VERSION}"),
        Some(i) => VERSION[..i].to_string(),
    }
});

pub fn version_major_minor() -> &'static str {
    &VERSION_MAJOR_MINOR
}
