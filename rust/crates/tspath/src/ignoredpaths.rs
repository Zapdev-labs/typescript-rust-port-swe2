// Ported from tsc/internal/tspath/ignoredpaths.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::pathkey::PathKey;
use crate::rooted_path::{RootedDirectoryPath, RootedPath};

static IGNORED_PATHS: &[&str] = &["/node_modules/.", "/.git", ".#"];

// PORT: Go's private `containsIgnoredPath` helper is renamed with a `_str`
// suffix so the public `ContainsIgnoredPath` keeps its Go name.
pub(crate) fn contains_ignored_path_str(path: &str) -> bool {
    for pattern in IGNORED_PATHS {
        if path.contains(pattern) {
            return true;
        }
    }
    false
}

pub fn contains_ignored_path(path: &RootedPath) -> bool {
    contains_ignored_path_str(path.as_string())
}

pub fn contains_ignored_directory(directory: &RootedDirectoryPath) -> bool {
    contains_ignored_path_str(directory.as_string())
}

pub fn contains_ignored_path_key(path: &PathKey) -> bool {
    contains_ignored_path_str(path.as_string())
}
