// Ported from tsc/internal/tspath/ignoredpaths.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::pathkey::PathKey;
use crate::rooted_path::{RootedDirectoryPath, RootedPath};

static IGNORED_PATHS: &[&str] = &[
    "/node_modules/.",
    "/.git",
    ".#",
];

fn contains_ignored_path(path: &str) -> bool {
    for pattern in IGNORED_PATHS {
        if path.contains(pattern) {
            return true;
        }
    }
    false
}

pub fn contains_ignored_path_rooted(path: &RootedPath) -> bool {
    contains_ignored_path(path.as_string())
}

pub fn contains_ignored_directory(directory: &RootedDirectoryPath) -> bool {
    contains_ignored_path(directory.as_string())
}

pub fn contains_ignored_path_key(path: &PathKey) -> bool {
    contains_ignored_path(path.as_string())
}
