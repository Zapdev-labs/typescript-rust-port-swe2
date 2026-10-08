// Ported from tsc/internal/repo/paths.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::path::Path;
use std::sync::OnceLock;

static ROOT_PATH: OnceLock<String> = OnceLock::new();

fn root_path_init() -> String {
    // PORT: Go uses runtime.Caller(0) to get this file's path, which is
    // tsc/internal/repo/paths.go. The Rust analog is CARGO_MANIFEST_DIR — the
    // directory containing this crate's Cargo.toml — which is also absolute
    // and lies inside the repo (rust/crates/repo).
    let filename = env!("CARGO_MANIFEST_DIR");

    // PORT: Go's `strings.HasPrefix(filename, "github.com/")` -trimpath check
    // has no analog here; cargo only makes CARGO_MANIFEST_DIR non-absolute
    // under path remapping, which the next check catches.
    if !Path::new(filename).is_absolute() {
        panic!("{filename} is not an absolute path");
    }

    // PORT: the Go walk looks for go.mod in ancestors of the source file,
    // finding tsc/go.mod. This crate lives in rust/crates/repo, not inside
    // tsc/, so each ancestor is checked for a tsc/go.mod entry — the found
    // tsc directory is the same module root Go returns.
    let mut dir = Path::new(filename);
    loop {
        let candidate = dir.join("tsc").join("go.mod");
        if candidate.is_file() {
            return dir
                .join("tsc")
                .into_os_string()
                .into_string()
                // PORT: Go paths are arbitrary bytes; Rust String is UTF-8.
                .unwrap_or_else(|_| panic!("repo root path is not valid UTF-8"));
        }
        match dir.parent() {
            Some(parent) => dir = parent,
            None => panic!("could not find go.mod above {filename}"),
        }
    }
}

pub fn root_path() -> &'static str {
    ROOT_PATH.get_or_init(root_path_init)
}

static TEST_DATA_PATH: OnceLock<String> = OnceLock::new();

fn test_data_path_init() -> String {
    // filepath.Join(rootPath(), "testdata")
    Path::new(root_path())
        .join("testdata")
        .into_os_string()
        .into_string()
        .unwrap_or_else(|_| panic!("testdata path is not valid UTF-8"))
}

pub fn test_data_path() -> &'static str {
    TEST_DATA_PATH.get_or_init(test_data_path_init)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn test_root_path() {
        let root = root_path();
        assert!(Path::new(root).is_absolute());
        assert!(Path::new(root).join("go.mod").is_file());
        assert!(root.ends_with("tsc"));
    }

    #[test]
    fn test_test_data_path() {
        let path = test_data_path();
        assert_eq!(path, format!("{}/testdata", root_path()));
        assert!(Path::new(path).is_dir());
    }
}
