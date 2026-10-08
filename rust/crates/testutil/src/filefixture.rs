// Ported from tsc/internal/testutil/filefixture/filefixture.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `testing.TB` is dropped — `SkipIfNotExist` becomes the predicate
// `exists` (caller early-returns), and `ReadFile`'s `tb.Fatalf` becomes
// `read_file` panicking. File contents are `[u8]`, not `String`: Go returns
// `string(file bytes)` and fixture files need not be valid UTF-8.

use std::fmt;
use std::fs;
use std::io;
use std::path::Path;
use std::sync::{Arc, OnceLock};

/// Fixture is a named test file, either backed by a real file on disk
/// (read and cached on first use) or by in-memory contents.
pub trait Fixture: Send + Sync + fmt::Debug {
    /// Name returns the fixture's display name.
    fn name(&self) -> &str;
    /// Path returns the fixture's path (not necessarily an on-disk file).
    fn path(&self) -> &str;
    /// Exists reports whether the fixture's backing file exists.
    ///
    /// Go: `SkipIfNotExist(tb)` — call sites read
    /// `if !fixture.exists() { return; }` instead of `t.Skip`.
    fn exists(&self) -> bool;
    /// TryReadFile returns the fixture contents or the read error.
    fn try_read_file(&self) -> io::Result<&[u8]>;
    /// ReadFile returns the fixture contents, panicking on read error
    /// (Go: `tb.Fatalf`).
    fn read_file(&self) -> &[u8] {
        self.try_read_file()
            .unwrap_or_else(|e| panic!("Failed to read test fixture {:?}: {e}", self.path()))
    }
}

/// fromFile is a fixture backed by a real file; contents and read errors
/// are cached on first read (Go: `sync.OnceValues`).
#[derive(Debug)]
struct FromFile {
    name: String,
    path: String,
    contents: OnceLock<io::Result<Vec<u8>>>,
}

/// FromFile creates a [Fixture] that reads `path` on first use.
pub fn from_file(name: impl Into<String>, path: impl Into<String>) -> Arc<dyn Fixture> {
    Arc::new(FromFile {
        name: name.into(),
        path: path.into(),
        contents: OnceLock::new(),
    })
}

impl Fixture for FromFile {
    fn name(&self) -> &str {
        &self.name
    }

    fn path(&self) -> &str {
        &self.path
    }

    fn exists(&self) -> bool {
        // Go: `os.Stat(f.path)` — any stat error skips the test.
        Path::new(&self.path).try_exists().unwrap_or(false)
    }

    fn try_read_file(&self) -> io::Result<&[u8]> {
        match self.contents.get_or_init(|| fs::read(&self.path)) {
            Ok(contents) => Ok(contents.as_slice()),
            // io::Error is not Clone; rebuild it preserving kind and message.
            Err(e) => Err(io::Error::new(e.kind(), e.to_string())),
        }
    }
}

/// fromString is a fixture backed by in-memory contents.
#[derive(Debug)]
struct FromString {
    name: String,
    path: String,
    contents: Vec<u8>,
}

/// FromString creates a [Fixture] with fixed contents.
pub fn from_string(
    name: impl Into<String>,
    path: impl Into<String>,
    contents: impl Into<Vec<u8>>,
) -> Arc<dyn Fixture> {
    Arc::new(FromString {
        name: name.into(),
        path: path.into(),
        contents: contents.into(),
    })
}

impl Fixture for FromString {
    fn name(&self) -> &str {
        &self.name
    }

    fn path(&self) -> &str {
        &self.path
    }

    fn exists(&self) -> bool {
        // Go: `SkipIfNotExist` is a no-op for string fixtures.
        true
    }

    fn try_read_file(&self) -> io::Result<&[u8]> {
        Ok(&self.contents)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_string_fixture() {
        let f = from_string("empty.ts", "empty.ts", "");
        assert_eq!(f.name(), "empty.ts");
        assert_eq!(f.path(), "empty.ts");
        assert!(f.exists()); // Go: SkipIfNotExist is a no-op
        assert_eq!(f.read_file(), b"");
    }

    #[test]
    fn from_file_fixture_missing() {
        let f = from_file("nope", "/definitely/not/here.ts");
        assert!(!f.exists()); // Go: SkipIfNotExist would t.Skip
        assert!(f.try_read_file().is_err());
    }

    #[test]
    fn from_file_fixture_reads_and_caches() {
        let dir = crate::TempDir::new();
        let path = dir.path().join("f.ts");
        fs::write(&path, b"contents").unwrap();
        let f = from_file("f.ts", path.to_str().unwrap());
        assert!(f.exists());
        assert_eq!(f.read_file(), b"contents");
        // Cached: subsequent reads do not hit disk.
        fs::remove_file(&path).unwrap();
        assert_eq!(f.read_file(), b"contents");
    }
}
