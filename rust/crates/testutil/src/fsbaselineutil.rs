// Ported from tsc/internal/testutil/fsbaselineutil/differ.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `DiffEntry.Content` is `Vec<u8>` and diff payloads are `Vec<u8>` —
// Go strings can hold arbitrary file bytes. `regexp`-free:
// `SanitizeInternalSymbolName`'s `\x{FFFD}@[^@]+@[0-9]+` is implemented as a
// byte scan (the whole pattern is ASCII-anchored, and `[^@]`/`[0-9]` are
// byte-exact), matching RE2's leftmost-first, non-overlapping semantics.
// `d.MapFs()` becomes [FsDiffer::with_map_fs] since the `Arc<dyn Fs>`
// downcast can't outlive its temporary borrow. `*d.WrittenFiles =
// collections.SyncSet{}` becomes `SyncSet::clear` — the Go reset mutates
// the shared set in place, and so does clear.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::io;
use std::sync::Arc;
use std::time::SystemTime;

use tsc_collections::SyncSet;
use tsc_tspath::{
    RootedFilePath, RootedPath, rooted_file_path_from_normalized, rooted_path_from_normalized,
};
use tsc_vfs::fs::{FileMode, MODE_SYMLINK};
use tsc_vfs::{Vfs, vfstest};

/// DiffEntry describes a file or symlink in a filesystem snapshot.
#[derive(Clone, Debug)]
pub struct DiffEntry {
    pub content: Vec<u8>,
    pub mtime: SystemTime,
    pub is_written: bool,
    pub symlink_target: String,
}

/// Snapshot is a serialized filesystem state for diffing.
/// (No Debug: `SyncSet` doesn't implement it.)
pub struct Snapshot {
    pub snap: BTreeMap<String, DiffEntry>,
    pub default_libs: SyncSet<RootedPath>,
}

/// DefaultLibsFn is `func() *collections.SyncSet[tspath.RootedPath]` — a
/// nil function is `None` on the field; a nil *SyncSet return is `None`
/// inside.
pub type DefaultLibsFn = Box<dyn Fn() -> Option<Arc<SyncSet<RootedPath>>> + Send + Sync>;

/// FSDiffer tracks a test filesystem against a serialized snapshot and
/// emits baseline diffs.
pub struct FsDiffer {
    /// Go: `FS iovfs.FsWithSys`. The port takes the unasserted `Arc<dyn Vfs>`
    /// (what callers like `sys.fs.FS` hold) and applies the
    /// `.(iovfs.FsWithSys)` assertion lazily via `as_fs_with_sys`.
    pub fs: Arc<dyn Vfs>,
    /// Go: `DefaultLibs func() *collections.SyncSet[tspath.RootedPath]`.
    pub default_libs: Option<DefaultLibsFn>,
    pub written_files: Arc<SyncSet<RootedFilePath>>,

    serialized_diff: Option<Snapshot>,
}

impl FsDiffer {
    /// SerializedDiff returns the last snapshot produced by [FsDiffer::baseline_fs_with_diff].
    pub fn serialized_diff(&self) -> Option<&Snapshot> {
        self.serialized_diff.as_ref()
    }

    /// The `fs.(iovfs.FsWithSys)` assertion — panics like Go's type
    /// assertion if the fs does not implement it.
    fn fs_with_sys(&self) -> &dyn tsc_vfs::iovfs::FsWithSys {
        self.fs
            .as_fs_with_sys()
            .expect("FSDiffer.FS is not an iovfs.FsWithSys")
    }

    /// MapFs is Go's `d.FS.FSys().(*vfstest.MapFS)` — panics if the
    /// underlying fs is not a vfstest MapFs.
    ///
    /// PORT: the downcast reference borrows the temporary `Arc<dyn Fs>`
    /// from `fsys()`, so callers get a closure instead of the reference.
    pub fn with_map_fs<R>(&self, f: impl FnOnce(&vfstest::MapFs) -> R) -> R {
        let fsys = self.fs_with_sys().fsys();
        let map_fs = fsys
            .as_any()
            .downcast_ref::<vfstest::MapFs>()
            .expect("FSDiffer.FS.FSys() is not a vfstest.MapFs");
        f(map_fs)
    }

    fn current_default_libs(&self) -> Option<Arc<SyncSet<RootedPath>>> {
        self.default_libs.as_ref().and_then(|f| f())
    }

    /// BaselineFSwithDiff writes a baseline diff of filesystem changes
    /// since the previous call, then snapshots the current state.
    ///
    /// todo: baselines the entire fs, possibly doesn't correctly diff all
    /// cases of emitted files, since emit isn't fully implemented and
    /// doesn't always emit the same way as strada
    ///
    /// PORT: Go ignores `fmt.Fprint` errors on the baseline writer; the port
    /// does the same.
    pub fn baseline_fs_with_diff(&mut self, baseline: &mut dyn io::Write) {
        let fsys = self.fs_with_sys().fsys();
        let map_fs = fsys
            .as_any()
            .downcast_ref::<vfstest::MapFs>()
            .expect("FSDiffer.FS.FSys() is not a vfstest.MapFs");

        let mut snap: BTreeMap<String, DiffEntry> = BTreeMap::new();

        // Go: `diffs map[string]string` sorted at output — BTreeMap is
        // byte-lexicographic like `slices.Sort(maps.Keys(diffs))`.
        let mut diffs: BTreeMap<String, Vec<u8>> = BTreeMap::new();

        for (path, file) in map_fs.entries() {
            if file.mode & MODE_SYMLINK != FileMode(0) {
                let Some(target) = map_fs.get_target_of_symlink(&path) else {
                    panic!("Failed to resolve symlink target: {path}");
                };
                let new_entry = DiffEntry {
                    content: Vec::new(),
                    mtime: file.mod_time,
                    is_written: false,
                    symlink_target: target,
                };
                snap.insert(path.clone(), new_entry.clone());
                self.add_fs_entry_diff(&mut diffs, Some(&new_entry), &path);
            } else if file.mode.is_regular() {
                let content = sanitize_internal_symbol_name(&file.data).into_owned();
                let new_entry = DiffEntry {
                    content,
                    mtime: file.mod_time,
                    is_written: self
                        .written_files
                        .has(&rooted_file_path_from_normalized(&path)),
                    symlink_target: String::new(),
                };
                snap.insert(path.clone(), new_entry.clone());
                self.add_fs_entry_diff(&mut diffs, Some(&new_entry), &path);
            }
        }
        if let Some(serialized_diff) = &self.serialized_diff {
            for path in serialized_diff.snap.keys() {
                if map_fs.get_file_info(path).is_none() {
                    // report deleted
                    self.add_fs_entry_diff(&mut diffs, None, path);
                }
            }
        }
        let default_libs = SyncSet::new();
        if let Some(libs) = self.current_default_libs() {
            libs.range(|lib_path| {
                default_libs.add(lib_path);
                true
            });
        }
        self.serialized_diff = Some(Snapshot { snap, default_libs });
        for (path, diff) in &diffs {
            let _ = baseline.write_all(b"//// [");
            let _ = baseline.write_all(path.as_bytes());
            let _ = baseline.write_all(b"] ");
            let _ = baseline.write_all(diff);
            let _ = baseline.write_all(b"\n");
        }
        let _ = baseline.write_all(b"\n");
        self.written_files.clear(); // Reset written files after baseline
    }

    fn add_fs_entry_diff(
        &self,
        diffs: &mut BTreeMap<String, Vec<u8>>,
        new_dir_content: Option<&DiffEntry>,
        path: &str,
    ) {
        let (old_dir_content, default_libs) = match &self.serialized_diff {
            Some(serialized_diff) => (
                serialized_diff.snap.get(path),
                Some(&serialized_diff.default_libs),
            ),
            None => (None, None),
        };
        let rooted_path = rooted_path_from_normalized(path);
        // todo handle more cases of fs changes
        let Some(old_dir_content) = old_dir_content else {
            let libs = self.current_default_libs();
            if libs.as_ref().is_none_or(|libs| !libs.has(&rooted_path)) {
                let new_dir_content =
                    new_dir_content.expect("addFsEntryDiff: new entry missing for unrecorded path");
                if !new_dir_content.symlink_target.is_empty() {
                    diffs.insert(
                        path.to_string(),
                        format!("-> {} *new*", new_dir_content.symlink_target).into_bytes(),
                    );
                } else {
                    let mut diff = b"*new* \n".to_vec();
                    diff.extend_from_slice(&new_dir_content.content);
                    diffs.insert(path.to_string(), diff);
                }
            }
            return;
        };
        match new_dir_content {
            None => {
                diffs.insert(path.to_string(), b"*deleted*".to_vec());
            }
            Some(new_dir_content) if new_dir_content.content != old_dir_content.content => {
                let mut diff = b"*modified* \n".to_vec();
                diff.extend_from_slice(&new_dir_content.content);
                diffs.insert(path.to_string(), diff);
            }
            Some(new_dir_content) if new_dir_content.is_written => {
                diffs.insert(path.to_string(), b"*rewrite with same content*".to_vec());
            }
            Some(new_dir_content) if new_dir_content.mtime != old_dir_content.mtime => {
                diffs.insert(path.to_string(), b"*mTime changed*".to_vec());
            }
            Some(new_dir_content) => {
                let libs = self.current_default_libs();
                if default_libs.is_some_and(|d| d.has(&rooted_path))
                    && libs.as_ref().is_some_and(|libs| !libs.has(&rooted_path))
                {
                    // Lib file that was read
                    let mut diff = b"*Lib*\n".to_vec();
                    diff.extend_from_slice(&new_dir_content.content);
                    diffs.insert(path.to_string(), diff);
                }
            }
        }
    }

    /// ChangedPaths returns the filesystem changes detected between the
    /// last snapshot and the current filesystem state.
    pub fn changed_paths(&self) -> Vec<FileChange> {
        let Some(old_snap) = &self.serialized_diff else {
            return Vec::new();
        };
        self.with_map_fs(|map_fs| {
            let mut changes = Vec::new();

            // Check current files against previous snapshot.
            for (path, file) in map_fs.entries() {
                if file.mode & MODE_SYMLINK != FileMode(0) || !file.mode.is_regular() {
                    continue;
                }
                match old_snap.snap.get(&path) {
                    None => {
                        // New file.
                        changes.push(FileChange {
                            path,
                            deleted: false,
                        });
                    }
                    Some(old)
                        if file.data.as_ref() != old.content.as_slice()
                            || file.mod_time != old.mtime =>
                    {
                        // Modified or touched file.
                        changes.push(FileChange {
                            path,
                            deleted: false,
                        });
                    }
                    _ => {}
                }
            }

            // Check for deleted files.
            for path in old_snap.snap.keys() {
                if map_fs.get_file_info(path).is_none() {
                    changes.push(FileChange {
                        path: path.clone(),
                        deleted: true,
                    });
                }
            }

            changes
        })
    }
}

/// FileChange represents a filesystem change detected between snapshots.
#[derive(Clone, Debug)]
pub struct FileChange {
    pub path: String,
    pub deleted: bool,
}

/// `\x{FFFD}@` — the U+FFFD replacement character in UTF-8 followed by '@',
/// the internal symbol name prefix.
const FFFD_AT: &[u8] = &[0xEF, 0xBF, 0xBD, b'@'];

/// SanitizeInternalSymbolName replaces internal symbol names of shape
/// \uFFFD@symbolName@123 with \uFFFD@symbolName@<symbolId>
/// to avoid baselining differences in symbol ids, which can change between runs.
///
/// Go: `internalSymbolRegex.ReplaceAllStringFunc` over
/// `\x{FFFD}@[^@]+@[0-9]+`; ported as a byte scan — the pattern is entirely
/// byte-anchored (`[^@]` can't match `@`, `[0-9]` is ASCII), so UTF-8
/// decoding inside `[^@]+` is never ambiguous.
pub fn sanitize_internal_symbol_name(s: &[u8]) -> Cow<'_, [u8]> {
    // strings.Contains(s, "\uFFFD@")
    if !s.windows(FFFD_AT.len()).any(|w| w == FFFD_AT) {
        return Cow::Borrowed(s);
    }
    let mut out = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len() {
        if let Some((match_end, at)) = match_internal_symbol(&s[i..]) {
            // Go: match[:idStart] + "@<symbolId>"
            out.extend_from_slice(&s[i..i + at]);
            out.extend_from_slice(b"@<symbolId>");
            i += match_end;
        } else {
            out.push(s[i]);
            i += 1;
        }
    }
    Cow::Owned(out)
}

/// Matches `\x{FFFD}@[^@]+@[0-9]+` at the start of `s`; on success returns
/// (match length, byte offset of the '@' before the digit run).
fn match_internal_symbol(s: &[u8]) -> Option<(usize, usize)> {
    if !s.starts_with(FFFD_AT) {
        return None;
    }
    // [^@]+
    let mut j = FFFD_AT.len();
    let name_start = j;
    while j < s.len() && s[j] != b'@' {
        j += 1;
    }
    if j == name_start || j == s.len() {
        return None;
    }
    // '@'
    let at = j;
    j += 1;
    // [0-9]+
    let digit_start = j;
    while j < s.len() && s[j].is_ascii_digit() {
        j += 1;
    }
    if j == digit_start {
        return None;
    }
    Some((j, at))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tsc_tspath::CaseSensitivity;

    #[test]
    fn sanitize_replaces_symbol_ids() {
        let s = "a \u{FFFD}@name@123 b";
        assert_eq!(
            sanitize_internal_symbol_name(s.as_bytes()).as_ref(),
            "a \u{FFFD}@name@<symbolId> b".as_bytes()
        );
    }

    #[test]
    fn sanitize_multiple_occurrences() {
        let s = "\u{FFFD}@x@1 \u{FFFD}@y@22";
        assert_eq!(
            sanitize_internal_symbol_name(s.as_bytes()).as_ref(),
            "\u{FFFD}@x@<symbolId> \u{FFFD}@y@<symbolId>".as_bytes()
        );
    }

    #[test]
    fn sanitize_no_match_returns_unchanged() {
        let s = b"plain text".as_slice();
        assert!(matches!(sanitize_internal_symbol_name(s), Cow::Borrowed(_)));
        // \uFFFD@ present but no [^@]+ or no digits -> unchanged bytes.
        let s = "\u{FFFD}@".as_bytes();
        assert_eq!(sanitize_internal_symbol_name(s).as_ref(), s);
        let s = "\u{FFFD}@@1".as_bytes();
        assert_eq!(sanitize_internal_symbol_name(s).as_ref(), s);
        let s = "\u{FFFD}@a@".as_bytes();
        assert_eq!(sanitize_internal_symbol_name(s).as_ref(), s);
        let s = "\u{FFFD}@a@b".as_bytes();
        assert_eq!(sanitize_internal_symbol_name(s).as_ref(), s);
    }

    fn make_differ(files: Vec<(&str, &str)>) -> FsDiffer {
        let fs = vfstest::from_map(files, CaseSensitivity::CaseSensitive);
        FsDiffer {
            fs,
            default_libs: None,
            written_files: Arc::new(SyncSet::new()),
            serialized_diff: None,
        }
    }

    #[test]
    fn baseline_fs_with_diff_new_file() {
        let mut differ = make_differ(vec![("/a/b.ts", "content")]);
        let mut out = Vec::new();
        differ.baseline_fs_with_diff(&mut out);
        assert_eq!(out, b"//// [/a/b.ts] *new* \ncontent\n\n".to_vec());
        // Second call with no changes emits just the trailing newline.
        out.clear();
        differ.baseline_fs_with_diff(&mut out);
        assert_eq!(out, b"\n".to_vec());
    }

    #[test]
    fn baseline_fs_with_diff_modified_and_deleted() {
        let mut differ = make_differ(vec![("/a/b.ts", "content"), ("/a/c.ts", "see")]);
        let mut out = Vec::new();
        differ.baseline_fs_with_diff(&mut out);
        // Modify b.ts, delete c.ts via the vfs.
        differ
            .fs
            .write_file(&rooted_file_path_from_normalized("/a/b.ts"), "new content")
            .unwrap();
        differ
            .fs
            .remove(&rooted_path_from_normalized("/a/c.ts"))
            .unwrap();
        out.clear();
        differ.baseline_fs_with_diff(&mut out);
        assert_eq!(
            out,
            b"//// [/a/b.ts] *modified* \nnew content\n//// [/a/c.ts] *deleted*\n\n".to_vec()
        );
    }

    #[test]
    fn changed_paths_reports_changes() {
        let mut differ = make_differ(vec![("/a/b.ts", "content")]);
        let mut out = Vec::new();
        differ.baseline_fs_with_diff(&mut out);
        assert!(differ.changed_paths().is_empty());
        differ
            .fs
            .write_file(&rooted_file_path_from_normalized("/a/b.ts"), "changed")
            .unwrap();
        let changes = differ.changed_paths();
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].path, "/a/b.ts");
        assert!(!changes[0].deleted);
    }
}
