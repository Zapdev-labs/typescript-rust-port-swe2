// Ported from tsc/internal/vfs/internal/internal.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_tspath::{RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{self, DirEntry, FileInfo, FileMode, Fs, MODE_IRREGULAR, MODE_SYMLINK};
use crate::vfs::Entries;

/// RootForFn is `RootFor func(root string) fs.FS`; PORT: returns Option since
/// Go may return nil for URL roots handled by [fs::sub] failure.
pub type RootForFn = dyn Fn(&str) -> Option<Arc<dyn Fs>> + Send + Sync;

/// IsReparsePointFn reports whether a path is a Windows reparse point.
pub type IsReparsePointFn = dyn Fn(&str) -> bool + Send + Sync;

/// Common holds the shared implementation backing iovfs.ioFS and osvfs.osFS.
///
/// PORT: Go's `RootFor func(root string) fs.FS` may return nil for URL roots
/// handled by [fs::sub] failure; here it returns Option.
#[derive(Clone)]
pub struct Common {
    pub root_for: Arc<RootForFn>,
    pub is_reparse_point: Option<Arc<IsReparsePointFn>>,
}

pub fn root_length(p: &str) -> usize {
    let l = tsc_tspath::get_encoded_root_length(p);
    if l == 0 {
        panic!("vfs: path {} is not absolute", fs::go_quote(p));
    } else if l < 0 {
        return (!l) as usize;
    }
    l as usize
}

pub fn split_path(p: &str) -> (String, String) {
    let p = tsc_tspath::normalize_path(p);
    let l = root_length(&p);
    let root_name = p[..l].to_string();
    let rest = tsc_tspath::remove_trailing_directory_separator(&p[l..]).to_string();
    (root_name, rest)
}

impl Common {
    pub fn root_and_path(
        &self,
        path: &RootedPath,
    ) -> (Option<Arc<dyn Fs>>, RootedDirectoryPath, String) {
        let _ = root_length(path.as_string());
        let (root, rest) = path.root_and_relative_path();
        let rest = if rest.is_empty() { "." } else { rest };
        let fsys = (self.root_for)(root.as_string());
        (fsys, root, rest.to_string())
    }

    pub fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        let (fsys, _, rest) = self.root_and_path(path);
        let fsys = fsys?;
        fs::stat(&*fsys, &rest).ok()
    }

    pub fn file_exists(&self, path: &RootedFilePath) -> bool {
        match self.stat(&path.as_path()) {
            Some(stat) => !stat.is_dir(),
            None => false,
        }
    }

    pub fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        match self.stat(&path.as_path()) {
            Some(stat) => stat.is_dir(),
            None => false,
        }
    }

    pub fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        let mut result = Entries {
            symlinks: Some(Default::default()),
            ..Default::default()
        };

        fn add_to_result(result: &mut Entries, name: &str, mode: FileMode, is_link: bool) -> bool {
            if mode.is_dir() {
                result.directories.push(name.to_string());
            } else if mode.is_regular() {
                result.files.push(name.to_string());
            } else {
                return false;
            }

            if is_link {
                result
                    .symlinks
                    .as_mut()
                    .expect("symlinks initialized")
                    .insert(name.to_string());
            }
            true
        }

        for entry in self.get_entries(path) {
            let entry_type = entry.type_();

            if add_to_result(&mut result, &entry.name(), entry_type, false) {
                continue;
            }

            if entry_type & MODE_SYMLINK != FileMode(0) {
                // Easy case; UNIX-like system will clearly mark symlinks.
                let name = entry.name();
                if let Some(stat) = self.stat(&path.resolve_file(&name).as_path()) {
                    add_to_result(&mut result, &name, stat.mode(), true);
                }
                continue;
            }

            if entry_type & MODE_IRREGULAR != FileMode(0)
                && let Some(is_reparse_point) = self.is_reparse_point.as_ref()
            {
                // Could be a Windows junction or other reparse point.
                // Check using the OS-specific helper.
                let name = entry.name();
                let full_path = path.resolve_file(&name);
                if is_reparse_point(full_path.as_string()) {
                    if let Some(stat) = self.stat(&full_path.as_path()) {
                        add_to_result(&mut result, &name, stat.mode(), true);
                    }
                }
                continue;
            }
        }

        result
    }

    fn get_entries(&self, path: &RootedDirectoryPath) -> Vec<Arc<dyn DirEntry>> {
        let (fsys, _, rest) = self.root_and_path(&path.as_path());
        let Some(fsys) = fsys else {
            return Vec::new();
        };

        fs::read_dir(&*fsys, &rest).unwrap_or_default()
    }

    pub fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        let (fsys, _, rest) = self.root_and_path(&path.as_path());
        let fsys = fsys?;

        let b = fs::read_file(&*fsys, &rest).ok()?;

        if b.is_empty() {
            return Some(String::new());
        }

        // PORT: Go's unsafe.String zero-copy conversion is not needed since we
        // hold an owned Vec<u8>; decode_bytes works on bytes directly.
        decode_bytes(&b)
    }
}

fn decode_bytes(s: &[u8]) -> Option<String> {
    if s.len() >= 2 {
        match (s[0], s[1]) {
            (0xFF, 0xFE) => return Some(decode_utf16(&s[2..], true)),
            (0xFE, 0xFF) => return Some(decode_utf16(&s[2..], false)),
            _ => {}
        }
    }
    let s = if s.len() >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF {
        &s[3..]
    } else {
        s
    };

    // PORT: Go strings hold arbitrary bytes and preserve them verbatim when
    // the emitter copies source text into its output. Rust `String` must be
    // valid UTF-8, so each byte that fails Go's `utf8.DecodeRune` accept set
    // is mapped to a supplementary-plane private-use marker (U+F0000 + byte).
    // The marker occupies exactly one char per invalid byte — matching Go's
    // one-rune-per-error advance — and `faithful_bytes` reverses the mapping
    // wherever decoded text is written back to bytes.
    Some(decode_utf8_faithful(s))
}

/// `utf8.DecodeRune` accept-set check: valid UTF-8 only — no overlongs,
/// no surrogates, nothing above U+10FFFF. Returns `(char, len)` on success;
/// `None` on any encoding error (Go returns `RuneError` and consumes 1 byte).
fn decode_rune(s: &[u8]) -> Option<(char, usize)> {
    let b0 = *s.first()?;
    if b0 < 0x80 {
        return Some((b0 as char, 1));
    }
    let (len, min, mut cp) = match b0 {
        0xC2..=0xDF => (2usize, 0x80u32, (b0 & 0x1F) as u32),
        0xE0..=0xEF => (3, 0x800, (b0 & 0x0F) as u32),
        0xF0..=0xF4 => (4, 0x10000, (b0 & 0x07) as u32),
        _ => return None,
    };
    if s.len() < len {
        return None;
    }
    for &b in &s[1..len] {
        if !(0x80..=0xBF).contains(&b) {
            return None;
        }
        cp = (cp << 6) | (b & 0x3F) as u32;
    }
    if cp < min || cp > 0x10FFFF || (0xD800..=0xDFFF).contains(&cp) {
        return None;
    }
    char::from_u32(cp).map(|c| (c, len))
}

/// First supplementary private-use plane (U+F0000–U+F00FF marks bytes 0x00–0xFF).
/// No testdata or compiler-generated text uses this range.
pub(crate) const FAITHFUL_MARKER_BASE: u32 = 0xF0000;

/// Decodes `s` as UTF-8 the way Go's scanner sees it: every byte that is not
/// part of a valid UTF-8 sequence becomes `U+F0000 + byte`, a reversible
/// private-use marker, instead of U+FFFD.
pub(crate) fn decode_utf8_faithful(s: &[u8]) -> String {
    if std::str::from_utf8(s).is_ok() {
        // Fast path: no invalid bytes, no markers to produce.
        return String::from_utf8_lossy(s).into_owned();
    }
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < s.len() {
        match decode_rune(&s[i..]) {
            Some((c, len)) => {
                out.push(c);
                i += len;
            }
            None => {
                out.push(
                    char::from_u32(FAITHFUL_MARKER_BASE + s[i] as u32)
                        .expect("marker is a valid char"),
                );
                i += 1;
            }
        }
    }
    out
}

/// Reverses `decode_utf8_faithful` at a byte-sink boundary: marker chars
/// become their original byte; everything else is plain UTF-8. Identical to
/// `s.as_bytes()` when no markers are present (the common case).
pub fn faithful_bytes(s: &str) -> Vec<u8> {
    if !s
        .chars()
        .any(|c| (FAITHFUL_MARKER_BASE..FAITHFUL_MARKER_BASE + 0x100).contains(&(c as u32)))
    {
        return s.as_bytes().to_vec();
    }
    let mut out = Vec::with_capacity(s.len());
    let mut buf = [0u8; 4];
    for c in s.chars() {
        let cp = c as u32;
        if (FAITHFUL_MARKER_BASE..FAITHFUL_MARKER_BASE + 0x100).contains(&cp) {
            out.push((cp - FAITHFUL_MARKER_BASE) as u8);
        } else {
            out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        }
    }
    out
}

fn decode_utf16(s: &[u8], little_endian: bool) -> String {
    let units: Vec<u16> = s[..s.len() / 2 * 2]
        .chunks_exact(2)
        .map(|b| {
            if little_endian {
                u16::from_le_bytes([b[0], b[1]])
            } else {
                u16::from_be_bytes([b[0], b[1]])
            }
        })
        .collect();
    // Go's utf16.Decode replaces unpaired surrogates with U+FFFD, matching
    // String::from_utf16_lossy.
    String::from_utf16_lossy(&units)
}
