// Ported from tsc/internal/vfs/internal/internal.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_tspath::{RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{self, DirEntry, FileInfo, FileMode, Fs, MODE_IRREGULAR, MODE_SYMLINK};
use crate::vfs::Entries;

/// Common holds the shared implementation backing iovfs.ioFS and osvfs.osFS.
///
/// PORT: Go's `RootFor func(root string) fs.FS` may return nil for URL roots
/// handled by [fs::sub] failure; here it returns Option.
#[derive(Clone)]
pub struct Common {
    pub root_for: Arc<dyn Fn(&str) -> Option<Arc<dyn Fs>> + Send + Sync>,
    pub is_reparse_point: Option<Arc<dyn Fn(&str) -> bool + Send + Sync>>,
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

        fn add_to_result(
            result: &mut Entries,
            name: &str,
            mode: FileMode,
            is_link: bool,
        ) -> bool {
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

            if entry_type & MODE_IRREGULAR != FileMode(0) && self.is_reparse_point.is_some() {
                // Could be a Windows junction or other reparse point.
                // Check using the OS-specific helper.
                let name = entry.name();
                let full_path = path.resolve_file(&name);
                if self.is_reparse_point.as_ref().unwrap()(full_path.as_string()) {
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

        match fs::read_dir(&*fsys, &rest) {
            Ok(entries) => entries,
            Err(_) => Vec::new(),
        }
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

    // PORT: Go strings may hold arbitrary bytes; non-UTF-8 contents are
    // decoded lossily here.
    Some(String::from_utf8_lossy(s).into_owned())
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

