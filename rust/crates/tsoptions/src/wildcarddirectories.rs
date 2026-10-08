// Ported from tsc/internal/tsoptions/wildcarddirectories.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;

use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RootedDirectoryPath};
use tsc_vfs::vfsmatch;

/// `wildcardDirectoryMatch` — the result of a wildcard directory match.
pub(crate) struct WildcardDirectoryMatch {
    pub path: RootedDirectoryPath,
    pub recursive: bool,
}

/// `getWildcardDirectories` — Go takes `[]T` where `T` is a
/// `PathPatternInput`; the Rust matcher takes `&[PathPattern]`/equivalents,
/// so callers pass string slices of specs.
///
/// Returns `None` when `include` is empty (Go's nil map), otherwise the
/// directory → recursive-watched map. PORT: Go's `map` iteration order is
//  unspecified; a `HashMap` is used identically here.
pub fn get_wildcard_directories(
    include: &[tspath::PathPattern],
    exclude: &[tspath::PathPattern],
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> Option<HashMap<RootedDirectoryPath, bool>> {
    // We watch a directory recursively if it contains a wildcard anywhere in a directory segment
    // of the pattern:
    //
    //  /a/b/**/d   - Watch /a/b recursively to catch changes to any d in any subfolder recursively
    //  /a/b/*/d    - Watch /a/b recursively to catch any d in any immediate subfolder, even if a new subfolder is added
    //  /a/b        - Watch /a/b recursively to catch changes to anything in any recursive subfoler
    //
    // We watch a directory without recursion if it contains a wildcard in the file segment of
    // the pattern:
    //
    //  /a/b/*      - Watch /a/b directly to catch any new file
    //  /a/b/a?z    - Watch /a/b directly to catch any new file matching a?z

    if include.is_empty() {
        return None;
    }

    let exclude_matcher = vfsmatch::new_spec_matcher(
        exclude,
        current_directory,
        vfsmatch::USAGE_EXCLUDE,
        case_sensitivity,
    );

    let mut wildcard_directories: HashMap<RootedDirectoryPath, bool> = HashMap::new();
    let mut wild_card_key_to_path: HashMap<PathKey, RootedDirectoryPath> = HashMap::new();

    let mut recursive_keys: Vec<PathKey> = Vec::new();

    for file in include {
        let spec = tspath::normalize_path(&tspath::combine_paths(
            current_directory.as_string(),
            &[file.as_string()],
        ))
        .into_owned();
        if exclude_matcher
            .as_ref()
            .is_some_and(|m| m.match_string(&spec))
        {
            continue;
        }

        if let Some(match_) = get_wildcard_directory_from_spec(&spec) {
            let mut path = match_.path;
            if path.as_string().is_empty() {
                path = tspath::rooted_directory_path_from_normalized(
                    &spec[..tspath::get_root_length(&spec)],
                );
            }
            let key = case_sensitivity.path_key(&path.as_path());
            let recursive = match_.recursive;

            let existing_path = wild_card_key_to_path.get(&key).cloned();
            let existing_recursive = existing_path
                .as_ref()
                .and_then(|p| wildcard_directories.get(p).copied())
                .unwrap_or(false);
            let exists_path = existing_path.is_some();

            if !exists_path || (!existing_recursive && recursive) {
                let path_to_use = existing_path.unwrap_or_else(|| path.clone());
                wildcard_directories.insert(path_to_use, recursive);

                if !exists_path {
                    wild_card_key_to_path.insert(key.clone(), path);
                }

                if recursive {
                    recursive_keys.push(key);
                }
            }
        }

        // Remove any subpaths under an existing recursively watched directory
        let paths: Vec<RootedDirectoryPath> = wildcard_directories.keys().cloned().collect();
        for path in paths {
            for recursive_key in &recursive_keys {
                let key = case_sensitivity.path_key(&path.as_path());
                if key != *recursive_key && recursive_key.contains_path(&key) {
                    wildcard_directories.remove(&path);
                }
            }
        }
    }

    Some(wildcard_directories)
}

/// `getWildcardDirectoryFromSpec` — `None` is Go's nil result.
fn get_wildcard_directory_from_spec(spec: &str) -> Option<WildcardDirectoryMatch> {
    let bytes = spec.as_bytes();
    // Find the first occurrence of a wildcard character
    if let Some(first_wildcard) = bytes.iter().position(|b| *b == b'*' || *b == b'?') {
        // Find the last directory separator before the wildcard
        if let Some(last_sep_before_wildcard) =
            spec[..first_wildcard].rfind(tspath::DIRECTORY_SEPARATOR as char)
        {
            let mut path = RootedDirectoryPath::default();
            let path_text = &spec[..last_sep_before_wildcard];
            if !path_text.is_empty() {
                path = tspath::rooted_directory_path_from_absolute(path_text);
            }
            let last_directory_separator_index =
                spec.rfind(tspath::DIRECTORY_SEPARATOR as char).unwrap_or(0);

            // Determine if this should be watched recursively:
            // recursive if the wildcard appears in a directory segment (not just the final file segment)
            let recursive = first_wildcard < last_directory_separator_index;

            return Some(WildcardDirectoryMatch { path, recursive });
        }
    }

    // `strings.CutLast(spec, "/")`
    if let Some(idx) = spec.rfind(tspath::DIRECTORY_SEPARATOR as char) {
        let last_segment = &spec[idx + 1..];
        if vfsmatch::is_implicit_glob(last_segment) {
            let path = tspath::rooted_directory_path_from_absolute(
                tspath::remove_trailing_directory_separator(spec),
            );
            return Some(WildcardDirectoryMatch {
                path,
                recursive: true,
            });
        }
    }

    None
}
