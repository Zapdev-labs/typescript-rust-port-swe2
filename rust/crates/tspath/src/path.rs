// Ported from tsc/internal/tspath/path.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;
use std::fmt;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::dynamic::DYNAMIC_URI_FILE_NAME_PREFIX;
use crate::rooted_path::RootedDirectoryPath;
// PORT(shim): temporary — replace with `use tsc_stringutil as stringutil` once
// tsc-stringutil provides these functions.
use crate::stringutil_shim as stringutil;

// Internally, we represent paths as strings with '/' as the directory separator.
// When we make system calls (eg: LanguageServiceHost.getDirectory()),
// we expect the host to correctly handle paths in our specified format.
pub const DIRECTORY_SEPARATOR: char = '/';
pub(crate) const URL_SCHEME_SEPARATOR: &str = "://";

//// Path Tests

// Determines whether a byte corresponds to `/` or `\`.
pub(crate) fn is_any_directory_separator(char: u8) -> bool {
    char == b'/' || char == b'\\'
}

// Determines whether a path starts with a URL scheme (e.g. starts with `http://`, `ftp://`, `file://`, etc.).
pub fn is_url(path: &str) -> bool {
    get_encoded_root_length(path) < 0
}

// Determines whether a path is an absolute disk path (e.g. starts with `/`, or a dos path
// like `c:`, `c:\` or `c:/`).
pub fn is_rooted_disk_path(path: &str) -> bool {
    get_encoded_root_length(path) > 0
}

// IsDynamicFileName returns true if the file name represents a dynamic/virtual file
// that doesn't exist on disk (e.g., untitled files with paths like "^/untitled/...").
pub fn is_dynamic_file_name(file_name: &str) -> bool {
    file_name.starts_with("^/")
}

// Determines whether a path starts with an absolute path component (i.e. `/`, `c:/`, `file://`, etc.).
//
//	```
//	// POSIX
//	PathIsAbsolute("/path/to/file.ext") === true
//	// DOS
//	PathIsAbsolute("c:/path/to/file.ext") === true
//	// URL
//	PathIsAbsolute("file:///path/to/file.ext") === true
//	// Non-absolute
//	PathIsAbsolute("path/to/file.ext") === false
//	PathIsAbsolute("./path/to/file.ext") === false
//	```
pub fn path_is_absolute(path: &str) -> bool {
    get_encoded_root_length(path) != 0
}

pub fn has_trailing_directory_separator(path: &str) -> bool {
    !path.is_empty() && is_any_directory_separator(path.as_bytes()[path.len() - 1])
}

// Combines paths. If a path is absolute, it replaces any previous path. Relative paths are not simplified.
//
//	```
//	// Non-rooted
//	CombinePaths("path", "to", "file.ext") === "path/to/file.ext"
//	CombinePaths("path", "dir", "..", "to", "file.ext") === "path/dir/../to/file.ext"
//	// POSIX
//	CombinePaths("/path", "to", "file.ext") === "/path/to/file.ext"
//	CombinePaths("/path", "/to", "file.ext") === "/to/file.ext"
//	// DOS
//	CombinePaths("c:/path", "to", "file.ext") === "c:/path/to/file.ext"
//	CombinePaths("c:/path", "c:/to", "file.ext") === "c:/to/file.ext"
//	// URL
//	CombinePaths("file:///path", "to", "file.ext") === "file:///path/to/file.ext"
//	CombinePaths("file:///path", "file:///to", "file.ext") === "file:///to/file.ext"
//	```
pub fn combine_paths(first_path: &str, paths: &[&str]) -> String {
    // TODO (drosen): There is potential for a fast path here.
    // In the case where we find the last absolute path and just path.Join from there.
    let first_path = normalize_slashes(first_path);

    let mut b = String::new();
    let mut size = first_path.len() + paths.len();
    for p in paths {
        size += p.len();
    }
    b.reserve(size);

    b.push_str(&first_path);

    // To provide a way to "set" the path, keep track of the start and then slice.
    // This will waste some memory each time we do it, but saving memory is more common.
    let mut start = 0;

    for &trailing_path in paths {
        if trailing_path.is_empty() {
            continue;
        }
        let trailing_path = normalize_slashes(trailing_path);
        let result_is_empty = b[start..].is_empty();
        let trailing_path_is_rooted = !result_is_empty && get_root_length(&trailing_path) != 0;
        if result_is_empty || trailing_path_is_rooted {
            // `trailing_path` is absolute.
            start = b.len();
            b.push_str(&trailing_path);
        } else {
            if !has_trailing_directory_separator(&b[start..]) {
                b.push(DIRECTORY_SEPARATOR);
            }
            b.push_str(&trailing_path);
        }
    }
    b[start..].to_string()
}

pub fn get_path_components(path: &str) -> Vec<String> {
    let path = normalize_slashes(path);
    path_components(&path, get_root_length(&path))
}

pub(crate) fn resolve_path_components(path: &str, current_directory: &str) -> Vec<String> {
    let path = combine_paths(current_directory, &[path]);
    path_components(&path, get_root_length(&path))
}

pub(crate) fn path_components(path: &str, root_length: usize) -> Vec<String> {
    let root = &path[..root_length];
    let mut rest: Vec<String> = path[root_length..].split('/').map(str::to_string).collect();
    if !rest.is_empty() && rest.last().unwrap().is_empty() {
        rest.pop();
    }
    let mut components = Vec::with_capacity(rest.len() + 1);
    components.push(root.to_string());
    components.extend(rest);
    components
}

pub fn is_volume_character(char: u8) -> bool {
    char.is_ascii_lowercase() || char.is_ascii_uppercase()
}

pub(crate) fn get_file_url_volume_separator_end(url: &str, start: usize) -> Option<usize> {
    let url = url.as_bytes();
    if url.len() <= start {
        return None;
    }
    let ch0 = url[start];
    if ch0 == b':' {
        return Some(start + 1);
    }
    if ch0 == b'%' && url.len() > start + 2 && url[start + 1] == b'3' {
        let ch2 = url[start + 2];
        if ch2 == b'a' || ch2 == b'A' {
            return Some(start + 3);
        }
    }
    None
}

pub fn get_encoded_root_length(path: &str) -> i32 {
    let bytes = path.as_bytes();
    let ln = bytes.len();
    if ln == 0 {
        return 0;
    }
    let ch0 = bytes[0];

    // POSIX or UNC
    if ch0 == b'/' || ch0 == b'\\' {
        if ln == 1 || bytes[1] != ch0 {
            return 1; // POSIX: "/" (or non-normalized "\")
        }

        let offset = 2;
        let p1 = path[offset..].find(ch0 as char);
        match p1 {
            None => return ln as i32, // UNC: "//server" or "\\server"
            Some(p1) => return (p1 + offset + 1) as i32, // UNC: "//server/" or "\\server\"
        }
    }

    // DOS
    if is_volume_character(ch0) && ln > 1 && bytes[1] == b':' {
        if ln == 2 {
            return 2; // DOS: "c:" (but not "c:d")
        }
        let ch2 = bytes[2];
        if ch2 == b'/' || ch2 == b'\\' {
            return 3; // DOS: "c:/" or "c:\"
        }
    }

    // Untitled paths (e.g., "^/untitled/ts-nul-authority/Untitled-1")
    if ch0 == b'^' && ln > 1 && bytes[1] == b'/' {
        if path.starts_with(DYNAMIC_URI_FILE_NAME_PREFIX) {
            let scheme_end = path[DYNAMIC_URI_FILE_NAME_PREFIX.len()..].find('/');
            if let Some(scheme_end) = scheme_end {
                let authority_start = DYNAMIC_URI_FILE_NAME_PREFIX.len() + scheme_end + 1;
                match path[authority_start..].find('/') {
                    Some(authority_end) => return (authority_start + authority_end + 1) as i32,
                    None => return !(ln as i32),
                }
            }
        }
        return 2; // Untitled: "^/"
    }

    // URL
    if let Some(scheme_end) = path.find(URL_SCHEME_SEPARATOR) {
        let authority_start = scheme_end + URL_SCHEME_SEPARATOR.len();
        if let Some(authority_length) = path[authority_start..].find('/') {
            // URL: "file:///", "file://server/", "file://server/path"
            let authority_end = authority_start + authority_length;

            // For local "file" URLs, include the leading DOS volume (if present).
            // Per https://www.ietf.org/rfc/rfc1738.txt, a host of "" or "localhost" is a
            // special case interpreted as "the machine from which the URL is being interpreted".
            let scheme = &path[..scheme_end];
            let authority = &path[authority_start..authority_end];
            if stringutil::equate_string_case_insensitive(scheme, "file")
                && (authority.is_empty() || stringutil::equate_string_case_insensitive(authority, "localhost"))
                && path.len() > authority_end + 2
                && is_volume_character(bytes[authority_end + 1])
            {
                if let Some(volume_separator_end) = get_file_url_volume_separator_end(path, authority_end + 2) {
                    if volume_separator_end == path.len() {
                        // URL: "file:///c:", "file://localhost/c:", "file:///c$3a", "file://localhost/c%3a"
                        // but not "file:///c:d" or "file:///c%3ad"
                        return !(volume_separator_end as i32);
                    }
                    if bytes[volume_separator_end] == b'/' {
                        // URL: "file:///c:/", "file://localhost/c:/", "file:///c%3a/", "file://localhost/c%3a/"
                        return !(volume_separator_end as i32 + 1);
                    }
                }
            }
            return !(authority_end as i32 + 1); // URL: "file://server/", "http://server/"
        }
        return !(ln as i32); // URL: "file://server", "http://server"
    }

    // relative
    0
}

pub fn get_root_length(path: &str) -> usize {
    let root_length = get_encoded_root_length(path);
    if root_length < 0 {
        return (!root_length) as usize;
    }
    root_length as usize
}

pub fn get_directory_path(path: &str) -> Cow<'_, str> {
    match normalize_slashes(path) {
        Cow::Borrowed(s) => Cow::Borrowed(get_directory_path_from_normalized(s)),
        Cow::Owned(s) => Cow::Owned(get_directory_path_from_normalized(&s).to_string()),
    }
}

pub(crate) fn get_directory_path_from_normalized(path: &str) -> &str {
    // If the path provided is itself a root, then return it.
    let root_length = get_root_length(path);
    if root_length == path.len() {
        return path;
    }

    // return the leading portion of the path up to the last (non-terminal) directory separator
    // but not including any trailing directory separator.
    let path = remove_trailing_directory_separator(path);
    &path[..root_length.max(path.rfind('/').map_or(0, |i| i as usize))]
}

pub fn get_path_from_path_components(path_components: &[String]) -> String {
    if path_components.is_empty() {
        return String::new();
    }

    let mut root = String::new();
    if !path_components[0].is_empty() {
        root = ensure_trailing_directory_separator(&path_components[0]).into_owned();
    }

    root + &path_components[1..].join("/")
}

pub fn normalize_slashes(path: &str) -> Cow<'_, str> {
    // strings.ReplaceAll(path, "\\", "/") — returns the original string when
    // there is nothing to replace, hence the Cow.
    if path.contains('\\') {
        Cow::Owned(path.replace('\\', "/"))
    } else {
        Cow::Borrowed(path)
    }
}

pub(crate) fn reduce_path_components(components: &[String]) -> Vec<String> {
    if components.is_empty() {
        return Vec::new();
    }
    let mut reduced = vec![components[0].clone()];
    for component in &components[1..] {
        if component.is_empty() {
            continue;
        }
        if component == "." {
            continue;
        }
        if component == ".." {
            if reduced.len() > 1 {
                if reduced.last().unwrap() != ".." {
                    reduced.pop();
                    continue;
                }
            } else if !reduced[0].is_empty() {
                continue;
            }
        }
        reduced.push(component.clone());
    }
    reduced
}

// Combines and resolves paths. If a path is absolute, it replaces any previous path. Any
// `.` and `..` path components are resolved. Trailing directory separators are preserved.
//
// ```go
// resolvePath("/path", "to", "file.ext") == "path/to/file.ext"
// resolvePath("/path", "to", "file.ext/") == "path/to/file.ext/"
// resolvePath("/path", "dir", "..", "to", "file.ext") == "path/to/file.ext"
// ```
pub fn resolve_path(path: &str, paths: &[&str]) -> String {
    let combined_path = if !paths.is_empty() {
        combine_paths(path, paths)
    } else {
        normalize_slashes(path).into_owned()
    };
    normalize_path(&combined_path).into_owned()
}

pub fn resolve_path_without_trailing_directory_separator(path: &str, paths: &[&str]) -> String {
    let resolved = resolve_path(path, paths);
    if resolved.len() > get_root_length(&resolved) {
        return remove_trailing_directory_separator(&resolved).to_string();
    }
    resolved
}

pub fn get_normalized_path_components(path: &str, current_directory: &str) -> Vec<String> {
    let combined = combine_paths(current_directory, &[path]);
    get_normalized_path_components_from_combined(&combined)
}

pub(crate) fn get_normalized_path_components_from_combined(path: &str) -> Vec<String> {
    let root_length = get_root_length(path);
    // Always include the root component (empty string for relative paths).
    let mut components: Vec<String> = Vec::with_capacity(8);
    components.push(path[..root_length].to_string());

    let bytes = path.as_bytes();
    let mut i = root_length;
    while i < path.len() {
        // Skip directory separators (handles consecutive separators and trailing '/').
        while i < path.len() && bytes[i] == b'/' {
            i += 1;
        }
        if i >= path.len() {
            break;
        }

        let start = i;
        while i < path.len() && bytes[i] != b'/' {
            i += 1;
        }
        let component = &path[start..i];

        if component.is_empty() || component == "." {
            continue;
        }
        if component == ".." {
            if components.len() > 1 {
                if components.last().unwrap() != ".." {
                    components.pop();
                    continue;
                }
            } else if !components[0].is_empty() {
                // If this is an absolute path, we can't go above the root.
                continue;
            }
        }

        components.push(component.to_string());
    }

    components
}

pub fn get_normalized_absolute_path<'a>(
    file_name: &'a str,
    current_directory: &'a RootedDirectoryPath,
) -> Cow<'a, str> {
    let root_length = get_root_length(file_name);
    let file_name: Cow<str> = if root_length == 0 && !current_directory.is_empty() {
        Cow::Owned(combine_paths(current_directory.as_string(), &[file_name]))
    } else {
        // CombinePaths normalizes slashes, so not necessary in other branch
        normalize_slashes(file_name)
    };
    match file_name {
        Cow::Borrowed(s) => get_normalized_absolute_path_from_normalized_slashes(s),
        Cow::Owned(s) => {
            Cow::Owned(get_normalized_absolute_path_from_normalized_slashes(&s).into_owned())
        }
    }
}

pub(crate) fn get_normalized_absolute_path_from_directory<'a>(
    file_name: &'a str,
    current_directory: &'a RootedDirectoryPath,
) -> Cow<'a, str> {
    let root_length = get_root_length(file_name);
    let file_name: Cow<str> = if root_length == 0 && !current_directory.is_empty() {
        if file_name.is_empty() {
            Cow::Borrowed(current_directory.as_string())
        } else {
            Cow::Owned(append_path_to_directory(
                current_directory,
                &normalize_slashes(file_name),
            ))
        }
    } else {
        // CombinePaths normalizes slashes, so not necessary in other branch
        normalize_slashes(file_name)
    };
    match file_name {
        Cow::Borrowed(s) => get_normalized_absolute_path_from_normalized_slashes(s),
        Cow::Owned(s) => {
            Cow::Owned(get_normalized_absolute_path_from_normalized_slashes(&s).into_owned())
        }
    }
}

pub(crate) fn get_normalized_absolute_path_from_normalized_slashes(file_name: &str) -> Cow<'_, str> {
    let root_length = get_root_length(file_name);
    if let Some(simple_normalized) = simple_normalize_path(file_name) {
        let length = simple_normalized.len();
        if length > root_length {
            return match simple_normalized {
                Cow::Borrowed(s) => Cow::Borrowed(remove_trailing_directory_separator(s)),
                Cow::Owned(s) => {
                    Cow::Owned(remove_trailing_directory_separator(&s).to_string())
                }
            };
        }
        if length == root_length && root_length != 0 {
            return match simple_normalized {
                Cow::Borrowed(s) => ensure_trailing_directory_separator(s),
                Cow::Owned(s) => {
                    Cow::Owned(ensure_trailing_directory_separator(&s).into_owned())
                }
            };
        }
        return simple_normalized;
    }

    let length = file_name.len();
    let root = &file_name[..root_length];
    // `normalized` is only initialized once `fileName` is determined to be non-normalized.
    // `changed` is set at the same time.
    let mut changed = false;
    let mut normalized = String::new();
    let mut index = root_length;
    let mut normalized_up_to = index;
    let mut seen_non_dot_dot_segment = root_length != 0;
    let bytes = file_name.as_bytes();
    while index < length {
        // At beginning of segment
        let mut segment_start = index;
        let mut ch = bytes[index];
        while ch == b'/' {
            index += 1;
            if index < length {
                ch = bytes[index];
            } else {
                break;
            }
        }
        if index > segment_start {
            // Seen superfluous separator
            if !changed {
                normalized = file_name[..root_length.max(segment_start - 1)].to_string();
                changed = true;
            }
            if index == length {
                break;
            }
            segment_start = index;
        }
        // Past any superfluous separators
        let segment_end = match file_name[index + 1..].find('/') {
            None => length,
            Some(i) => i + index + 1,
        };
        let segment_length = segment_end - segment_start;
        if segment_length == 1 && bytes[index] == b'.' {
            // "." segment (skip)
            if !changed {
                normalized = file_name[..normalized_up_to].to_string();
                changed = true;
            }
        } else if segment_length == 2 && bytes[index] == b'.' && bytes[index + 1] == b'.' {
            // ".." segment
            if !seen_non_dot_dot_segment {
                if changed {
                    if normalized.len() == root_length {
                        normalized.push_str("..");
                    } else {
                        normalized.push_str("/..");
                    }
                } else {
                    normalized_up_to = index + 2;
                }
            } else if !changed {
                if normalized_up_to >= 1 {
                    normalized = file_name[..root_length
                        .max(file_name[..normalized_up_to - 1].rfind('/').unwrap_or(0))]
                    .to_string();
                } else {
                    normalized = file_name[..normalized_up_to].to_string();
                }
                changed = true;
                seen_non_dot_dot_segment = (normalized.len() != root_length || root_length != 0)
                    && normalized != ".."
                    && !normalized.ends_with("/..");
            } else {
                match normalized.rfind('/') {
                    Some(last_slash) => {
                        normalized.truncate(root_length.max(last_slash));
                    }
                    None => normalized = root.to_string(),
                }
                seen_non_dot_dot_segment = (normalized.len() != root_length || root_length != 0)
                    && normalized != ".."
                    && !normalized.ends_with("/..");
            }
        } else if changed {
            if normalized.len() != root_length {
                normalized.push('/');
            }
            seen_non_dot_dot_segment = true;
            normalized.push_str(&file_name[segment_start..segment_end]);
        } else {
            seen_non_dot_dot_segment = true;
            normalized_up_to = segment_end;
        }
        index = segment_end + 1;
    }
    if changed {
        return Cow::Owned(normalized);
    }
    if length > root_length {
        return Cow::Borrowed(remove_trailing_directory_separators(file_name));
    }
    if length == root_length {
        return ensure_trailing_directory_separator(file_name);
    }
    Cow::Borrowed(file_name)
}

pub(crate) fn simple_normalize_path(path: &str) -> Option<Cow<'_, str>> {
    // Most paths don't require normalization
    if !has_relative_path_segment(path) {
        return Some(Cow::Borrowed(path));
    }
    // Some paths only require cleanup of `/./` or leading `./`
    let simplified: Cow<str> = if path.contains("/./") {
        Cow::Owned(path.replace("/./", "/"))
    } else {
        Cow::Borrowed(path)
    };
    match simplified {
        Cow::Borrowed(s) => {
            let trimmed = s.strip_prefix("./").unwrap_or(s);
            if trimmed != path
                && !has_relative_path_segment(trimmed)
                && !(trimmed != s && trimmed.starts_with('/'))
            {
                // If we trimmed a leading "./" and the path now starts with "/", we changed the meaning
                Some(Cow::Borrowed(trimmed))
            } else {
                None
            }
        }
        Cow::Owned(s) => {
            let trimmed = s.strip_prefix("./").unwrap_or(&s);
            if trimmed != path
                && !has_relative_path_segment(trimmed)
                && !(trimmed != s.as_str() && trimmed.starts_with('/'))
            {
                // If we trimmed a leading "./" and the path now starts with "/", we changed the meaning
                Some(Cow::Owned(trimmed.to_string()))
            } else {
                None
            }
        }
    }
}

// hasRelativePathSegment reports whether p contains ".", "..", "./", "../", "/.", "/..", "//", "/./", or "/../".
pub(crate) fn has_relative_path_segment(p: &str) -> bool {
    let bytes = p.as_bytes();
    let n = p.len();
    if n == 0 {
        return false;
    }

    if p == "." || p == ".." {
        return true;
    }

    // Leading "./" OR "../"
    if bytes[0] == b'.' {
        if n >= 2 && bytes[1] == b'/' {
            return true;
        }
        // Leading "../"
        if n >= 3 && bytes[1] == b'.' && bytes[2] == b'/' {
            return true;
        }
    }
    // Trailing "/." OR "/.."
    if bytes[n - 1] == b'.' {
        if n >= 2 && bytes[n - 2] == b'/' {
            return true;
        }
        if n >= 3 && bytes[n - 2] == b'.' && bytes[n - 3] == b'/' {
            return true;
        }
    }

    // Now look for any `//` or `/./` or `/../`

    let mut prev_slash = false;
    let mut seg_len = 0; // length of current segment since last slash
    let mut dot_count = 0i32; // consecutive dots at start of the current segment; -1 => not only dots

    for &c in bytes.iter() {
        if c == b'/' {
            // "//"
            if prev_slash {
                return true;
            }
            // "/./" or "/../"
            if (seg_len == 1 && dot_count == 1) || (seg_len == 2 && dot_count == 2) {
                return true;
            }
            prev_slash = true;
            seg_len = 0;
            dot_count = 0;
            continue;
        }

        if c == b'.' {
            if dot_count >= 0 {
                dot_count += 1;
            }
        } else {
            dot_count = -1;
        }
        seg_len += 1;
        prev_slash = false;
    }

    // Trailing "/." or "/.."
    (seg_len == 1 && dot_count == 1) || (seg_len == 2 && dot_count == 2)
}

pub fn normalize_path(path: &str) -> Cow<'_, str> {
    let path = normalize_slashes(path);
    let had_trailing = has_trailing_directory_separator(&path);
    let normalized: Cow<str> = match path {
        Cow::Borrowed(s) => get_normalized_absolute_path_from_normalized_slashes(s),
        Cow::Owned(s) => {
            Cow::Owned(get_normalized_absolute_path_from_normalized_slashes(&s).into_owned())
        }
    };
    if !normalized.is_empty() && had_trailing {
        return match normalized {
            Cow::Borrowed(s) => ensure_trailing_directory_separator(s),
            Cow::Owned(s) => Cow::Owned(ensure_trailing_directory_separator(&s).into_owned()),
        };
    }
    normalized
}

// trimRuneCount returns the suffix of s after skipping up to runeCount runes,
// clamping to the end of s if it has fewer runes than runeCount.
pub(crate) fn trim_rune_count(s: &str, rune_count: usize) -> &str {
    let mut i = 0;
    for _ in 0..rune_count {
        if i >= s.len() {
            break;
        }
        // utf8.DecodeRuneInString — s is valid UTF-8 so the size is the char width.
        i += s[i..].chars().next().unwrap().len_utf8();
    }
    &s[i..]
}

// We convert the file names to lower case as key for file name on case insensitive file system
// While doing so we need to handle special characters (eg \u0130) to ensure that we dont convert
// it to lower case, fileName with its lowercase form can exist along side it.
// Handle special characters and make those case sensitive instead
//
// |-#--|-Unicode--|-Char code-|-Desc-------------------------------------------------------------------|
// | 1. | i        | 105       | Ascii i                                                                |
// | 2. | I        | 73        | Ascii I                                                                |
// |-------- Special characters ------------------------------------------------------------------------|
// | 3. | \u0130   | 304       | Upper case I with dot above                                            |
// | 4. | i,\u0307 | 105,775   | i, followed by 775: Lower case of (3rd item)                           |
// | 5. | I,\u0307 | 73,775    | I, followed by 775: Upper case of (4th item), lower case is (4th item) |
// | 6. | \u0131   | 305       | Lower case i without dot, upper case is I (2nd item)                   |
// | 7. | \u00DF   | 223       | Lower case sharp s                                                     |
//
// Because item 3 is special where in its lowercase character has its own
// upper case form we cant convert its case.
// Rest special characters are either already in lower case format or
// they have corresponding upper case character so they dont need special handling
pub fn to_file_name_lower_case(file_name: &str) -> Cow<'_, str> {
    const I_WITH_DOT: char = '\u{0130}';

    let mut ascii = true;
    let mut needs_lower = false;
    for &c in file_name.as_bytes() {
        if c >= 0x80 {
            ascii = false;
            break;
        }
        if c.is_ascii_uppercase() {
            needs_lower = true;
        }
    }
    if ascii {
        if !needs_lower {
            return Cow::Borrowed(file_name);
        }
        // PORT: Go builds the byte buffer by hand and aliases it via
        // unsafe.String; str::to_ascii_lowercase is the same transformation
        // ('A'..'Z' -> 'a'..'z', all other bytes untouched) without unsafe.
        return Cow::Owned(file_name.to_ascii_lowercase());
    }

    Cow::Owned(
        file_name
            .chars()
            .map(|r| {
                if r == I_WITH_DOT {
                    return r;
                }
                stringutil::go_to_lower(r)
            })
            .collect(),
    )
}

pub fn remove_trailing_directory_separator(path: &str) -> &str {
    if has_trailing_directory_separator(path) {
        return &path[..path.len() - 1];
    }
    path
}

pub(crate) fn remove_trailing_directory_separators(path: &str) -> &str {
    let mut path = path;
    while has_trailing_directory_separator(path) {
        path = remove_trailing_directory_separator(path);
    }
    path
}

pub fn ensure_trailing_directory_separator(path: &str) -> Cow<'_, str> {
    if !has_trailing_directory_separator(path) {
        return Cow::Owned(format!("{path}/"));
    }

    Cow::Borrowed(path)
}

//// Relative Paths

pub fn get_path_components_relative_to(
    from: &str,
    to: &str,
    case_sensitivity: CaseSensitivity,
) -> Vec<String> {
    get_path_components_relative_to_worker(
        &reduce_path_components(&get_path_components(from)),
        &reduce_path_components(&get_path_components(to)),
        case_sensitivity,
    )
}

pub(crate) fn resolve_path_components_relative_to(
    from: &str,
    to: &str,
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> Vec<String> {
    get_path_components_relative_to_worker(
        &reduce_path_components(&resolve_path_components(from, current_directory.as_string())),
        &reduce_path_components(&resolve_path_components(to, current_directory.as_string())),
        case_sensitivity,
    )
}

// PORT: named `get_path_components_relative_to_worker` to avoid colliding with
// the public `get_path_components_relative_to`; the Go original is
// `getPathComponentsRelativeTo` taking component slices directly.
fn get_path_components_relative_to_worker(
    from_components: &[String],
    to_components: &[String],
    case_sensitivity: CaseSensitivity,
) -> Vec<String> {
    let mut start = 0;
    let max_common_components = from_components.len().min(to_components.len());
    let string_equaler = case_sensitivity.get_equality_comparer();
    while start < max_common_components {
        let from_component = &from_components[start];
        let to_component = &to_components[start];
        if start == 0 {
            if !stringutil::equate_string_case_insensitive(from_component, to_component) {
                break;
            }
        } else if !string_equaler(from_component, to_component) {
            break;
        }
        start += 1;
    }

    if start == 0 {
        return to_components.to_vec();
    }

    let num_dot_dot_slashes = from_components.len() - start;
    let mut result = vec![String::new(); 1 + num_dot_dot_slashes + to_components.len() - start];

    let mut i = 1;
    // Add all the relative components until we hit a common directory.
    for _ in 0..num_dot_dot_slashes {
        result[i] = "..".to_string();
        i += 1;
    }
    // Now add all the remaining components of the "to" path.
    for component in &to_components[start..] {
        result[i] = component.clone();
        i += 1;
    }

    result
}

pub fn get_relative_path_from_directory(
    from_directory: &str,
    to: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    if (get_root_length(from_directory) > 0) != (get_root_length(to) > 0) {
        panic!("paths must either both be absolute or both be relative");
    }
    let path_components = get_path_components_relative_to(from_directory, to, case_sensitivity);
    get_path_from_path_components(&path_components)
}

pub fn resolve_relative_path_from_directory(
    from_directory: &str,
    to: &str,
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> String {
    if (get_root_length(from_directory) > 0) != (get_root_length(to) > 0) {
        panic!("paths must either both be absolute or both be relative");
    }
    let path_components =
        resolve_path_components_relative_to(from_directory, to, current_directory, case_sensitivity);
    get_path_from_path_components(&path_components)
}

pub fn get_relative_path_from_file(from: &str, to: &str, case_sensitivity: CaseSensitivity) -> String {
    ensure_path_is_non_module_name(&get_relative_path_from_directory(
        &get_directory_path(from),
        to,
        case_sensitivity,
    ))
    .into_owned()
}

pub fn convert_to_relative_path(
    absolute_or_relative_path: &str,
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> String {
    if !is_rooted_disk_path(absolute_or_relative_path) {
        return absolute_or_relative_path.to_string();
    }

    resolve_relative_path_to_directory_or_url(
        current_directory.as_string(),
        absolute_or_relative_path,
        false, // isAbsolutePathAnUrl
        current_directory,
        case_sensitivity,
    )
}

pub fn get_relative_path_to_directory_or_url(
    directory_path_or_url: &str,
    relative_or_absolute_path: &str,
    is_absolute_path_an_url: bool,
    case_sensitivity: CaseSensitivity,
) -> String {
    let path_components = get_path_components_relative_to(
        directory_path_or_url,
        relative_or_absolute_path,
        case_sensitivity,
    );
    get_relative_path_to_directory_or_url_worker(path_components, is_absolute_path_an_url)
}

pub fn resolve_relative_path_to_directory_or_url(
    directory_path_or_url: &str,
    relative_or_absolute_path: &str,
    is_absolute_path_an_url: bool,
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> String {
    let path_components = resolve_path_components_relative_to(
        directory_path_or_url,
        relative_or_absolute_path,
        current_directory,
        case_sensitivity,
    );
    get_relative_path_to_directory_or_url_worker(path_components, is_absolute_path_an_url)
}

// PORT: named `get_relative_path_to_directory_or_url_worker`; the Go original
// is `getRelativePathToDirectoryOrUrl` taking the already-computed components.
fn get_relative_path_to_directory_or_url_worker(
    mut path_components: Vec<String>,
    is_absolute_path_an_url: bool,
) -> String {
    let first_component = &path_components[0];
    if is_absolute_path_an_url && is_rooted_disk_path(first_component) {
        let prefix;
        if first_component.as_bytes()[0] == DIRECTORY_SEPARATOR as u8 {
            prefix = "file://";
        } else {
            prefix = "file:///";
        }
        path_components[0] = format!("{prefix}{first_component}");
    }

    get_path_from_path_components(&path_components)
}

// Gets the portion of a path following the last (non-terminal) separator (`/`).
// Semantics align with NodeJS's `path.basename` except that we support URL's as well.
// If the base name has any one of the provided extensions, it is removed.
//
//	// POSIX
//	GetBaseFileName("/path/to/file.ext") == "file.ext"
//	GetBaseFileName("/path/to/") == "to"
//	GetBaseFileName("/") == ""
//	// DOS
//	GetBaseFileName("c:/path/to/file.ext") == "file.ext"
//	GetBaseFileName("c:/path/to/") == "to"
//	GetBaseFileName("c:/") == ""
//	GetBaseFileName("c:") == ""
//	// URL
//	GetBaseFileName("http://typescriptlang.org/path/to/file.ext") == "file.ext"
//	GetBaseFileName("http://typescriptlang.org/path/to/") == "to"
//	GetBaseFileName("http://typescriptlang.org/") == ""
//	GetBaseFileName("http://typescriptlang.org") == ""
//	GetBaseFileName("file://server/path/to/file.ext") == "file.ext"
//	GetBaseFileName("file://server/path/to/") == "to"
//	GetBaseFileName("file://server/") == ""
//	GetBaseFileName("file://server") == ""
//	GetBaseFileName("file:///path/to/file.ext") == "file.ext"
//	GetBaseFileName("file:///path/to/") == "to"
//	GetBaseFileName("file:///") == ""
//	GetBaseFileName("file://") == ""
pub fn get_base_file_name(path: &str) -> Cow<'_, str> {
    match normalize_slashes(path) {
        Cow::Borrowed(s) => Cow::Borrowed(get_base_file_name_from_normalized(s)),
        Cow::Owned(s) => Cow::Owned(get_base_file_name_from_normalized(&s).to_string()),
    }
}

pub(crate) fn get_base_file_name_from_normalized(path: &str) -> &str {
    // if the path provided is itself the root, then it has no file name.
    let root_length = get_root_length(path);
    if root_length == path.len() {
        return "";
    }

    // return the trailing portion of the path starting after the last (non-terminal) directory
    // separator but not including any trailing directory separator.
    let path = remove_trailing_directory_separator(path);
    &path[root_length.max(path.rfind(DIRECTORY_SEPARATOR).map_or(0, |i| i + 1))..]
}

// Gets the file extension for a path.
// If extensions are provided, gets the file extension for a path, provided it is one of the provided extensions.
//
//	GetAnyExtensionFromPath("/path/to/file.ext", nil, CaseSensitive) == ".ext"
//	GetAnyExtensionFromPath("/path/to/file.ext/", nil, CaseSensitive) == ".ext"
//	GetAnyExtensionFromPath("/path/to/file", nil, CaseSensitive) == ""
//	GetAnyExtensionFromPath("/path/to.ext/file", nil, CaseSensitive) == ""
//	GetAnyExtensionFromPath("/path/to/file.ext", ".ext", CaseInsensitive) === ".ext"
//	GetAnyExtensionFromPath("/path/to/file.js", ".ext", CaseInsensitive) === ""
//	GetAnyExtensionFromPath("/path/to/file.js", [".ext", ".js"], CaseInsensitive) === ".js"
//	GetAnyExtensionFromPath("/path/to/file.ext", ".EXT", CaseSensitive) === ""
pub fn get_any_extension_from_path<'a>(
    path: &'a str,
    extensions: &[&str],
    case_sensitivity: CaseSensitivity,
) -> Cow<'a, str> {
    // Retrieves any string from the final "." onwards from a base file name.
    // Unlike extensionFromPath, which throws an exception on unrecognized extensions.
    if !extensions.is_empty() {
        return Cow::Borrowed(get_any_extension_from_path_worker(
            remove_trailing_directory_separator(path),
            extensions,
            case_sensitivity.get_equality_comparer(),
        ));
    }

    match normalize_slashes(path) {
        Cow::Borrowed(s) => Cow::Borrowed(get_any_extension_from_normalized_path(s)),
        Cow::Owned(s) => Cow::Owned(get_any_extension_from_normalized_path(&s).to_string()),
    }
}

pub(crate) fn get_any_extension_from_normalized_path(path: &str) -> &str {
    let base_file_name = get_base_file_name_from_normalized(path);
    if let Some(extension_index) = base_file_name.rfind('.') {
        return &base_file_name[extension_index..];
    }
    ""
}

pub fn get_longest_extension_from_path<'a>(
    path: &'a str,
    extensions: &[&str],
    case_sensitivity: CaseSensitivity,
) -> &'a str {
    let path = remove_trailing_directory_separator(path);
    let comparer = case_sensitivity.get_equality_comparer();
    let mut longest = "";
    for &extension in extensions {
        if extension.len() > longest.len() {
            let matched = try_get_extension_from_path(path, extension, comparer);
            if !matched.is_empty() {
                longest = matched;
            }
        }
    }
    longest
}

pub(crate) fn get_any_extension_from_path_worker<'a>(
    path: &'a str,
    extensions: &[&str],
    string_equality_comparer: fn(&str, &str) -> bool,
) -> &'a str {
    for &extension in extensions {
        let result = try_get_extension_from_path(path, extension, string_equality_comparer);
        if !result.is_empty() {
            return result;
        }
    }
    ""
}

pub(crate) fn try_get_extension_from_path<'a>(
    path: &'a str,
    extension: &str,
    string_equality_comparer: fn(&str, &str) -> bool,
) -> &'a str {
    let extension: Cow<str> = if extension.starts_with('.') {
        Cow::Borrowed(extension)
    } else {
        Cow::Owned(format!(".{extension}"))
    };
    if path.len() >= extension.len() && path.as_bytes()[path.len() - extension.len()] == b'.' {
        let path_extension = &path[path.len() - extension.len()..];
        if string_equality_comparer(path_extension, &extension) {
            return path_extension;
        }
    }
    ""
}

pub fn path_is_relative(path: &str) -> bool {
    // True if path is ".", "..", or starts with "./", "../", ".\", or "..\".

    let bytes = path.as_bytes();
    if path == "." || path == ".." {
        return true;
    }

    if bytes.len() >= 2 && bytes[0] == b'.' && (bytes[1] == b'/' || bytes[1] == b'\\') {
        return true;
    }

    if bytes.len() >= 3
        && bytes[0] == b'.'
        && bytes[1] == b'.'
        && (bytes[2] == b'/' || bytes[2] == b'\\')
    {
        return true;
    }

    false
}

// EnsurePathIsNonModuleName ensures a path is either absolute (prefixed with `/` or `c:`) or dot-relative (prefixed
// with `./` or `../`) so as not to be confused with an unprefixed module name.
pub fn ensure_path_is_non_module_name(path: &str) -> Cow<'_, str> {
    if !path_is_absolute(path) && !path_is_relative(path) {
        return Cow::Owned(format!("./{path}"));
    }
    Cow::Borrowed(path)
}

pub fn is_external_module_name_relative(module_name: &str) -> bool {
    // TypeScript 1.0 spec (April 2014): 11.2.1
    // An external module name is "relative" if the first term is "." or "..".
    // Update: We also consider a path like `C:\foo.ts` "relative" because we do not search for it in `node_modules` or treat it as an ambient module.
    path_is_relative(module_name) || is_rooted_disk_path(module_name)
}

// CaseSensitivity controls canonical path identity and comparison.
// Its zero value is CaseInsensitive.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum CaseSensitivity {
    #[default]
    CaseInsensitive,
    CaseSensitive,
}

impl CaseSensitivity {
    pub fn is_case_sensitive(&self) -> bool {
        *self == CaseSensitivity::CaseSensitive
    }

    pub fn is_case_insensitive(&self) -> bool {
        *self == CaseSensitivity::CaseInsensitive
    }

    // Canonicalize applies c to text used for path comparison or keys.
    pub fn canonicalize<'a>(&self, text: &'a str) -> Cow<'a, str> {
        if self.is_case_sensitive() {
            return Cow::Borrowed(text);
        }
        to_file_name_lower_case(text)
    }

    // TrimPrefix removes prefix from text according to c. It
    // returns text unchanged and false when the prefix does not match.
    //
    // This must not slice text using len(prefix): canonicalization can change a
    // string's UTF-8 byte length without changing its rune count.
    pub fn trim_prefix<'a>(&self, text: &'a str, prefix: &str) -> (&'a str, bool) {
        if self.is_case_sensitive() {
            return match text.strip_prefix(prefix) {
                Some(suffix) => (suffix, true),
                None => (text, false),
            };
        }
        let canonical_prefix = self.canonicalize(prefix);
        if !self.canonicalize(text).starts_with(canonical_prefix.as_ref()) {
            return (text, false);
        }
        (
            trim_rune_count(text, canonical_prefix.chars().count()),
            true,
        )
    }

    // PORT: Go's `String()` method has an `unknown` arm for out-of-range
    // values; a Rust enum cannot hold out-of-range values, so Display only
    // covers the two real variants.
    pub fn get_comparer(&self) -> fn(&str, &str) -> i32 {
        stringutil::get_string_comparer(!self.is_case_sensitive())
    }

    pub(crate) fn get_equality_comparer(&self) -> fn(&str, &str) -> bool {
        stringutil::get_string_equality_comparer(!self.is_case_sensitive())
    }
}

impl fmt::Display for CaseSensitivity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CaseSensitivity::CaseInsensitive => "false",
            CaseSensitivity::CaseSensitive => "true",
        })
    }
}

pub fn compare_paths_relative_to(
    a: &str,
    b: &str,
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> i32 {
    let a = combine_paths(current_directory.as_string(), &[a]);
    let b = combine_paths(current_directory.as_string(), &[b]);
    compare_paths(&a, &b, case_sensitivity)
}

pub fn compare_paths(a: &str, b: &str, case_sensitivity: CaseSensitivity) -> i32 {
    let a = combine_paths("", &[a]);
    let b = combine_paths("", &[b]);
    if a == b {
        return 0;
    }
    if a.is_empty() {
        return -1;
    }
    if b.is_empty() {
        return 1;
    }

    // NOTE: Performance optimization - shortcut if the root segments differ as there would be no
    //       need to perform path reduction.
    let a_root = &a[..get_root_length(&a)];
    let b_root = &b[..get_root_length(&b)];
    let result = stringutil::compare_strings_case_insensitive(a_root, b_root);
    if result != 0 {
        return result;
    }

    // NOTE: Performance optimization - shortcut if there are no relative path segments in
    //       the non-root portion of the path
    let a_rest = &a[a_root.len()..];
    let b_rest = &b[b_root.len()..];
    if !has_relative_path_segment(a_rest) && !has_relative_path_segment(b_rest) {
        return case_sensitivity.get_comparer()(a_rest, b_rest);
    }

    // The path contains a relative path segment. Normalize the paths and perform a slower component
    // by component comparison.
    let a_components = reduce_path_components(&get_path_components(&a));
    let b_components = reduce_path_components(&get_path_components(&b));
    let shared_length = a_components.len().min(b_components.len());
    for i in 1..shared_length {
        let result = case_sensitivity.get_comparer()(&a_components[i], &b_components[i]);
        if result != 0 {
            return result;
        }
    }
    a_components.len().cmp(&b_components.len()) as i32
}

pub fn contains_path(parent: &str, child: &str, case_sensitivity: CaseSensitivity) -> bool {
    let parent = combine_paths("", &[parent]);
    let child = combine_paths("", &[child]);
    if parent.is_empty() || child.is_empty() {
        return false;
    }
    if parent == child {
        return true;
    }
    let parent_components = reduce_path_components(&get_path_components(&parent));
    let child_components = reduce_path_components(&get_path_components(&child));
    if child_components.len() < parent_components.len() {
        return false;
    }

    let component_comparer = case_sensitivity.get_equality_comparer();
    for (i, parent_component) in parent_components.iter().enumerate() {
        let comparer: fn(&str, &str) -> bool = if i == 0 {
            stringutil::equate_string_case_insensitive
        } else {
            component_comparer
        };
        if !comparer(parent_component, &child_components[i]) {
            return false;
        }
    }

    true
}

pub fn file_extension_is(path: &str, extension: &str) -> bool {
    path.len() > extension.len() && path.ends_with(extension)
}

// Calls `callback` on `directory` and every ancestor directory it has, returning the first defined result.
// Stops at global cache location
pub fn for_each_ancestor_directory_stopping_at_global_cache<T>(
    global_cache_location: &str,
    directory: &str,
    mut callback: impl FnMut(&str) -> (T, bool),
) -> Option<T> {
    for_each_ancestor_directory(directory, |ancestor_directory| {
        let (result, stop) = callback(ancestor_directory);
        (result, stop || ancestor_directory == global_cache_location)
    })
}

pub fn for_each_ancestor_directory<T>(
    directory: &str,
    mut callback: impl FnMut(&str) -> (T, bool),
) -> Option<T> {
    // PORT: Go re-slices the input for each parent (no allocation); since
    // get_directory_path can return an owned Cow we keep an owned cursor.
    let mut directory = directory.to_string();
    loop {
        let (result, stop) = callback(&directory);
        if stop {
            return Some(result);
        }

        let parent_path = get_directory_path(&directory);
        if parent_path.as_ref() == directory {
            return None;
        }

        directory = parent_path.into_owned();
    }
}

pub fn has_extension(file_name: &str) -> bool {
    get_base_file_name(file_name).contains('.')
}

pub fn split_volume_path(path: &str) -> (String, &str, bool) {
    let bytes = path.as_bytes();
    if bytes.len() >= 2 && is_volume_character(bytes[0]) && bytes[1] == b':' {
        return (path[0..2].to_lowercase(), &path[2..], true);
    }
    (String::new(), path, false)
}

// GetCommonParents returns the smallest set of directories that are parents of all paths with
// at least `minComponents` directory components. Any path that has fewer than `minComponents` directory components
// will be returned in the second return value. Examples:
//
//	/a/b/c/d, /a/b/c/e, /a/b/f/g  =>  /a/b
//	/a/b/c/d, /a/b/c/e, /a/b/f/g, /x/y  =>  /
//	/a/b/c/d, /a/b/c/e, /a/b/f/g, /x/y  (minComponents: 2)	=>  /a/b, /x/y
//	c:/a/b/c/d, d:/a/b/c/d =>	c:/a/b/c/d, d:/a/b/c/d
pub(crate) fn get_common_parents(
    paths: &[&str],
    min_components: usize,
    get_path_components_fn: impl Fn(&str) -> Vec<String>,
    case_sensitivity: CaseSensitivity,
) -> (Vec<String>, FxHashSet<String>) {
    if min_components < 1 {
        panic!("minComponents must be at least 1");
    }
    if paths.is_empty() {
        return (Vec::new(), FxHashSet::default());
    }
    if paths.len() == 1 {
        if reduce_path_components(&get_path_components_fn(paths[0])).len() < min_components {
            return (Vec::new(), FxHashSet::from_iter([paths[0].to_string()]));
        }
        return (paths.iter().map(|s| s.to_string()).collect(), FxHashSet::default());
    }

    let mut ignored: FxHashSet<String> = FxHashSet::default();
    let mut path_components = Vec::with_capacity(paths.len());
    for &path in paths {
        let components = reduce_path_components(&get_path_components_fn(path));
        if components.len() < min_components {
            ignored.insert(path.to_string());
        } else {
            path_components.push(components);
        }
    }

    let results = get_common_parents_worker(&path_components, min_components, case_sensitivity);
    let result_paths: Vec<String> = results
        .iter()
        .map(|comps| get_path_from_path_components(comps))
        .collect();

    (result_paths, ignored)
}

pub(crate) fn get_common_parents_worker(
    component_groups: &[Vec<String>],
    min_components: usize,
    case_sensitivity: CaseSensitivity,
) -> Vec<Vec<String>> {
    if component_groups.is_empty() {
        return Vec::new();
    }
    // Determine the maximum depth we can consider
    let mut max_depth = component_groups[0].len();
    for comps in &component_groups[1..] {
        let l = comps.len();
        if l < max_depth {
            max_depth = l;
        }
    }

    let equality = case_sensitivity.get_equality_comparer();
    for last_common_index in 0..max_depth {
        let candidate = &component_groups[0][last_common_index];
        for comps in &component_groups[1..] {
            if !equality(candidate, &comps[last_common_index]) {
                // divergence
                if last_common_index < min_components {
                    // Not enough components, we need to fan out
                    let mut ordered_groups: Vec<String> = Vec::with_capacity(component_groups.len());
                    let mut new_groups: FxHashMap<String, (Vec<String>, Vec<Vec<String>>)> =
                        FxHashMap::default();
                    // PORT: `new_groups` is
                    // `FxHashMap<String, (Vec<String>, Vec<Vec<String>>)>`
                    // (Go: map[string]struct{head, tails}).
                    for g in component_groups {
                        let key =
                            case_sensitivity.canonicalize(&g[last_common_index]).into_owned();
                        if !new_groups.contains_key(&key) {
                            ordered_groups.push(key.clone());
                        }
                        let entry = new_groups
                            .entry(key)
                            .or_insert_with(|| (g[..last_common_index + 1].to_vec(), Vec::new()));
                        entry.1.push(g[last_common_index + 1..].to_vec());
                    }
                    ordered_groups.sort_unstable();
                    let mut result: Vec<Vec<String>> = Vec::with_capacity(new_groups.len());
                    for key in &ordered_groups {
                        let (head, tails) = new_groups.get(key).unwrap();
                        let sub_results = get_common_parents_worker(
                            tails,
                            min_components - (last_common_index + 1),
                            case_sensitivity,
                        );
                        for sr in sub_results {
                            if sr.is_empty() {
                                result.push(head.clone());
                            } else {
                                let mut combined = head.clone();
                                combined.extend(sr);
                                result.push(combined);
                            }
                        }
                    }
                    return result;
                }
                return vec![component_groups[0][..last_common_index].to_vec()];
            }
        }
    }

    vec![component_groups[0][..max_depth].to_vec()]
}

pub fn starts_with_directory(
    file_name: &str,
    directory_name: &str,
    case_sensitivity: CaseSensitivity,
) -> bool {
    if directory_name.is_empty() {
        return false;
    }

    let canonical_file_name = case_sensitivity.canonicalize(file_name);
    let canonical_directory_name = case_sensitivity.canonicalize(directory_name);
    let canonical_directory_name = canonical_directory_name
        .strip_suffix('/')
        .unwrap_or(canonical_directory_name.as_ref());
    let canonical_directory_name = canonical_directory_name
        .strip_suffix('\\')
        .unwrap_or(canonical_directory_name);

    canonical_file_name.starts_with(&format!("{canonical_directory_name}/"))
        || canonical_file_name.starts_with(&format!("{canonical_directory_name}\\"))
}

pub fn compare_number_of_directory_separators(path1: &str, path2: &str) -> i32 {
    path1
        .matches('/')
        .count()
        .cmp(&path2.matches('/').count()) as i32
}
