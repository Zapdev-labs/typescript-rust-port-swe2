// Ported from tsc/internal/tspath/pathkey.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::ops::Deref;

use crate::dynamic::{canonical_dynamic_uri_path, is_encoded_dynamic_file_name};
use crate::extension::{
    file_extension_is_one_of, has_js_file_extension, try_get_extension_from_path,
};
use crate::path::{
    CaseSensitivity, DIRECTORY_SEPARATOR, get_base_file_name_from_normalized,
    get_directory_path_from_normalized, get_root_length, has_trailing_directory_separator,
    is_dynamic_file_name, remove_trailing_directory_separator, to_file_name_lower_case,
};
use crate::rooted_path::{RootedPath, try_rooted_path_from_normalized};
// PORT(shim): temporary — replace with `use tsc_stringutil as stringutil` once
// tsc-stringutil provides these functions.
use crate::stringutil_shim as stringutil;

// PathKey is a canonical key for a rooted, normalized path under a
// caller-selected CaseSensitivity. Keys are comparable only when they use the
// same CaseSensitivity. A PathKey is for comparison and lookup, and must not be
// used as a RootedPath because canonicalization may have changed its casing.
// The zero value is a valid sentinel. PathKey does not assert that the path
// exists.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PathKey(String);

// PathKeyFromCanonical constructs a PathKey from text whose CaseSensitivity has
// already been applied. It validates that a non-empty path is rooted and
// normalized; the empty path is accepted as the sentinel value.
pub fn path_key_from_canonical(path: &str) -> PathKey {
    match try_path_key_from_canonical(path) {
        Some(result) => result,
        None => panic!("path must be normalized"),
    }
}

// TryPathKeyFromCanonical constructs a PathKey from text whose CaseSensitivity
// has already been applied. It validates that a non-empty path is rooted and
// normalized; the empty path is accepted as the sentinel value.
pub fn try_path_key_from_canonical(path: &str) -> Option<PathKey> {
    if path.is_empty() {
        return Some(PathKey::default());
    }
    if try_rooted_path_from_normalized(path).is_none() {
        return None;
    }
    Some(PathKey::from(path))
}

impl From<&str> for PathKey {
    fn from(s: &str) -> Self {
        PathKey(s.to_string())
    }
}

impl From<String> for PathKey {
    fn from(s: String) -> Self {
        PathKey(s)
    }
}

impl Deref for PathKey {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl CaseSensitivity {
    // PathKey returns the canonical key for an already rooted, normalized path
    // under c.
    pub fn path_key(&self, path: &RootedPath) -> PathKey {
        if is_encoded_dynamic_file_name(path.as_string()) {
            return PathKey::from(canonical_dynamic_uri_path(path.as_string()).as_ref());
        }
        PathKey::from(self.canonicalize(path.as_string()).as_ref())
    }
}

impl PathKey {
    pub fn as_string(&self) -> &str {
        &self.0
    }

    // Parent returns the lexical parent key. Root keys are fixed points, while the
    // parent of a single-component relative key is the empty key.
    pub fn parent(&self) -> PathKey {
        PathKey::from(get_directory_path_from_normalized(&self.0))
    }

    pub fn remove_trailing_directory_separator(&self) -> PathKey {
        PathKey::from(remove_trailing_directory_separator(&self.0))
    }

    pub fn extension(&self) -> &str {
        try_get_extension_from_path(&self.0)
    }

    pub fn extension_is_one_of(&self, extensions: &[&str]) -> bool {
        file_extension_is_one_of(&self.0, extensions)
    }

    pub fn has_js_file_extension(&self) -> bool {
        has_js_file_extension(&self.0)
    }

    pub fn base_name(&self) -> &str {
        get_base_file_name_from_normalized(&self.0)
    }

    pub fn is_dynamic(&self) -> bool {
        is_dynamic_file_name(&self.0)
    }

    pub fn case_insensitive_key(&self) -> PathKey {
        if is_encoded_dynamic_file_name(&self.0) {
            return self.clone();
        }
        PathKey::from(to_file_name_lower_case(&self.0).as_ref())
    }

    // AppendCanonicalComponent appends an already canonical path component.
    pub fn append_canonical_component(&self, component: &str) -> PathKey {
        if self.is_empty() {
            panic!("cannot append a component to an empty path key");
        }
        if component.is_empty()
            || component.contains(['/', '\\'])
            || component == "."
            || component == ".."
        {
            panic!("invalid canonical path component");
        }
        let result = if has_trailing_directory_separator(&self.0) {
            format!("{}{component}", self.0)
        } else {
            format!("{}/{component}", self.0)
        };
        path_key_from_canonical(&result)
    }

    // AppendCanonicalSuffix appends a suffix that is already canonical under the
    // CaseSensitivity used to construct p.
    pub fn append_canonical_suffix(&self, suffix: &str) -> PathKey {
        if self.is_empty() && !suffix.is_empty() {
            panic!("cannot append a suffix to an empty path key");
        }
        if suffix.contains(['/', '\\']) {
            panic!("path suffix must not contain a directory separator");
        }
        path_key_from_canonical(&format!("{}{suffix}", self.0))
    }

    // SplitAtCanonicalComponent finds component and returns the path before it and
    // the path through it. Both results retain the key's canonical casing.
    pub fn split_at_canonical_component(&self, component: &str) -> Option<(PathKey, PathKey)> {
        if component.is_empty()
            || component.contains(['/', '\\'])
            || component == "."
            || component == ".."
        {
            panic!("invalid canonical path component");
        }
        let needle = format!("/{component}");
        let path = self.as_string();
        let root_length = get_root_length(path);
        if root_length == 0 {
            return None;
        }
        let mut offset = root_length - 1;
        loop {
            let index = match path[offset..].find(&needle) {
                None => return None,
                Some(i) => i + offset,
            };
            let end = index + needle.len();
            if end == path.len() || path.as_bytes()[end] == DIRECTORY_SEPARATOR as u8 {
                let before_end = index.max(root_length);
                return Some((
                    PathKey::from(&path[..before_end]),
                    PathKey::from(&path[..end]),
                ));
            }
            offset = end;
        }
    }

    // ContainsLowercaseDirectorySequence checks a slash-delimited lowercase
    // component sequence that includes both its leading and trailing separators.
    pub fn contains_lowercase_directory_sequence(&self, sequence: &str) -> bool {
        self.0.contains(sequence)
    }

    // ContainsPath checks whether child is contained within or equal to p.
    // Both keys must have been created with the same CaseSensitivity.
    pub fn contains_path(&self, child: &PathKey) -> bool {
        if self.0.is_empty() {
            return false;
        }
        let parent = self.as_string();
        let child_text = child.as_string();
        let parent_root_length = get_root_length(parent);
        let child_root_length = get_root_length(child_text);
        let mut parent_root = &parent[..parent_root_length];
        let mut child_root = &child_text[..child_root_length];
        let dynamic = is_encoded_dynamic_file_name(parent) || is_encoded_dynamic_file_name(child_text);
        if dynamic {
            parent_root = parent_root
                .strip_suffix(DIRECTORY_SEPARATOR)
                .unwrap_or(parent_root);
            child_root = child_root
                .strip_suffix(DIRECTORY_SEPARATOR)
                .unwrap_or(child_root);
        }
        let mut roots_equal = stringutil::equate_string_case_insensitive(parent_root, child_root);
        if dynamic {
            roots_equal = parent_root == child_root;
        }
        if !roots_equal {
            return false;
        }
        let parent_rest = &parent[parent_root_length..];
        let child_rest = &child_text[child_root_length..];
        parent_rest == child_rest
            || (child_rest.len() > parent_rest.len()
                && child_rest.starts_with(parent_rest)
                && (parent_rest.is_empty()
                    || parent_rest.as_bytes()[parent_rest.len() - 1] == b'/'
                    || child_rest.as_bytes()[parent_rest.len()] == b'/'))
    }

    // ForEachAncestorDirectory calls callback for p and each of its ancestors.
    pub fn for_each_ancestor_directory<T>(
        &self,
        mut callback: impl FnMut(&PathKey) -> (T, bool),
    ) -> Option<T> {
        let mut p = self.clone();
        loop {
            let (result, stop) = callback(&p);
            if stop {
                return Some(result);
            }
            let parent = p.parent();
            if parent == p {
                return None;
            }
            p = parent;
        }
    }
}
