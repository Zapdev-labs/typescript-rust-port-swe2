// Ported from tsc/internal/tspath/rooted_path.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;
use std::ops::Deref;

use rustc_hash::FxHashSet;

use crate::dynamic::{canonical_dynamic_uri_path, is_encoded_dynamic_file_name};
use crate::extension::{
    change_any_extension, change_extension, change_full_extension, file_extension_is_one_of,
    get_declaration_emit_extension_for_path, get_declaration_file_extension_from_normalized,
    get_possible_original_input_extension_for_extension, has_implementation_ts_file_extension,
    has_json_file_extension, has_js_file_extension, has_ts_file_extension, remove_extension,
    remove_file_extension, try_extract_ts_extension, try_get_extension_from_path,
};
use crate::module_specifier::ModuleSpecifier;
use crate::path::{
    DIRECTORY_SEPARATOR, URL_SCHEME_SEPARATOR, CaseSensitivity, file_extension_is,
    get_base_file_name_from_normalized, get_directory_path_from_normalized,
    get_encoded_root_length, get_normalized_absolute_path,
    get_normalized_absolute_path_from_directory,
    get_normalized_absolute_path_from_normalized_slashes, get_path_components,
    get_path_from_path_components, get_root_length, has_relative_path_segment,
    has_trailing_directory_separator, is_any_directory_separator, is_dynamic_file_name,
    normalize_slashes, path_is_absolute, reduce_path_components,
    remove_trailing_directory_separator,
};
use crate::relative_path::RelativePath;
// PORT(shim): temporary — replace with `use tsc_stringutil as stringutil` once
// tsc-stringutil provides these functions.
use crate::stringutil_shim as stringutil;

// RootedPath is a rooted, slash-normalized, lexically normalized path that may
// represent either a file or a directory. It preserves path casing. Its zero
// value is a valid sentinel.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RootedPath(String);

// RootedFilePath is a RootedPath intended to be used as a file path. It does
// not assert that the path exists or is a file on a filesystem.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RootedFilePath(String);

// FileNameStem is a rooted filename prefix, not a normalized path. Removing
// an extension can leave a trailing separator or a "." or ".." component.
// Complete the stem with AppendSuffix before using it as a path.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FileNameStem(String);

// RootedDirectoryPath is a RootedPath intended to be used as a directory path.
// It does not assert that the path exists or is a directory on a filesystem,
// and does not guarantee a trailing directory separator.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RootedDirectoryPath(String);

impl RootedPath {
    pub fn as_string(&self) -> &str {
        &self.0
    }
}

impl From<&str> for RootedPath {
    fn from(s: &str) -> Self {
        RootedPath(s.to_string())
    }
}

impl From<String> for RootedPath {
    fn from(s: String) -> Self {
        RootedPath(s)
    }
}

impl From<RootedFilePath> for RootedPath {
    fn from(f: RootedFilePath) -> Self {
        RootedPath(f.0)
    }
}

impl From<RootedDirectoryPath> for RootedPath {
    fn from(d: RootedDirectoryPath) -> Self {
        RootedPath(d.0)
    }
}

impl Deref for RootedPath {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl From<&str> for RootedFilePath {
    fn from(s: &str) -> Self {
        RootedFilePath(s.to_string())
    }
}

impl From<String> for RootedFilePath {
    fn from(s: String) -> Self {
        RootedFilePath(s)
    }
}

impl From<RootedPath> for RootedFilePath {
    fn from(p: RootedPath) -> Self {
        RootedFilePath(p.0)
    }
}

impl From<RootedFilePath> for RootedDirectoryPath {
    fn from(f: RootedFilePath) -> Self {
        RootedDirectoryPath(f.0)
    }
}

impl Deref for RootedFilePath {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl From<&str> for FileNameStem {
    fn from(s: &str) -> Self {
        FileNameStem(s.to_string())
    }
}

impl From<String> for FileNameStem {
    fn from(s: String) -> Self {
        FileNameStem(s)
    }
}

impl Deref for FileNameStem {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl From<&str> for RootedDirectoryPath {
    fn from(s: &str) -> Self {
        RootedDirectoryPath(s.to_string())
    }
}

impl From<String> for RootedDirectoryPath {
    fn from(s: String) -> Self {
        RootedDirectoryPath(s)
    }
}

impl From<RootedPath> for RootedDirectoryPath {
    fn from(p: RootedPath) -> Self {
        RootedDirectoryPath(p.0)
    }
}

impl Deref for RootedDirectoryPath {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

// ToRootedPath resolves path against currentDirectory and normalizes it.
pub fn to_rooted_path(path: &str, current_directory: &RootedDirectoryPath) -> RootedPath {
    if path.is_empty() {
        panic!("path must not be empty");
    }
    if has_rooted_url_suffix(path) {
        panic!("path must not contain a URL query or fragment");
    }
    if get_encoded_root_length(path) == 0
        && has_url_root(current_directory.as_string())
        && path.contains(['?', '#'])
    {
        panic!("relative URL path must not contain a query or fragment");
    }
    let normalized = get_normalized_absolute_path_from_directory(path, current_directory);
    if get_encoded_root_length(&normalized) == 0 || has_rooted_url_suffix(&normalized) {
        panic!("path must be rooted");
    }
    RootedPath(ensure_rooted_path_root_separator(&normalized).into_owned())
}

// RootedPathFromAbsolute validates and normalizes an absolute path, including
// converting platform directory separators to '/'.
pub fn rooted_path_from_absolute(path: &str) -> RootedPath {
    match try_rooted_path_from_absolute(path) {
        Some(result) => result,
        None => panic!("path must be absolute"),
    }
}

// TryRootedPathFromAbsolute validates and normalizes an absolute path,
// including converting platform directory separators to '/'.
pub fn try_rooted_path_from_absolute(path: &str) -> Option<RootedPath> {
    if has_rooted_url_suffix(path) || !path_is_absolute(path) {
        return None;
    }
    Some(RootedPath(
        ensure_rooted_path_root_separator(&get_normalized_absolute_path(
            path,
            &RootedDirectoryPath(String::new()),
        ))
        .into_owned(),
    ))
}

fn ensure_rooted_path_root_separator(path: &str) -> Cow<'_, str> {
    if get_root_length(path) == path.len() && !has_trailing_directory_separator(path) {
        return Cow::Owned(format!("{path}{DIRECTORY_SEPARATOR}"));
    }
    Cow::Borrowed(path)
}

// RootedPathFromNormalized validates a path that is already rooted and
// normalized without changing it.
pub fn rooted_path_from_normalized(path: &str) -> RootedPath {
    match try_rooted_path_from_normalized(path) {
        Some(result) => result,
        None => panic!("path must be rooted and normalized: {path}"),
    }
}

// TryRootedPathFromNormalized validates a path that is already rooted and
// normalized without changing it.
pub fn try_rooted_path_from_normalized(path: &str) -> Option<RootedPath> {
    if has_rooted_url_suffix(path) {
        return None;
    }
    let mut root_length = get_encoded_root_length(path);
    if root_length < 0 {
        root_length = !root_length;
    }
    let root_length = root_length as usize;
    if path.is_empty()
        || root_length == 0
        || path.contains('\\')
        || (root_length < path.len() && path.as_bytes()[root_length] == b'/')
        || has_relative_path_segment(&path[root_length..])
        || (path.len() == root_length && !has_trailing_directory_separator(path))
        || (path.len() > root_length && has_trailing_directory_separator(path))
    {
        return None;
    }
    Some(RootedPath::from(path))
}

pub(crate) fn has_rooted_url_suffix(path: &str) -> bool {
    if !has_url_root(path) {
        return false;
    }
    let after_scheme = match path.split_once(URL_SCHEME_SEPARATOR) {
        Some((_, after)) => after,
        None => path,
    };
    after_scheme.find(['?', '#']).is_some()
}

pub(crate) fn has_url_root(path: &str) -> bool {
    get_encoded_root_length(path) < 0 && path.contains(URL_SCHEME_SEPARATOR)
}

// ToRootedFilePath resolves fileName against currentDirectory, normalizes it,
// and gives it file intent.
pub fn to_rooted_file_path(file_name: &str, current_directory: &RootedDirectoryPath) -> RootedFilePath {
    RootedFilePath(to_rooted_path(file_name, current_directory).0)
}

// RootedFilePathFromAbsolute validates and normalizes an absolute path,
// including converting platform directory separators to '/', then gives it
// file intent.
pub fn rooted_file_path_from_absolute(file_name: &str) -> RootedFilePath {
    RootedFilePath(rooted_path_from_absolute(file_name).0)
}

// TryRootedFilePathFromAbsolute validates and normalizes an absolute path,
// including converting platform directory separators to '/', then gives it
// file intent.
pub fn try_rooted_file_path_from_absolute(file_name: &str) -> Option<RootedFilePath> {
    try_rooted_path_from_absolute(file_name).map(|p| RootedFilePath(p.0))
}

// RootedFilePathFromNormalized validates a path that is already rooted and
// normalized without changing it, then gives it file intent.
pub fn rooted_file_path_from_normalized(file_name: &str) -> RootedFilePath {
    RootedFilePath(rooted_path_from_normalized(file_name).0)
}

// TryRootedFilePathFromNormalized validates a path that is already rooted and
// normalized without changing it, then gives it file intent.
pub fn try_rooted_file_path_from_normalized(file_name: &str) -> Option<RootedFilePath> {
    try_rooted_path_from_normalized(file_name).map(|p| RootedFilePath(p.0))
}

// ToRootedDirectoryPath resolves directory against currentDirectory,
// normalizes it, and gives it directory intent.
pub fn to_rooted_directory_path(
    directory: &str,
    current_directory: &RootedDirectoryPath,
) -> RootedDirectoryPath {
    RootedDirectoryPath(to_rooted_path(directory, current_directory).0)
}

// RootedDirectoryPathFromAbsolute validates and normalizes an absolute path,
// including converting platform directory separators to '/', then gives it
// directory intent.
pub fn rooted_directory_path_from_absolute(directory: &str) -> RootedDirectoryPath {
    RootedDirectoryPath(rooted_path_from_absolute(directory).0)
}

// RootedDirectoryPathFromNormalized validates a path that is already rooted
// and normalized without changing it, then gives it directory intent.
pub fn rooted_directory_path_from_normalized(directory: &str) -> RootedDirectoryPath {
    RootedDirectoryPath(rooted_path_from_normalized(directory).0)
}

// RootedFilePathFromPath gives a RootedPath file intent without changing it.
pub fn rooted_file_path_from_path(path: RootedPath) -> RootedFilePath {
    RootedFilePath(path.0)
}

// RootedDirectoryPathFromPath gives a RootedPath directory intent without
// changing it.
pub fn rooted_directory_path_from_path(path: RootedPath) -> RootedDirectoryPath {
    RootedDirectoryPath(path.0)
}

impl RootedFilePath {
    pub fn as_string(&self) -> &str {
        &self.0
    }

    // Compare returns the case-sensitive lexical ordering of the normalized path text.
    pub fn compare(&self, other: &RootedFilePath) -> i32 {
        stringutil::compare_strings_case_sensitive(&self.0, &other.0)
    }

    pub fn as_path(&self) -> RootedPath {
        RootedPath(self.0.clone())
    }

    pub fn as_module_specifier(&self) -> ModuleSpecifier {
        ModuleSpecifier::from(self.0.as_str())
    }

    pub fn directory(&self) -> RootedDirectoryPath {
        self.as_path().directory()
    }

    pub fn without_root(&self) -> &str {
        let path = self.as_string();
        &path[get_root_length(path)..]
    }

    pub fn root_and_relative_path(&self) -> (RootedDirectoryPath, &str) {
        // PORT: Go delegates to AsPath().RootAndRelativePath(); inlined because
        // the result borrows from self.
        let path = self.as_string();
        let root_length = get_root_length(path);
        (
            RootedDirectoryPath::from(&path[..root_length]),
            &path[root_length..],
        )
    }

    pub fn directory_before(&self, index: usize) -> RootedDirectoryPath {
        let path = self.as_string();
        if index < get_root_length(path)
            || index > path.len()
            || (index < path.len() && !is_any_directory_separator(path.as_bytes()[index]))
        {
            panic!("directory boundary must be at a path separator");
        }
        RootedDirectoryPath::from(&path[..index])
    }

    pub fn suffix_after_separator(&self, index: usize) -> &str {
        let path = self.as_string();
        if index >= path.len() || !is_any_directory_separator(path.as_bytes()[index]) {
            panic!("suffix boundary must be at a path separator");
        }
        &path[index + 1..]
    }

    // AppendSuffix appends a suffix that cannot change the rooted or normalized
    // path structure.
    pub fn append_suffix(&self, suffix: &str) -> RootedFilePath {
        validate_file_name_suffix(self.as_string(), suffix);
        let result = RootedFilePath(format!("{}{}", self.0, suffix));
        if !result.is_empty() {
            rooted_path_from_normalized(result.as_string());
        }
        result
    }

    pub fn as_stem(&self) -> FileNameStem {
        FileNameStem(self.0.clone())
    }

    pub fn remove_file_extension(&self) -> FileNameStem {
        FileNameStem::from(remove_file_extension(self.as_string()))
    }

    pub fn remove_extension(&self, extension: &str) -> FileNameStem {
        validate_file_extension(extension);
        if !self.as_string().ends_with(extension) {
            panic!("file name does not have extension: {extension}");
        }
        FileNameStem::from(remove_extension(self.as_string(), extension))
    }

    pub fn change_extension(&self, extension: &str) -> RootedFilePath {
        validate_file_extension(extension);
        rooted_file_path_from_extension_mutation(&change_extension(&self.0, extension))
    }

    pub fn change_full_extension(&self, extension: &str) -> RootedFilePath {
        validate_file_extension(extension);
        rooted_file_path_from_extension_mutation(&change_full_extension(&self.0, extension))
    }

    pub fn change_any_extension(
        &self,
        extension: &str,
        extensions: &[&str],
        case_sensitivity: CaseSensitivity,
    ) -> RootedFilePath {
        validate_file_extension(extension);
        for candidate in extensions {
            validate_file_extension(candidate);
        }
        rooted_file_path_from_extension_mutation(&change_any_extension(
            &self.0,
            extension,
            extensions,
            case_sensitivity,
        ))
    }

    pub fn base_name(&self) -> &str {
        // PORT: Go delegates to AsPath().BaseName(); inlined because the result
        // borrows from self.
        get_base_file_name_from_normalized(&self.0)
    }

    pub fn extension_is(&self, extension: &str) -> bool {
        file_extension_is(&self.0, extension)
    }

    pub fn extension_is_one_of(&self, extensions: &[&str]) -> bool {
        file_extension_is_one_of(&self.0, extensions)
    }

    pub fn extension(&self) -> &str {
        try_get_extension_from_path(&self.0)
    }

    pub fn any_extension(
        &self,
        extensions: &[&str],
        case_sensitivity: CaseSensitivity,
    ) -> Cow<'_, str> {
        if extensions.is_empty() {
            return Cow::Borrowed(crate::path::get_any_extension_from_normalized_path(&self.0));
        }
        crate::path::get_any_extension_from_path(&self.0, extensions, case_sensitivity)
    }

    pub fn longest_extension(&self, extensions: &[&str], case_sensitivity: CaseSensitivity) -> &str {
        crate::path::get_longest_extension_from_path(&self.0, extensions, case_sensitivity)
    }

    pub fn has_extension(&self) -> bool {
        get_base_file_name_from_normalized(&self.0).contains('.')
    }

    pub fn has_implementation_ts_file_extension(&self) -> bool {
        has_implementation_ts_file_extension(&self.0)
    }

    pub fn has_ts_file_extension(&self) -> bool {
        has_ts_file_extension(&self.0)
    }

    pub fn try_extract_ts_extension(&self) -> &str {
        try_extract_ts_extension(&self.0)
    }

    pub fn has_json_file_extension(&self) -> bool {
        has_json_file_extension(&self.0)
    }

    pub fn declaration_file_extension(&self) -> &str {
        get_declaration_file_extension_from_normalized(&self.0)
    }

    pub fn declaration_emit_extension(&self) -> Cow<'_, str> {
        get_declaration_emit_extension_for_path(&self.0)
    }

    pub fn possible_original_input_extensions(&self) -> Vec<String> {
        get_possible_original_input_extension_for_extension(&self.0)
    }

    pub fn has_js_file_extension(&self) -> bool {
        has_js_file_extension(&self.0)
    }

    pub fn is_dynamic(&self) -> bool {
        self.as_path().is_dynamic()
    }

    pub fn is_declaration_file(&self) -> bool {
        !get_declaration_file_extension_from_normalized(&self.0).is_empty()
    }

    pub fn components(&self) -> Vec<String> {
        get_path_components(&self.0)
    }

    pub fn root_length(&self) -> usize {
        get_root_length(&self.0)
    }

    pub fn relative_to(&self, directory: &RootedDirectoryPath) -> Option<RelativePath> {
        self.as_path().relative_to(directory)
    }

    pub fn split_at_component(
        &self,
        component: &str,
    ) -> Option<(RootedDirectoryPath, RootedDirectoryPath)> {
        if component.is_empty()
            || component.contains(['/', '\\'])
            || component == "."
            || component == ".."
        {
            panic!("invalid path component");
        }
        let needle = format!("/{component}");
        let path = self.as_string();
        let root_length = self.root_length();
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
                    RootedDirectoryPath::from(&path[..before_end]),
                    RootedDirectoryPath::from(&path[..end]),
                ));
            }
            offset = end;
        }
    }

    pub fn contains_lowercase_directory_sequence(&self, sequence: &str) -> bool {
        self.0.contains(sequence)
    }

    pub fn split_at_last_component(
        &self,
        component: &str,
    ) -> Option<(RootedDirectoryPath, RootedDirectoryPath)> {
        if component.is_empty()
            || component.contains(['/', '\\'])
            || component == "."
            || component == ".."
        {
            panic!("invalid path component");
        }
        let needle = format!("/{component}");
        let path = self.as_string();
        let mut end = path.len();
        while end > 0 {
            let index = match path[..end].rfind(&needle) {
                None => return None,
                Some(i) => i,
            };
            let component_end = index + needle.len();
            // PORT: `index + 1 >= root_length` is Go's `index >= f.RootLength()-1`
            // without the usize underflow when root_length == 0.
            if index + 1 >= self.root_length()
                && (component_end == path.len()
                    || path.as_bytes()[component_end] == DIRECTORY_SEPARATOR as u8)
            {
                let before_end = index.max(self.root_length());
                return Some((
                    RootedDirectoryPath::from(&path[..before_end]),
                    RootedDirectoryPath::from(&path[..component_end]),
                ));
            }
            end = index;
        }
        None
    }

    pub fn directory_separator_count(&self) -> usize {
        self.0.matches('/').count()
    }
}

impl RootedPath {
    // Compare returns the case-sensitive lexical ordering of the normalized path text.
    pub fn compare(&self, other: &RootedPath) -> i32 {
        stringutil::compare_strings_case_sensitive(&self.0, &other.0)
    }

    pub fn directory(&self) -> RootedDirectoryPath {
        let path = self.as_string();
        let root_length = get_root_length(path);
        if root_length == path.len() {
            return RootedDirectoryPath(self.0.clone());
        }
        let path = remove_trailing_directory_separator(path);
        RootedDirectoryPath::from(&path[..root_length.max(last_directory_separator(path).unwrap_or(0))])
    }

    pub fn root_and_relative_path(&self) -> (RootedDirectoryPath, &str) {
        let path = self.as_string();
        let root_length = get_root_length(path);
        (
            RootedDirectoryPath::from(&path[..root_length]),
            &path[root_length..],
        )
    }

    pub fn base_name(&self) -> &str {
        get_base_file_name_from_normalized(&self.0)
    }

    pub fn is_dynamic(&self) -> bool {
        is_dynamic_file_name(&self.0)
    }

    pub fn relative_to(&self, directory: &RootedDirectoryPath) -> Option<RelativePath> {
        CaseSensitivity::CaseSensitive
            .trim_contained_path(directory.as_string(), self.as_string())
            .map(RelativePath::from)
    }
}

pub(crate) fn validate_file_name_suffix(prefix: &str, suffix: &str) {
    if prefix.is_empty() && !suffix.is_empty() {
        panic!("cannot append a suffix to an empty file name");
    }
    if suffix.contains(['/', '\\']) {
        panic!("file name suffix must not contain a directory separator");
    }
}

impl FileNameStem {
    pub fn as_string(&self) -> &str {
        &self.0
    }

    pub fn append_suffix(&self, suffix: &str) -> RootedFilePath {
        validate_file_name_suffix(self.as_string(), suffix);
        let result = format!("{}{}", self.0, suffix);
        if result.is_empty() {
            return RootedFilePath::default();
        }
        rooted_file_path_from_normalized(&result)
    }
}

pub(crate) fn validate_file_extension(extension: &str) {
    if extension.contains(['/', '\\']) {
        panic!("file extension must not contain a directory separator");
    }
}

pub(crate) fn rooted_file_path_from_extension_mutation(path: &str) -> RootedFilePath {
    let base_name = get_base_file_name_from_normalized(path);
    if base_name == "."
        || base_name == ".."
        || (has_trailing_directory_separator(path) && path.len() > get_root_length(path))
    {
        panic!("file extension change must preserve path normalization");
    }
    rooted_file_path_from_resolved(path)
}

impl CaseSensitivity {
    pub fn split_file_path_at_component(
        &self,
        file_name: &RootedFilePath,
        component: &str,
    ) -> Option<(RootedDirectoryPath, RootedDirectoryPath)> {
        if component.is_empty()
            || component.contains(['/', '\\'])
            || component == "."
            || component == ".."
        {
            panic!("invalid path component");
        }
        let components = get_path_components(file_name.as_string());
        let mut c = *self;
        if is_encoded_dynamic_file_name(file_name.as_string()) {
            c = CaseSensitivity::CaseSensitive;
        }
        for i in 1..components.len() {
            if c.get_comparer()(&components[i], component) == 0 {
                return Some((
                    RootedDirectoryPath::from(get_path_from_path_components(&components[..i])),
                    RootedDirectoryPath::from(get_path_from_path_components(&components[..i + 1])),
                ));
            }
        }
        None
    }

    // CompareFilePaths compares already rooted and normalized file names without
    // combining or reducing their path components.
    pub fn compare_file_paths(&self, a: &RootedFilePath, b: &RootedFilePath) -> i32 {
        self.compare_paths(&a.as_path(), &b.as_path())
    }

    // ComparePaths compares already rooted and normalized paths without combining
    // or reducing their path components.
    pub fn compare_paths(&self, a: &RootedPath, b: &RootedPath) -> i32 {
        self.compare_rooted_text(a.as_string(), b.as_string())
    }

    // CompareFileNameStems compares filename prefixes without interpreting dot
    // components produced by extension removal as directory traversal.
    pub fn compare_file_name_stems(&self, a: &FileNameStem, b: &FileNameStem) -> i32 {
        self.compare_rooted_text(a.as_string(), b.as_string())
    }

    fn compare_rooted_text(&self, a_string: &str, b_string: &str) -> i32 {
        if a_string == b_string {
            return 0;
        }
        if a_string.is_empty() {
            return -1;
        }
        if b_string.is_empty() {
            return 1;
        }

        if is_encoded_dynamic_file_name(a_string) || is_encoded_dynamic_file_name(b_string) {
            return stringutil::compare_strings_case_sensitive(
                &canonical_dynamic_uri_path(a_string),
                &canonical_dynamic_uri_path(b_string),
            );
        }
        let a_root_length = get_root_length(a_string);
        let b_root_length = get_root_length(b_string);
        let result = stringutil::compare_strings_case_insensitive(
            &a_string[..a_root_length],
            &b_string[..b_root_length],
        );
        if result != 0 {
            return result;
        }
        self.get_comparer()(&a_string[a_root_length..], &b_string[b_root_length..])
    }

    pub fn contains_file_path(&self, parent: &RootedDirectoryPath, child: &RootedFilePath) -> bool {
        self.contains_path(parent, &child.as_path())
    }

    pub fn contains_path(&self, parent: &RootedDirectoryPath, child: &RootedPath) -> bool {
        self.trim_contained_path(parent.as_string(), child.as_string())
            .is_some()
    }

    pub fn starts_with_directory(
        &self,
        file_name: &RootedFilePath,
        directory: &RootedDirectoryPath,
    ) -> bool {
        match self.trim_contained_path(directory.as_string(), file_name.as_string()) {
            Some(relative) => !relative.is_empty(),
            None => false,
        }
    }

    pub fn relative_file_path_from_directory(
        &self,
        directory: &RootedDirectoryPath,
        file_name: &RootedFilePath,
    ) -> Option<RelativePath> {
        self.relative_path_within_directory(directory, &file_name.as_path())
    }

    pub fn relative_path_within_directory(
        &self,
        directory: &RootedDirectoryPath,
        path: &RootedPath,
    ) -> Option<RelativePath> {
        self.trim_contained_path(directory.as_string(), path.as_string())
            .map(RelativePath::from)
    }

    pub(crate) fn trim_contained_path<'a>(&self, parent: &str, child: &'a str) -> Option<&'a str> {
        if parent.is_empty() || child.is_empty() {
            return None;
        }
        let parent_root_length = get_root_length(parent);
        let child_root_length = get_root_length(child);
        let mut parent_root = &parent[..parent_root_length];
        let mut child_root = &child[..child_root_length];
        let dynamic = is_encoded_dynamic_file_name(parent) || is_encoded_dynamic_file_name(child);
        let mut c = *self;
        if dynamic {
            parent_root = parent_root
                .strip_suffix(DIRECTORY_SEPARATOR)
                .unwrap_or(parent_root);
            child_root = child_root
                .strip_suffix(DIRECTORY_SEPARATOR)
                .unwrap_or(child_root);
            c = CaseSensitivity::CaseSensitive;
        }
        let mut roots_equal = stringutil::equate_string_case_insensitive(parent_root, child_root);
        if dynamic {
            roots_equal = parent_root == child_root;
        }
        if !roots_equal {
            return None;
        }
        let (relative, ok) =
            c.trim_prefix(&child[child_root_length..], &parent[parent_root_length..]);
        if !ok
            || (!relative.is_empty()
                && !has_trailing_directory_separator(parent)
                && parent.len() != parent_root_length
                && relative.as_bytes()[0] != DIRECTORY_SEPARATOR as u8)
        {
            return None;
        }
        Some(relative.strip_prefix(DIRECTORY_SEPARATOR).unwrap_or(relative))
    }

    // CommonDirectoryOfFiles returns the deepest directory containing every file.
    // It preserves the spelling of the first file name.
    pub fn common_directory_of_files(&self, file_names: &[RootedFilePath]) -> RootedDirectoryPath {
        let mut common_path_components: Option<Vec<String>> = None;
        for file_name in file_names {
            let mut path_components = get_path_components(file_name.as_string());
            path_components.truncate(path_components.len() - 1);
            if common_path_components.is_none() {
                common_path_components = Some(path_components);
                continue;
            }
            let common = common_path_components.as_mut().unwrap();

            let n = common.len().min(path_components.len());
            let mut effective_case_sensitivity = *self;
            if is_encoded_dynamic_file_name(file_name.as_string())
                || is_encoded_dynamic_file_name(&get_path_from_path_components(common.as_slice()))
            {
                effective_case_sensitivity = CaseSensitivity::CaseSensitive;
                let trimmed = common[0]
                    .strip_suffix(DIRECTORY_SEPARATOR)
                    .unwrap_or(common[0].as_str())
                    .to_string();
                common[0] = trimmed;
                let trimmed = path_components[0]
                    .strip_suffix(DIRECTORY_SEPARATOR)
                    .unwrap_or(path_components[0].as_str())
                    .to_string();
                path_components[0] = trimmed;
            }
            for i in 0..n {
                if effective_case_sensitivity.canonicalize(&common[i])
                    != effective_case_sensitivity.canonicalize(&path_components[i])
                {
                    if i == 0 {
                        return RootedDirectoryPath::default();
                    }
                    common.truncate(i);
                    break;
                }
            }
            if path_components.len() < common.len() {
                common.truncate(path_components.len());
            }
        }
        match common_path_components {
            None => RootedDirectoryPath::default(),
            Some(common) if common.is_empty() => RootedDirectoryPath::default(),
            Some(common) => RootedDirectoryPath::from(get_path_from_path_components(&common)),
        }
    }
}

pub(crate) fn relative_path_from_normalized_paths(
    from: &str,
    to: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let mut from_components = crate::path::path_components(from, get_root_length(from));
    let mut to_components = crate::path::path_components(to, get_root_length(to));
    let mut case_sensitivity = case_sensitivity;
    if is_encoded_dynamic_file_name(from) || is_encoded_dynamic_file_name(to) {
        from_components[0] = from_components[0]
            .strip_suffix(DIRECTORY_SEPARATOR)
            .unwrap_or(&from_components[0])
            .to_string();
        to_components[0] = to_components[0]
            .strip_suffix(DIRECTORY_SEPARATOR)
            .unwrap_or(&to_components[0])
            .to_string();
        if from_components[0] != to_components[0] {
            return to.to_string();
        }
        case_sensitivity = CaseSensitivity::CaseSensitive;
    }
    get_path_from_path_components(&crate::path::get_path_components_relative_to_worker(
        &from_components,
        &to_components,
        case_sensitivity,
    ))
}

pub fn get_common_parent_directories(
    directories: &[RootedDirectoryPath],
    min_components: usize,
    get_components: impl Fn(&RootedDirectoryPath) -> Vec<String>,
    case_sensitivity: CaseSensitivity,
) -> (Vec<RootedDirectoryPath>, FxHashSet<RootedDirectoryPath>) {
    if min_components < 1 {
        panic!("minComponents must be at least 1");
    }
    if directories.is_empty() {
        return (Vec::new(), FxHashSet::default());
    }
    if directories.len() == 1 {
        if reduce_path_components(&get_components(&directories[0])).len() < min_components {
            return (Vec::new(), FxHashSet::from_iter([directories[0].clone()]));
        }
        return (directories.to_vec(), FxHashSet::default());
    }

    let mut ignored: FxHashSet<RootedDirectoryPath> = FxHashSet::default();
    let mut path_components = Vec::with_capacity(directories.len());
    for directory in directories {
        let components = reduce_path_components(&get_components(directory));
        if components.len() < min_components {
            ignored.insert(directory.clone());
        } else {
            path_components.push(components);
        }
    }

    let results = crate::path::get_common_parents_worker(&path_components, min_components, case_sensitivity);
    let parents: Vec<RootedDirectoryPath> = results
        .iter()
        .map(|components| rooted_directory_path_from_absolute(&get_path_from_path_components(components)))
        .collect();
    (parents, ignored)
}

impl RootedDirectoryPath {
    pub fn as_string(&self) -> &str {
        &self.0
    }

    // Compare returns the case-sensitive lexical ordering of the normalized path text.
    pub fn compare(&self, other: &RootedDirectoryPath) -> i32 {
        stringutil::compare_strings_case_sensitive(&self.0, &other.0)
    }

    pub fn as_path(&self) -> RootedPath {
        RootedPath(self.0.clone())
    }

    pub fn base_name(&self) -> &str {
        // PORT: Go delegates to AsPath().BaseName(); inlined because the result
        // borrows from self.
        get_base_file_name_from_normalized(&self.0)
    }

    pub fn components(&self) -> Vec<String> {
        get_path_components(&self.0)
    }

    pub fn contains_lowercase_directory_sequence(&self, sequence: &str) -> bool {
        self.0.contains(sequence)
    }

    pub fn resolve_file(&self, path: &str) -> RootedFilePath {
        if self.is_empty() {
            panic!("cannot resolve from an empty directory name");
        }
        if path.is_empty() {
            return RootedFilePath(self.0.clone());
        }
        if get_encoded_root_length(path) == 0
            && has_url_root(self.as_string())
            && path.contains(['?', '#'])
        {
            panic!("relative URL path must not contain a query or fragment");
        }
        if can_append_path_without_normalization(path) {
            return rooted_file_path_from_resolved(&append_path_to_directory(self, path));
        }
        if is_normalized_slashes_relative_path(path) {
            return rooted_file_path_from_resolved(
                &get_normalized_absolute_path_from_normalized_slashes(&append_path_to_directory(
                    self, path,
                )),
            );
        }
        to_rooted_file_path(path, self)
    }

    pub fn resolve_relative_file(&self, path: &RelativePath) -> RootedFilePath {
        if self.is_empty() {
            panic!("cannot resolve from an empty directory name");
        }
        if path.is_empty() {
            return RootedFilePath(self.0.clone());
        }
        if has_url_root(self.as_string()) && path.as_string().contains(['?', '#']) {
            panic!("relative URL path must not contain a query or fragment");
        }
        if path.requires_resolution() {
            return to_rooted_file_path(path.as_string(), self);
        }
        rooted_file_path_from_resolved(&append_path_to_directory(self, path.as_string()))
    }

    // ResolveFileFromNormalizedRelative resolves an already normalized relative
    // path without revalidating the directory or path.
    pub fn resolve_file_from_normalized_relative(&self, path: &str) -> RootedFilePath {
        if self.is_empty() {
            panic!("cannot resolve from an empty directory path");
        }
        if path.is_empty() {
            panic!("path must not be empty");
        }
        if get_encoded_root_length(path) == 0
            && has_url_root(self.as_string())
            && path.contains(['?', '#'])
        {
            panic!("relative URL path must not contain a query or fragment");
        }
        if is_any_directory_separator(path.as_bytes()[0])
            || normalize_slashes(path) != path
            || has_relative_path_segment(path)
            || has_trailing_directory_separator(path)
        {
            panic!("path must be relative and normalized: {path}");
        }
        rooted_file_path_from_resolved(&append_path_to_directory(self, path))
    }

    pub fn resolve_relative_directory(&self, path: &RelativePath) -> RootedDirectoryPath {
        RootedDirectoryPath(self.resolve_relative_file(path).0)
    }

    pub fn resolve_directory(&self, path: &str) -> RootedDirectoryPath {
        if self.is_empty() {
            panic!("cannot resolve from an empty directory name");
        }
        if path.is_empty() {
            return RootedDirectoryPath(self.0.clone());
        }
        if get_encoded_root_length(path) == 0
            && has_url_root(self.as_string())
            && path.contains(['?', '#'])
        {
            panic!("relative URL path must not contain a query or fragment");
        }
        if can_append_path_without_normalization(path) {
            return RootedDirectoryPath(rooted_file_path_from_resolved(&append_path_to_directory(self, path)).0);
        }
        if is_normalized_slashes_relative_path(path) {
            return RootedDirectoryPath(
                rooted_file_path_from_resolved(
                    &get_normalized_absolute_path_from_normalized_slashes(&append_path_to_directory(
                        self, path,
                    )),
                )
                .0,
            );
        }
        to_rooted_directory_path(path, self)
    }

    pub fn for_each_ancestor_directory<T>(
        &self,
        mut callback: impl FnMut(&RootedDirectoryPath) -> (T, bool),
    ) -> Option<T> {
        let mut directory = self.clone();
        loop {
            let (result, stop) = callback(&directory);
            if stop {
                return Some(result);
            }
            let parent = RootedDirectoryPath::from(get_directory_path_from_normalized(directory.as_string()));
            if parent == directory {
                return None;
            }
            directory = parent;
        }
    }
}

pub(crate) fn rooted_file_path_from_resolved(path: &str) -> RootedFilePath {
    if has_rooted_url_suffix(path) {
        panic!("path must not contain a URL query or fragment");
    }
    RootedFilePath::from(path)
}

// ForEachAncestorDirectoryPathStoppingAtGlobalCache calls callback for
// directory and its ancestors while retaining the normalized rooted invariant.
pub fn for_each_ancestor_directory_path_stopping_at_global_cache<T>(
    global_cache: &RootedDirectoryPath,
    directory: &RootedDirectoryPath,
    mut callback: impl FnMut(&RootedDirectoryPath) -> (T, bool),
) -> Option<T> {
    directory.for_each_ancestor_directory(|ancestor| {
        let (result, stop) = callback(ancestor);
        (result, stop || ancestor == global_cache)
    })
}

pub(crate) fn can_append_path_without_normalization(path: &str) -> bool {
    is_normalized_slashes_relative_path(path)
        && !has_relative_path_segment(path)
        && !has_trailing_directory_separator(path)
}

pub(crate) fn is_normalized_slashes_relative_path(path: &str) -> bool {
    !path.is_empty() && get_encoded_root_length(path) == 0 && !path.contains('\\')
}

pub(crate) fn append_path_to_directory(directory: &RootedDirectoryPath, path: &str) -> String {
    if has_trailing_directory_separator(directory.as_string()) {
        return format!("{}{}", directory.as_string(), path);
    }
    format!("{}/{path}", directory.as_string())
}

pub(crate) fn last_directory_separator(path: &str) -> Option<usize> {
    path.rfind(DIRECTORY_SEPARATOR)
}
