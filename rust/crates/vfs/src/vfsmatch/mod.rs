// Ported from tsc/internal/vfs/vfsmatch/vfsmatch.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// This file implements the glob matching algorithm specified in
// MATCHING_ALGORITHM.md. No regex is used: patterns are compiled to
// component/segment lists and matched with an explicit iterative algorithm.

#[cfg(test)]
mod tests;

use std::sync::Arc;

use tsc_collections::set::Set;
use tsc_tspath::{CaseSensitivity, PathKey, PathPattern, RootedDirectoryPath, RootedFilePath};

use crate::vfs::Vfs;

/// Usage is vfsmatch.Usage.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(i8)]
pub enum Usage {
    Files = 0,
    Directories = 1,
    Exclude = 2,
}

/// UsageFiles / UsageDirectories / UsageExclude.
pub const USAGE_FILES: Usage = Usage::Files;
pub const USAGE_DIRECTORIES: Usage = Usage::Directories;
pub const USAGE_EXCLUDE: Usage = Usage::Exclude;

/// UnlimitedDepth can be passed as the depth argument to indicate there is no depth limit.
pub const UNLIMITED_DEPTH: i64 = i64::MAX;

/// PathPatternInput is the `string | tspath.PathPattern` constraint used by
/// the Go generics.
pub trait PathPatternInput {
    fn as_str(&self) -> &str;
}

impl PathPatternInput for str {
    fn as_str(&self) -> &str {
        self
    }
}
impl PathPatternInput for &str {
    fn as_str(&self) -> &str {
        self
    }
}
impl PathPatternInput for String {
    fn as_str(&self) -> &str {
        self
    }
}
impl PathPatternInput for &String {
    fn as_str(&self) -> &str {
        self
    }
}
impl PathPatternInput for PathPattern {
    fn as_str(&self) -> &str {
        self.as_string()
    }
}
impl PathPatternInput for &PathPattern {
    fn as_str(&self) -> &str {
        self.as_string()
    }
}

/// ReadDirectory is vfsmatch.ReadDirectory.
pub fn read_directory<T: PathPatternInput>(
    host: &Arc<dyn Vfs>,
    path: &RootedDirectoryPath,
    extensions: &[&str],
    excludes: &[T],
    includes: &[T],
    depth: i64,
) -> Vec<RootedFilePath> {
    match_file_names(path, extensions, excludes, includes, depth, host)
}

/// IsImplicitGlob checks if a path component is implicitly a glob.
/// An "includes" path "foo" is implicitly a glob "foo/**/*" if its last
/// component has no extension, and does not contain any glob characters itself.
pub fn is_implicit_glob(last_path_component: &str) -> bool {
    !last_path_component.contains(&['*', '?', '.'][..])
}

const WILDCARD_CHAR_CODES: [char; 2] = ['*', '?'];

fn get_include_base_path(absolute: &str) -> String {
    let wildcard_offset = absolute.find(&WILDCARD_CHAR_CODES[..]);
    match wildcard_offset {
        None => {
            // No "*" or "?" in the path
            if !tsc_tspath::has_extension(absolute) {
                absolute.to_string()
            } else {
                tsc_tspath::remove_trailing_directory_separator(&tsc_tspath::get_directory_path(
                    absolute,
                ))
                .to_string()
            }
        }
        Some(wildcard_offset) => {
            // strings.LastIndex returns -1 when the separator is absent;
            // max(-1, root_length) picks the root in that case.
            let last_sep = absolute[..wildcard_offset]
                .rfind(tsc_tspath::DIRECTORY_SEPARATOR)
                .map(|i| i as i64)
                .unwrap_or(-1);
            let idx = last_sep
                .max(tsc_tspath::get_root_length(absolute) as i64)
                .max(0);
            absolute[..idx as usize].to_string()
        }
    }
}

/// getBasePaths computes the unique non-wildcard base paths amongst the
/// provided include patterns.
fn get_base_paths<T: PathPatternInput>(
    path: &RootedDirectoryPath,
    includes: &[T],
    case_sensitivity: CaseSensitivity,
) -> Vec<RootedDirectoryPath> {
    // Storage for our results in the form of literal paths (e.g. the paths as written by the user).
    let mut base_paths = vec![path.clone()];

    if !includes.is_empty() {
        // Storage for literal base paths amongst the include patterns.
        let mut include_base_paths: Vec<RootedDirectoryPath> = Vec::new();
        for include in includes {
            // We also need to check the relative paths by converting them to absolute and normalizing
            // in case they escape the base path (e.g "..\somedirectory")
            let absolute = if tsc_tspath::is_rooted_disk_path(include.as_str()) {
                tsc_tspath::normalize_path(include.as_str()).into_owned()
            } else {
                tsc_tspath::normalize_path(&tsc_tspath::combine_paths(
                    path.as_string(),
                    &[include.as_str()],
                ))
                .into_owned()
            };
            // Append the literal and canonical candidate base paths.
            include_base_paths.push(tsc_tspath::to_rooted_directory_path(
                &get_include_base_path(&absolute),
                path,
            ));
        }

        // Sort the offsets array using either the literal or canonical path representations.
        include_base_paths.sort_by(|a, b| {
            case_sensitivity
                .compare_paths(&a.as_path(), &b.as_path())
                .cmp(&0)
        });

        // Iterate over each include base path and include unique base paths that are not a
        // subpath of an existing base path
        for include_base_path in include_base_paths {
            if tsc_core::core::every(&base_paths, |basepath: &RootedDirectoryPath| {
                !case_sensitivity.contains_path(basepath, &include_base_path.as_path())
            }) {
                base_paths.push(include_base_path);
            }
        }
    }

    base_paths
}

/// globPattern is a compiled glob pattern for matching file paths without regex.
struct GlobPattern {
    components: Vec<Component>, // path segments to match (e.g., ["src", "**", "*.ts"])
    is_exclude: bool,           // exclude patterns have different matching rules
    case_sensitivity: CaseSensitivity,
    exclude_min_js: bool, // for "files" patterns, exclude .min.js by default
}

/// component is a single path segment in a glob pattern.
/// Examples: "src" (literal), "*" (wildcard), "*.ts" (wildcard), "**" (recursive)
struct Component {
    kind: ComponentKind,
    literal: String,        // for Literal: the exact string to match
    segments: Vec<Segment>, // for Wildcard: parsed wildcard pattern
    /// Include patterns with wildcards skip common package folders (node_modules, etc.)
    skip_package_folders: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ComponentKind {
    Literal,        // exact match (e.g., "src")
    Wildcard,       // contains * or ? (e.g., "*.ts")
    DoubleAsterisk, // ** matches zero or more directories
}

/// segment is a piece of a wildcard component.
/// Example: "*.ts" becomes [Star, Literal(".ts")]
struct Segment {
    kind: SegmentKind,
    literal: String, // only for Literal
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SegmentKind {
    Literal,  // exact text
    Star,     // * matches any chars except /
    Question, // ? matches single char except /
}

/// compileGlobPattern compiles a glob spec (e.g., "src/**/*.ts") into a pattern.
/// Returns None if the pattern would match nothing.
fn compile_glob_pattern(
    spec: &str,
    base_path: &RootedDirectoryPath,
    usage: Usage,
    case_sensitivity: CaseSensitivity,
) -> Option<GlobPattern> {
    let mut parts = tsc_tspath::get_normalized_path_components(spec, base_path.as_string());
    let mut case_sensitivity = case_sensitivity;
    if tsc_tspath::is_encoded_dynamic_file_name(&parts[0]) {
        case_sensitivity = CaseSensitivity::CaseSensitive;
    }

    // "src/**" without a filename matches nothing (for include patterns)
    if usage != Usage::Exclude && parts.last().map(|s| s.as_str()) == Some("**") {
        return None;
    }

    // Normalize root: "/home/" -> "/home"
    parts[0] = tsc_tspath::remove_trailing_directory_separator(&parts[0]).to_string();
    if tsc_tspath::is_encoded_dynamic_file_name(&parts[0]) {
        let root_parts: Vec<String> = parts[0].split('/').map(|s| s.to_string()).collect();
        parts = root_parts
            .into_iter()
            .chain(parts[1..].iter().cloned())
            .collect();
    }

    // Directories implicitly match all files: "src" -> "src/**/*"
    if is_implicit_glob(parts.last().map(|s| s.as_str()).unwrap_or("")) {
        parts.push("**".to_string());
        parts.push("*".to_string());
    }

    let is_include = usage != Usage::Exclude;
    let components = parts
        .iter()
        .map(|part| parse_component(part, is_include))
        .collect();
    Some(GlobPattern {
        is_exclude: usage == Usage::Exclude,
        case_sensitivity,
        exclude_min_js: usage == Usage::Files,
        components,
    })
}

/// parseComponent converts a path segment string into a component.
fn parse_component(s: &str, is_include: bool) -> Component {
    if s == "**" {
        return Component {
            kind: ComponentKind::DoubleAsterisk,
            literal: String::new(),
            segments: Vec::new(),
            skip_package_folders: false,
        };
    }
    if !s.contains(&['*', '?'][..]) {
        return Component {
            kind: ComponentKind::Literal,
            literal: s.to_string(),
            segments: Vec::new(),
            skip_package_folders: false,
        };
    }
    Component {
        kind: ComponentKind::Wildcard,
        literal: String::new(),
        segments: parse_segments(s),
        skip_package_folders: is_include,
    }
}

/// parseSegments breaks "*.ts" into [Star, Literal(".ts")]
fn parse_segments(s: &str) -> Vec<Segment> {
    let bytes = s.as_bytes();
    let mut result = Vec::new();
    let mut start = 0;
    for i in 0..bytes.len() {
        match bytes[i] {
            b'*' | b'?' => {
                if i > start {
                    result.push(Segment {
                        kind: SegmentKind::Literal,
                        literal: s[start..i].to_string(),
                    });
                }
                if bytes[i] == b'*' {
                    result.push(Segment {
                        kind: SegmentKind::Star,
                        literal: String::new(),
                    });
                } else {
                    result.push(Segment {
                        kind: SegmentKind::Question,
                        literal: String::new(),
                    });
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < s.len() {
        result.push(Segment {
            kind: SegmentKind::Literal,
            literal: s[start..].to_string(),
        });
    }
    result
}

impl GlobPattern {
    /// matches returns true if path matches this pattern.
    fn matches(&self, path: &str) -> bool {
        self.match_path_parts(path, "", 0, 0, false)
    }

    /// matchesParts returns true if prefix+suffix matches this pattern.
    /// This avoids allocating a combined string for common call sites where
    /// prefix ends with '/'.
    fn matches_parts(&self, prefix: &str, suffix: &str) -> bool {
        self.match_path_parts(prefix, suffix, 0, 0, false)
    }

    /// matchesPrefixParts returns true if files under prefix+suffix could match.
    fn matches_prefix_parts(&self, prefix: &str, suffix: &str) -> bool {
        self.match_path_parts(prefix, suffix, 0, 0, true)
    }

    /// matchPathParts operates on a virtual path formed by prefix+suffix.
    /// Offsets are in the combined string.
    fn match_path_parts(
        &self,
        prefix: &str,
        suffix: &str,
        mut path_offset: usize,
        mut comp_idx: usize,
        prefix_only: bool,
    ) -> bool {
        loop {
            let (path_part, next_offset, ok) = next_path_part_parts(prefix, suffix, path_offset);
            if !ok {
                if prefix_only {
                    return true;
                }
                return self.pattern_satisfied(comp_idx);
            }

            if comp_idx >= self.components.len() {
                return self.is_exclude && !prefix_only;
            }

            let comp = &self.components[comp_idx];
            match comp.kind {
                ComponentKind::DoubleAsterisk => {
                    if self.match_path_parts(prefix, suffix, path_offset, comp_idx + 1, prefix_only)
                    {
                        return true;
                    }
                    if !self.is_exclude
                        && (is_hidden_path(&path_part) || is_package_folder(&path_part))
                    {
                        return false;
                    }
                    path_offset = next_offset;
                    continue;
                }
                ComponentKind::Literal => {
                    if !self.strings_equal(&comp.literal, &path_part) {
                        return false;
                    }
                }
                ComponentKind::Wildcard => {
                    if comp.skip_package_folders && is_package_folder(&path_part) {
                        return false;
                    }
                    if !self.match_wildcard(&comp.segments, &path_part) {
                        return false;
                    }
                }
            }

            path_offset = next_offset;
            comp_idx += 1;
        }
    }

    /// patternSatisfied checks if remaining pattern components can match empty input.
    fn pattern_satisfied(&self, comp_idx: usize) -> bool {
        // A pattern is satisfied when remaining components can match empty input.
        // For both include and exclude patterns, only trailing "**" components may match nothing.
        self.components[comp_idx..]
            .iter()
            .all(|c| c.kind == ComponentKind::DoubleAsterisk)
    }

    /// matchWildcard matches a path component against wildcard segments.
    fn match_wildcard(&self, segs: &[Segment], s: &str) -> bool {
        // Include patterns: wildcards at start cannot match hidden files
        if !self.is_exclude
            && !segs.is_empty()
            && is_hidden_path(s)
            && (segs[0].kind == SegmentKind::Star || segs[0].kind == SegmentKind::Question)
        {
            return false;
        }

        // Fast path: single * followed by literal suffix (e.g., "*.ts")
        if segs.len() == 2
            && segs[0].kind == SegmentKind::Star
            && segs[1].kind == SegmentKind::Literal
        {
            let suffix = &segs[1].literal;
            if s.len() < suffix.len()
                || !self.bytes_equal(suffix.as_bytes(), &s.as_bytes()[s.len() - suffix.len()..])
            {
                return false;
            }
            return self.should_include_min_js(s, segs);
        }

        self.match_segments(segs, s) && self.should_include_min_js(s, segs)
    }

    /// matchSegments matches segments against string s using an iterative algorithm.
    /// This avoids exponential backtracking by tracking only the last star position.
    /// The algorithm is O(n*m) where n is the string length and m is pattern length.
    fn match_segments(&self, segs: &[Segment], s: &str) -> bool {
        let bytes = s.as_bytes();
        let (mut seg_idx, mut s_idx) = (0usize, 0usize);
        let (mut star_seg_idx, mut star_s_idx) = (-1i64, 0usize);

        while s_idx < s.len() {
            if seg_idx < segs.len() {
                let seg = &segs[seg_idx];
                match seg.kind {
                    SegmentKind::Literal => {
                        let end = s_idx + seg.literal.len();
                        // PORT: Go slices bytes (never panics); compare on the
                        // byte slice so a multi-byte rune can't split a char
                        // boundary mid-comparison.
                        if end <= s.len()
                            && self.bytes_equal(seg.literal.as_bytes(), &bytes[s_idx..end])
                        {
                            s_idx = end;
                            seg_idx += 1;
                            continue;
                        }
                    }
                    SegmentKind::Question => {
                        if bytes[s_idx] != b'/' {
                            // utf8.DecodeRuneInString — advance one rune.
                            s_idx += rune_len(&s[s_idx..]);
                            seg_idx += 1;
                            continue;
                        }
                    }
                    SegmentKind::Star => {
                        // Record star position for backtracking, then try matching zero chars.
                        star_seg_idx = seg_idx as i64;
                        star_s_idx = s_idx;
                        seg_idx += 1;
                        continue;
                    }
                }
            }

            // Current segment didn't match. Backtrack to last star if possible.
            if star_seg_idx >= 0 && star_s_idx < s.len() && bytes[star_s_idx] != b'/' {
                // Star consumes one more character (rune), retry from segment after star.
                star_s_idx += rune_len(&s[star_s_idx..]);
                s_idx = star_s_idx;
                seg_idx = star_seg_idx as usize + 1;
                continue;
            }

            return false;
        }

        // Consume any trailing stars.
        while seg_idx < segs.len() && segs[seg_idx].kind == SegmentKind::Star {
            seg_idx += 1;
        }
        seg_idx >= segs.len()
    }

    fn should_include_min_js(&self, filename: &str, segs: &[Segment]) -> bool {
        if !self.exclude_min_js {
            return true;
        }

        // Preserve legacy behavior:
        // - When matching is case-sensitive, only the exact ".min.js" suffix is excluded by default.
        // - When matching is case-insensitive, any casing variant is excluded by default.
        if !self.has_min_js_suffix(filename) {
            return true;
        }
        // Allow when the user's pattern explicitly references the .min. suffix.
        if self.pattern_mentions_min_suffix(segs) {
            return true;
        }
        false
    }

    fn has_min_js_suffix(&self, filename: &str) -> bool {
        if self.case_sensitivity.is_case_sensitive() {
            return filename.ends_with(".min.js");
        }
        const MIN_JS: &str = ".min.js";
        if filename.len() < MIN_JS.len() {
            return false;
        }
        // strings.EqualFold on the suffix.
        filename[filename.len() - MIN_JS.len()..].eq_ignore_ascii_case(MIN_JS)
    }

    fn pattern_mentions_min_suffix(&self, segs: &[Segment]) -> bool {
        for seg in segs {
            if seg.kind != SegmentKind::Literal {
                continue;
            }
            let lit = if self.case_sensitivity.is_case_insensitive() {
                seg.literal.to_lowercase()
            } else {
                seg.literal.clone()
            };
            if lit.contains(".min.js") || lit.contains(".min.") {
                return true;
            }
        }
        false
    }

    /// stringsEqual compares strings with appropriate case sensitivity.
    fn strings_equal(&self, a: &str, b: &str) -> bool {
        self.bytes_equal(a.as_bytes(), b.as_bytes())
    }

    /// bytesEqual compares byte slices with appropriate case sensitivity.
    /// Invalid UTF-8 (e.g. a slice ending inside a multi-byte rune) compares
    /// unequal unless byte-identical — matching Go, where EqualFold decodes
    /// invalid bytes to RuneError and can never equal a valid literal.
    fn bytes_equal(&self, a: &[u8], b: &[u8]) -> bool {
        if self.case_sensitivity.is_case_sensitive() {
            a == b
        } else {
            match (std::str::from_utf8(a), std::str::from_utf8(b)) {
                (Ok(a), Ok(b)) => {
                    // strings.EqualFold — ASCII fast path plus full Unicode folding.
                    // PORT: uses tsc-stringutil's comparer semantics via eq_ignore_ascii_case
                    // for ASCII; non-ASCII fold is approximated by char-wise lowercase
                    // comparison (Go's EqualFold is rune-wise simple folding).
                    a.eq_ignore_ascii_case(b) || fold_equal(a, b)
                }
                _ => a == b,
            }
        }
    }
}

/// rune_len is utf8.DecodeRuneInString's size result for a valid &str.
fn rune_len(s: &str) -> usize {
    s.chars().next().map(|c| c.len_utf8()).unwrap_or(1)
}

/// fold_equal approximates strings.EqualFold (rune-wise simple case folding).
fn fold_equal(a: &str, b: &str) -> bool {
    let mut ac = a.chars();
    let mut bc = b.chars();
    loop {
        match (ac.next(), bc.next()) {
            (None, None) => return true,
            (Some(x), Some(y)) => {
                if x != y && !chars_fold_equal(x, y) {
                    return false;
                }
            }
            _ => return false,
        }
    }
}

fn chars_fold_equal(x: char, y: char) -> bool {
    // Go compares via unicode.SimpleFold orbit — approximate with 1:1
    // upper/lower case mappings (skipping multi-char folds, which SimpleFold
    // also skips since SimpleFold is a rune->rune mapping).
    let xu = x.to_uppercase().next().unwrap_or(x);
    let yu = y.to_uppercase().next().unwrap_or(y);
    xu == yu || x.to_lowercase().next().unwrap_or(x) == y.to_lowercase().next().unwrap_or(y)
}

/// nextPathPart extracts the next path component from path starting at offset.
fn next_path_part_single(s: &str, offset: usize) -> (String, usize, bool) {
    let bytes = s.as_bytes();
    if offset >= s.len() {
        return (String::new(), offset, false);
    }
    if offset == 0 && !s.is_empty() && bytes[0] == b'/' {
        return (String::new(), 1, true);
    }
    let mut offset = offset;
    while offset < s.len() && bytes[offset] == b'/' {
        offset += 1;
    }
    if offset >= s.len() {
        return (String::new(), offset, false);
    }
    let rest = &s[offset..];
    match rest.find('/') {
        Some(idx) => (rest[..idx].to_string(), offset + idx, true),
        None => (rest.to_string(), s.len(), true),
    }
}

fn next_path_part_parts(prefix: &str, suffix: &str, offset: usize) -> (String, usize, bool) {
    // Fast paths: keep the hot single-string scan tight.
    if suffix.is_empty() {
        return next_path_part_single(prefix, offset);
    }
    if prefix.is_empty() {
        return next_path_part_single(suffix, offset);
    }

    // For matchFilesNoRegex call sites, prefix is a directory path ending in '/',
    // and suffix is a single entry name (no '/'). That makes this significantly
    // simpler than a general-purpose "virtual concatenation" scanner.

    let total_len = prefix.len() + suffix.len();
    if offset >= total_len {
        return (String::new(), offset, false);
    }

    // Handle leading slash (root of absolute path)
    if offset == 0 && prefix.as_bytes()[0] == b'/' {
        return (String::new(), 1, true);
    }

    // Scan within prefix.
    if offset < prefix.len() {
        let mut offset = offset;
        let bytes = prefix.as_bytes();
        while offset < prefix.len() && bytes[offset] == b'/' {
            offset += 1;
        }
        if offset < prefix.len() {
            let rest = &prefix[offset..];
            let idx = rest.find('/').unwrap_or(rest.len());
            // idx is guaranteed found for the call sites we care about because
            // prefix ends in '/'; unwrap_or keeps this total-correct anyway.
            return (rest[..idx].to_string(), offset + idx, true);
        }
        // Fall through into suffix region — offset is now prefix.len().
        let s_off = offset - prefix.len();
        if s_off >= suffix.len() {
            return (String::new(), offset, false);
        }
        return (suffix[s_off..].to_string(), total_len, true);
    }

    // Scan suffix: it's a single component.
    let s_off = offset - prefix.len();
    if s_off >= suffix.len() {
        return (String::new(), offset, false);
    }
    (suffix[s_off..].to_string(), total_len, true)
}

/// isHiddenPath checks if a path component is hidden (starts with dot).
fn is_hidden_path(name: &str) -> bool {
    name.starts_with('.')
}

/// isPackageFolder checks if name is a common package folder (node_modules, etc.)
fn is_package_folder(name: &str) -> bool {
    match name.len() {
        x if x == "node_modules".len() => name.eq_ignore_ascii_case("node_modules"),
        x if x == "jspm_packages".len() => name.eq_ignore_ascii_case("jspm_packages"),
        x if x == "bower_components".len() => name.eq_ignore_ascii_case("bower_components"),
        _ => false,
    }
}

/// globMatcher combines include and exclude patterns for file matching.
struct GlobMatcher {
    includes: Vec<GlobPattern>,
    excludes: Vec<GlobPattern>,
    had_includes: bool, // true if include specs were provided (even if none compiled)
}

fn new_glob_matcher<T: PathPatternInput>(
    include_specs: &[T],
    exclude_specs: &[T],
    base_path: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    usage: Usage,
) -> GlobMatcher {
    let mut m = GlobMatcher {
        had_includes: !include_specs.is_empty(),
        includes: Vec::with_capacity(include_specs.len()),
        excludes: Vec::with_capacity(exclude_specs.len()),
    };

    for spec in include_specs {
        if let Some(p) = compile_glob_pattern(spec.as_str(), base_path, usage, case_sensitivity) {
            m.includes.push(p);
        }
    }
    for spec in exclude_specs {
        if let Some(p) =
            compile_glob_pattern(spec.as_str(), base_path, Usage::Exclude, case_sensitivity)
        {
            m.excludes.push(p);
        }
    }
    m
}

impl GlobMatcher {
    /// matchesFileParts checks if prefix+suffix matches against the glob patterns.
    /// Returns the index of the matching include pattern and true if matched.
    fn matches_file_parts(&self, prefix: &str, suffix: &str) -> Option<usize> {
        for e in &self.excludes {
            if e.matches_parts(prefix, suffix) {
                return None;
            }
        }
        if self.includes.is_empty() {
            if self.had_includes {
                return None;
            }
            return Some(0);
        }
        for (i, p) in self.includes.iter().enumerate() {
            if p.matches_parts(prefix, suffix) {
                return Some(i);
            }
        }
        None
    }

    /// matchesDirectoryParts checks if files under the directory prefix+suffix
    /// could match any pattern.
    fn matches_directory_parts(&self, prefix: &str, suffix: &str) -> bool {
        for e in &self.excludes {
            if e.matches_parts(prefix, suffix) {
                return false;
            }
        }
        if self.includes.is_empty() {
            return !self.had_includes;
        }
        for p in &self.includes {
            if p.matches_prefix_parts(prefix, suffix) {
                return true;
            }
        }
        false
    }
}

/// globVisitor traverses directories matching files against glob patterns.
struct GlobVisitor<'a> {
    host: &'a Arc<dyn Vfs>,
    file_matcher: GlobMatcher,
    directory_matcher: GlobMatcher,
    extensions: Vec<String>,
    case_sensitivity: CaseSensitivity,
    visited: Set<PathKey>,
    results: Vec<Vec<RootedFilePath>>,
}

impl GlobVisitor<'_> {
    /// visit walks a directory tree, collecting files that match the glob patterns.
    /// resolved_real_path, when non-empty, is the already-resolved real path for this
    /// directory (computed incrementally from the parent). When empty, realpath is
    /// called to resolve symlinks.
    fn visit(
        &mut self,
        absolute_path: &RootedDirectoryPath,
        mut depth: i64,
        resolved_real_path: &RootedDirectoryPath,
    ) {
        // Detect symlink cycles
        let real_path = if !resolved_real_path.as_string().is_empty() {
            resolved_real_path.clone()
        } else {
            tsc_tspath::rooted_directory_path_from_path(
                self.host.realpath(&absolute_path.as_path()),
            )
        };
        let canonical_path = self.case_sensitivity.path_key(&real_path.as_path());
        if self.visited.has(&canonical_path) {
            return;
        }
        self.visited.add(canonical_path);

        let entries = self.host.get_accessible_entries(absolute_path);

        let abs_prefix =
            tsc_tspath::ensure_trailing_directory_separator(absolute_path.as_string()).into_owned();

        let ext_refs: Vec<&str> = self.extensions.iter().map(String::as_str).collect();
        for file in &entries.files {
            if !ext_refs.is_empty() && !tsc_tspath::file_extension_is_one_of(file, &ext_refs) {
                continue;
            }
            if let Some(idx) = self.file_matcher.matches_file_parts(&abs_prefix, file) {
                self.results[idx].push(absolute_path.resolve_file(file));
            }
        }

        if depth != UNLIMITED_DEPTH {
            depth -= 1;
            if depth == 0 {
                return;
            }
        }

        for dir in &entries.directories {
            if !self
                .directory_matcher
                .matches_directory_parts(&abs_prefix, dir)
            {
                continue;
            }
            let abs_dir = absolute_path.resolve_directory(dir);
            let child_real_path = if let Some(symlinks) = &entries.symlinks {
                if !symlinks.contains(dir) {
                    // Non-symlink directory: compute realpath incrementally.
                    real_path.resolve_directory(dir)
                } else {
                    // Symlink directory; leave empty to force realpath call.
                    RootedDirectoryPath::default()
                }
            } else {
                // If symlinks is None, the FS doesn't track symlinks;
                // leave childRealPath empty to call Realpath (preserving old behavior).
                RootedDirectoryPath::default()
            };
            self.visit(&abs_dir, depth, &child_real_path);
        }
    }
}

fn match_file_names<T: PathPatternInput>(
    path: &RootedDirectoryPath,
    extensions: &[&str],
    excludes: &[T],
    includes: &[T],
    depth: i64,
    host: &Arc<dyn Vfs>,
) -> Vec<RootedFilePath> {
    let case_sensitivity = host.case_sensitivity();

    let file_matcher = new_glob_matcher(includes, excludes, path, case_sensitivity, Usage::Files);
    let directory_matcher = new_glob_matcher(
        includes,
        excludes,
        path,
        case_sensitivity,
        Usage::Directories,
    );

    let result_count = file_matcher.includes.len().max(1);
    let mut v = GlobVisitor {
        host,
        file_matcher,
        directory_matcher,
        extensions: extensions.iter().map(|s| s.to_string()).collect(),
        case_sensitivity,
        visited: Set::new(),
        results: vec![Vec::new(); result_count],
    };

    let empty = RootedDirectoryPath::default();
    for base_path in get_base_paths(path, includes, case_sensitivity) {
        v.visit(&base_path, depth, &empty);
    }

    // Fast path: a single include bucket (or no includes) doesn't need flattening.
    if v.results.len() == 1 {
        return v.results.pop().unwrap_or_default();
    }
    tsc_core::core::flatten(&v.results)
}

/// SpecMatcher wraps multiple glob patterns for matching paths.
pub struct SpecMatcher {
    patterns: Vec<GlobPattern>,
}

impl SpecMatcher {
    /// MatchString returns true if any pattern matches the path.
    pub fn match_string(&self, path: &str) -> bool {
        self.patterns.iter().any(|p| p.matches(path))
    }

    pub fn match_file_name(&self, path: &RootedFilePath) -> bool {
        self.match_string(path.as_string())
    }

    /// MatchIndex returns the index of the first matching pattern, or -1.
    pub fn match_index(&self, path: &str) -> i64 {
        for (i, p) in self.patterns.iter().enumerate() {
            if p.matches(path) {
                return i as i64;
            }
        }
        -1
    }

    pub fn match_file_name_index(&self, path: &RootedFilePath) -> i64 {
        self.match_index(path.as_string())
    }
}

/// new_spec_matcher creates a matcher for one or more glob specs.
/// It returns a matcher that can test if paths match any of the patterns.
pub fn new_spec_matcher<T: PathPatternInput>(
    specs: &[T],
    base_path: &RootedDirectoryPath,
    usage: Usage,
    case_sensitivity: CaseSensitivity,
) -> Option<SpecMatcher> {
    if specs.is_empty() {
        return None;
    }
    let mut patterns = Vec::with_capacity(specs.len());
    for spec in specs {
        if let Some(p) = compile_glob_pattern(spec.as_str(), base_path, usage, case_sensitivity) {
            patterns.push(p);
        }
    }
    if patterns.is_empty() {
        return None;
    }
    Some(SpecMatcher { patterns })
}
