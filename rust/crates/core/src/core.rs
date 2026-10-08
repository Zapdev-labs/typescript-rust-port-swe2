// Ported from tsc/internal/core/core.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's by-value `func(T)` callbacks become `&T`/`FnMut(&T)` borrows
// throughout this file (T is usually a pointer/id type whose element access
// is what callers need). Functions that return the input slice unchanged
// return `Cow::Borrowed` so `same()` keeps working. Go's `iter.Seq`
// parameters become `impl Iterator`/`impl IntoIterator` — early exit is
// naturally supported since pull iterators are consumed lazily. Go's nil
// slices lose their nil-ness at `&[T]` boundaries; call sites that rely on
// nil-vs-empty wrap in `Option<&[T]>` themselves. `int` parameters that can
// be negative (star_index, find_index, splice start/deleteCount) stay `i32`;
// pure slice indices are `usize`.

use std::borrow::Cow;
use std::cell::Cell;
use std::cell::RefCell;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustc_hash::FxHashMap;
use serde::Serialize;
use tsc_debug as debug;
use tsc_json as json;
use tsc_stringutil as stringutil;
use tsc_tspath as tspath;

use crate::options_generated::CompilerOptions;
use crate::scriptkind::ScriptKind;
use crate::text::TextPos;

// PORT: Go calls runtime/debug.SetMaxStack(n); Rust has no equivalent runtime
// stack limit. The value is stored so thread-spawn sites can pass it to
// std::thread::Builder::stack_size; debug_stack_limit() exposes it.
static DEBUG_STACK_LIMIT: AtomicUsize = AtomicUsize::new(0);

pub fn apply_debug_stack_limit() {
    let Ok(v) = std::env::var("TS_GO_DEBUG_STACK_LIMIT") else {
        return;
    };
    if v.is_empty() {
        return;
    }
    let Ok(n) = v.parse::<usize>() else {
        return;
    };
    if n == 0 {
        return;
    }
    DEBUG_STACK_LIMIT.store(n, Ordering::Relaxed);
}

// PORT: not in Go — exposes the parsed TS_GO_DEBUG_STACK_LIMIT for
// thread::Builder::stack_size.
pub fn debug_stack_limit() -> Option<usize> {
    match DEBUG_STACK_LIMIT.load(Ordering::Relaxed) {
        0 => None,
        n => Some(n),
    }
}

pub fn filter<'a, T: Clone>(slice: &'a [T], mut f: impl FnMut(&T) -> bool) -> Cow<'a, [T]> {
    for (i, value) in slice.iter().enumerate() {
        if !f(value) {
            let mut result = slice[..i].to_vec();
            for value in &slice[i + 1..] {
                if f(value) {
                    result.push(value.clone());
                }
            }
            return Cow::Owned(result);
        }
    }
    Cow::Borrowed(slice)
}

// PORT: Go's `iter.Seq[T]` becomes a lazy iterator over `&T`.
pub fn filter_seq<'a, T: 'a>(
    slice: &'a [T],
    mut f: impl FnMut(&T) -> bool + 'a,
) -> impl Iterator<Item = &'a T> {
    slice.iter().filter(move |value| f(value))
}

pub fn filter_index<'a, T: Clone>(
    slice: &'a [T],
    mut f: impl FnMut(&T, usize, &[T]) -> bool,
) -> Cow<'a, [T]> {
    for (i, value) in slice.iter().enumerate() {
        if !f(value, i, slice) {
            let mut result = slice[..i].to_vec();
            for (i, value) in slice.iter().enumerate().skip(i + 1) {
                if f(value, i, slice) {
                    result.push(value.clone());
                }
            }
            return Cow::Owned(result);
        }
    }
    Cow::Borrowed(slice)
}

pub fn map<T, U>(slice: &[T], mut f: impl FnMut(&T) -> U) -> Vec<U> {
    slice.iter().map(&mut f).collect()
}

pub fn try_map<T, U, E>(slice: &[T], mut f: impl FnMut(&T) -> Result<U, E>) -> Result<Vec<U>, E> {
    if slice.is_empty() {
        return Ok(Vec::new());
    }
    let mut result = Vec::with_capacity(slice.len());
    for value in slice {
        result.push(f(value)?);
    }
    Ok(result)
}

pub fn map_index<T, U>(slice: &[T], mut f: impl FnMut(&T, usize) -> U) -> Vec<U> {
    slice
        .iter()
        .enumerate()
        .map(|(i, value)| f(value, i))
        .collect()
}

// PORT: Go's `mapped != *new(U)` becomes `Option<U>`; the callback returns
// Some(value) to keep it.
pub fn map_non_nil<T, U>(slice: &[T], mut f: impl FnMut(&T) -> Option<U>) -> Vec<U> {
    slice.iter().filter_map(&mut f).collect()
}

// PORT: Go's `func(T) (U, bool)` becomes `Option<U>`; identical body to
// map_non_nil (kept as a separate name to mirror Go).
pub fn map_filtered<T, U>(slice: &[T], mut f: impl FnMut(&T) -> Option<U>) -> Vec<U> {
    slice.iter().filter_map(&mut f).collect()
}

pub fn flat_map<T, U>(slice: &[T], mut f: impl FnMut(&T) -> Vec<U>) -> Vec<U> {
    let mut result = Vec::new();
    for value in slice {
        let mapped = f(value);
        result.extend(mapped);
    }
    result
}

pub fn same_map<'a, T: PartialEq + Clone>(
    slice: &'a [T],
    mut f: impl FnMut(&T) -> T,
) -> Cow<'a, [T]> {
    for (i, value) in slice.iter().enumerate() {
        let mapped = f(value);
        if mapped != *value {
            let mut result = Vec::with_capacity(slice.len());
            result.extend_from_slice(&slice[..i]);
            result.push(mapped);
            for value in &slice[i + 1..] {
                result.push(f(value));
            }
            return Cow::Owned(result);
        }
    }
    Cow::Borrowed(slice)
}

pub fn same_map_index<'a, T: PartialEq + Clone>(
    slice: &'a [T],
    mut f: impl FnMut(&T, usize) -> T,
) -> Cow<'a, [T]> {
    for (i, value) in slice.iter().enumerate() {
        let mapped = f(value, i);
        if mapped != *value {
            let mut result = Vec::with_capacity(slice.len());
            result.extend_from_slice(&slice[..i]);
            result.push(mapped);
            for (j, value) in slice.iter().enumerate().skip(i + 1) {
                result.push(f(value, j));
            }
            return Cow::Owned(result);
        }
    }
    Cow::Borrowed(slice)
}

pub fn same<T>(s1: &[T], s2: &[T]) -> bool {
    if s1.len() == s2.len() {
        return s1.is_empty() || s1.as_ptr() == s2.as_ptr();
    }
    false
}

pub fn some<T>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> bool {
    slice.iter().any(&mut f)
}

pub fn every<T>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> bool {
    slice.iter().all(&mut f)
}

// PORT: Go's variadic `funcs ...func(T) bool` becomes a Vec of boxed
// closures.
#[allow(clippy::type_complexity)]
pub fn or<T>(funcs: Vec<Box<dyn Fn(&T) -> bool>>) -> impl Fn(&T) -> bool {
    move |input| funcs.iter().any(|f| f(input))
}

pub fn find<T: Clone>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> Option<T> {
    slice.iter().find(|value| f(value)).cloned()
}

pub fn find_last<T: Clone>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> Option<T> {
    slice.iter().rev().find(|value| f(value)).cloned()
}

pub fn find_index<T>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> i32 {
    for (i, value) in slice.iter().enumerate() {
        if f(value) {
            return i as i32;
        }
    }
    -1
}

pub fn find_last_index<T>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> i32 {
    for (i, value) in slice.iter().enumerate().rev() {
        if f(value) {
            return i as i32;
        }
    }
    -1
}

// PORT: Go returns the zero value of T when the slice is empty; Rust returns
// Option<T>.
pub fn first_or_nil<T: Clone>(slice: &[T]) -> Option<T> {
    slice.first().cloned()
}

pub fn last_or_nil<T: Clone>(slice: &[T]) -> Option<T> {
    slice.last().cloned()
}

pub fn element_or_nil<T: Clone>(slice: &[T], index: usize) -> Option<T> {
    slice.get(index).cloned()
}

// PORT: `iter.Seq` becomes `Option<impl Iterator>` (None == nil seq).
pub fn first_or_nil_seq<T>(seq: Option<impl Iterator<Item = T>>) -> Option<T> {
    seq.and_then(|mut seq| seq.next())
}

// PORT: Go's `mapped != *new(U)` becomes `Option<U>`.
pub fn first_non_nil<T, U>(slice: &[T], mut f: impl FnMut(&T) -> Option<U>) -> Option<U> {
    slice.iter().find_map(&mut f)
}

// PORT: Go's variadic `values ...T` becomes IntoIterator; the zero value
// becomes `T::default()`.
pub fn first_non_zero<T: Default + PartialEq>(values: impl IntoIterator<Item = T>) -> T {
    values
        .into_iter()
        .find(|value| *value != T::default())
        .unwrap_or_default()
}

pub fn concatenate<'a, T: Clone>(s1: &'a [T], s2: &'a [T]) -> Cow<'a, [T]> {
    if s2.is_empty() {
        return Cow::Borrowed(s1);
    }
    if s1.is_empty() {
        return Cow::Borrowed(s2);
    }
    let mut result = Vec::with_capacity(s1.len() + s2.len());
    result.extend_from_slice(s1);
    result.extend_from_slice(s2);
    Cow::Owned(result)
}

pub fn splice<'a, T: Clone>(
    s1: &'a [T],
    start: i32,
    delete_count: i32,
    items: &[T],
) -> Cow<'a, [T]> {
    let len = s1.len() as i32;
    let mut start = start;
    if start < 0 {
        start += len;
    }
    if start < 0 {
        start = 0;
    }
    if start > len {
        start = len;
    }
    let delete_count = delete_count.max(0);
    let end = (start + delete_count.max(0)).min(len);
    if start == end && items.is_empty() {
        return Cow::Borrowed(s1);
    }
    let mut result = Vec::with_capacity(s1.len() + items.len());
    result.extend_from_slice(&s1[..start as usize]);
    result.extend_from_slice(items);
    result.extend_from_slice(&s1[end as usize..]);
    Cow::Owned(result)
}

pub fn count_where<T>(slice: &[T], mut f: impl FnMut(&T) -> bool) -> i32 {
    let mut count = 0;
    for value in slice {
        if f(value) {
            count += 1;
        }
    }
    count
}

pub fn replace_element<T: Clone>(slice: &[T], i: usize, t: T) -> Vec<T> {
    let mut result = slice.to_vec();
    result[i] = t;
    result
}

pub fn insert_sorted<T: Clone>(slice: &[T], element: T, cmp: impl Fn(&T, &T) -> i32) -> Vec<T> {
    let i = slice.partition_point(|v| cmp(v, &element) < 0);
    let mut result = Vec::with_capacity(slice.len() + 1);
    result.extend_from_slice(&slice[..i]);
    result.push(element);
    result.extend_from_slice(&slice[i..]);
    result
}

// MinAllFunc returns all minimum elements from xs according to the comparison function cmp.
pub fn min_all_func<T: Clone>(xs: &[T], cmp: impl Fn(&T, &T) -> i32) -> Vec<T> {
    if xs.is_empty() {
        return Vec::new();
    }

    let mut m = &xs[0];
    let mut mins = vec![m.clone()];

    for x in &xs[1..] {
        let c = cmp(x, m);
        if c < 0 {
            m = x;
            mins.clear();
            mins.push(x.clone());
        } else if c == 0 {
            mins.push(x.clone());
        }
    }

    mins
}

pub fn append_if_unique<'a, T: PartialEq + Clone>(slice: &'a [T], element: T) -> Cow<'a, [T]> {
    if slice.contains(&element) {
        return Cow::Borrowed(slice);
    }
    let mut result = slice.to_vec();
    result.push(element);
    Cow::Owned(result)
}

// PORT: Go's nilable `create func() T` becomes a `Cell<Option<F>>` inside the
// memoized closure; Go returns the stored value by copy, so T: Clone. Callers
// that need Sync should wrap in std::sync::OnceLock themselves (this mirrors
// Go's non-thread-safe closure-based Memoize).
pub fn memoize<T: Clone, F: FnOnce() -> T>(create: F) -> impl FnMut() -> T {
    let create = Cell::new(Some(create));
    let mut value: Option<T> = None;
    move || {
        if let Some(create) = create.take() {
            value = Some(create());
        }
        // value is always Some after the first call
        value.clone().expect("memoize: no value")
    }
}

// Returns whenTrue if b is true; otherwise, returns whenFalse. IfElse should only be used when branches are either
// constant or precomputed as both branches will be evaluated regardless as to the value of b.
pub fn if_else<T>(b: bool, when_true: T, when_false: T) -> T {
    if b { when_true } else { when_false }
}

// Returns value if value is not the zero value of T; Otherwise, returns defaultValue. OrElse should only be used when
// defaultValue is constant or precomputed as its argument will be evaluated regardless as to the content of value.
pub fn or_else<T: Default + PartialEq>(value: T, default_value: T) -> T {
    if value != T::default() {
        return value;
    }
    default_value
}

// Returns `a` if `a` is not `nil`; Otherwise, returns `b`. Coalesce is roughly analogous to `??` in JS, except that it
// non-shortcutting, so it is advised to only use a constant or precomputed value for `b`
pub fn coalesce<T>(a: Option<T>, b: Option<T>) -> Option<T> {
    if a.is_none() { b } else { a }
}

pub type EcmaLineStarts = Vec<TextPos>;

pub fn compute_ecma_line_starts(text: &str) -> EcmaLineStarts {
    let mut result: Vec<TextPos> =
        Vec::with_capacity(text.bytes().filter(|&b| b == b'\n').count() + 1);
    result.extend(compute_ecma_line_starts_seq(text));
    result
}

// PORT: Go's yield-based `iter.Seq[TextPos]` becomes a pull iterator;
// utf8.DecodeRuneInString on a Rust &str is `chars().next()` since &str is
// always valid UTF-8 (invalid input that Go would decode as RuneError cannot
// occur).
pub fn compute_ecma_line_starts_seq(text: &str) -> impl Iterator<Item = TextPos> + '_ {
    let text_len = text.len() as TextPos;
    let bytes = text.as_bytes();
    let mut pos: TextPos = 0;
    let mut line_start: TextPos = 0;
    let mut finished = false;
    std::iter::from_fn(move || {
        loop {
            if pos < text_len {
                let b = bytes[pos as usize];
                if b < 0x80 {
                    pos += 1;
                    match b {
                        b'\r' => {
                            if pos < text_len && bytes[pos as usize] == b'\n' {
                                pos += 1;
                            }
                            let result = line_start;
                            line_start = pos;
                            return Some(result);
                        }
                        b'\n' => {
                            let result = line_start;
                            line_start = pos;
                            return Some(result);
                        }
                        _ => {}
                    }
                } else {
                    let ch = text[pos as usize..].chars().next().unwrap();
                    pos += ch.len_utf8() as TextPos;
                    if stringutil::is_line_break(ch) {
                        let result = line_start;
                        line_start = pos;
                        return Some(result);
                    }
                }
            } else if !finished {
                finished = true;
                return Some(line_start);
            } else {
                return None;
            }
        }
    })
}

// PositionToLineAndByteOffset returns the 0-based line and byte offset from the
// start of that line for the given byte position, using the provided line starts.
// The byte offset is a raw UTF-8 byte offset from the line start, not a UTF-16 code unit count.
pub fn position_to_line_and_byte_offset(position: i32, line_starts: &[TextPos]) -> (i32, i32) {
    let line =
        (line_starts.partition_point(|&line_start| line_start <= position) as i32 - 1).max(0);
    (line, position - line_starts[line as usize])
}

/// UTF16Offset represents a character offset measured in UTF-16 code units.
pub type UTF16Offset = i32;

// UTF16Len returns the number of UTF-16 code units needed to
// represent the given UTF-8 encoded string.
pub fn utf16_len(s: &str) -> UTF16Offset {
    // Fast path: scan for non-ASCII bytes. For ASCII-only strings,
    // each byte is one UTF-16 code unit, so we can return len(s) directly.
    for (i, &b) in s.as_bytes().iter().enumerate() {
        if b >= 0x80 {
            // Found non-ASCII; count the ASCII prefix, then decode the rest.
            let mut n = i as UTF16Offset;
            // PORT: utf16.RuneLen(r) == r.len_utf16() for every char a Rust
            // &str can contain (RuneLen's -1 cases — invalid runes/surrogates —
            // are unreachable).
            for r in s[i..].chars() {
                n += r.len_utf16() as UTF16Offset;
            }
            return n;
        }
    }
    s.len() as UTF16Offset
}

pub fn flatten<T: Clone>(array: &[Vec<T>]) -> Vec<T> {
    let mut result = Vec::new();
    for sub_array in array {
        result.extend_from_slice(sub_array);
    }
    result
}

pub fn must<T, E: std::fmt::Display>(v: Result<T, E>) -> T {
    match v {
        Ok(v) => v,
        Err(e) => panic!("{e}"),
    }
}

// Extracts the first value of a multi-value return.
// PORT: Go's variadic `_ ...any` becomes a tuple argument; call sites pass
// the multi-value return as a tuple.
pub fn first_result<T1, Rest>((t1, _rest): (T1, Rest)) -> T1 {
    t1
}

pub fn stringify_json<T: ?Sized + Serialize>(
    input: &T,
    prefix: &str,
    indent: &str,
) -> Result<String, serde_json::Error> {
    let output = json::marshal_indent(input, prefix, indent)?;
    // JSON output is always valid UTF-8.
    Ok(String::from_utf8(output).expect("JSON output is not UTF-8"))
}

pub fn get_script_kind_from_file_name(file_name: &tspath::RootedFilePath) -> ScriptKind {
    let extension = file_name.any_extension(&[], tspath::CaseSensitivity::CaseSensitive);
    if !extension.is_empty() {
        match extension.to_lowercase().as_str() {
            tspath::EXTENSION_JS | tspath::EXTENSION_CJS | tspath::EXTENSION_MJS => {
                return ScriptKind::Js;
            }
            tspath::EXTENSION_JSX => return ScriptKind::Jsx,
            tspath::EXTENSION_TS | tspath::EXTENSION_CTS | tspath::EXTENSION_MTS => {
                return ScriptKind::Ts;
            }
            tspath::EXTENSION_TSX => return ScriptKind::Tsx,
            tspath::EXTENSION_JSON => return ScriptKind::Json,
            _ => {}
        }
    }
    ScriptKind::Unknown
}

pub fn get_default_extension_for_script_kind(script_kind: ScriptKind) -> &'static str {
    match script_kind {
        ScriptKind::Js => tspath::EXTENSION_JS,
        ScriptKind::Jsx => tspath::EXTENSION_JSX,
        ScriptKind::Tsx => tspath::EXTENSION_TSX,
        ScriptKind::Json => tspath::EXTENSION_JSON,
        _ => tspath::EXTENSION_TS,
    }
}

// EnsureScriptKindFromFileName is like GetScriptKindFromFileName, but defaults to
// ScriptKindTS when the file name has no recognized extension (e.g. files included
// with allowNonTsExtensions), so the result is always safe to hand to the parser.
pub fn ensure_script_kind_from_file_name(file_name: &tspath::RootedFilePath) -> ScriptKind {
    let kind = get_script_kind_from_file_name(file_name);
    if kind != ScriptKind::Unknown {
        return kind;
    }
    ScriptKind::Ts
}

// Given a name and a list of names that are *not* equal to the name, return a spelling suggestion if there is one that is close enough.
// Names less than length 3 only check for case-insensitive equality.
//
// find the candidate with the smallest Levenshtein distance,
//
//	except for candidates:
//	  * With no name
//	  * Whose length differs from the target name by more than 0.34 of the length of the name.
//	  * Whose levenshtein distance is more than 0.4 of the length of the name
//	    (0.4 allows 1 substitution/transposition for every 5 characters,
//	     and 1 insertion/deletion at 3 characters)
//
// @internal
//
// PORT: Go returns the zero value of T when there is no suggestion; Rust
// returns Option<T>. getName's `func(T) string` becomes
// `for<'b> Fn(&'b T) -> &'b str` (a name borrowed from the candidate).
pub fn get_spelling_suggestion<T>(
    name: &str,
    candidates: impl IntoIterator<Item = T>,
    get_name: impl Fn(&T) -> &str,
    compare: impl Fn(&T, &T) -> i32,
) -> Option<T> {
    get_spelling_suggestion_impl(
        name, candidates, get_name, compare, 0, /*maxCandidates*/
    )
}

pub fn get_spelling_suggestion_with_max_candidate_count<T>(
    name: &str,
    candidates: impl IntoIterator<Item = T>,
    get_name: impl Fn(&T) -> &str,
    compare: impl Fn(&T, &T) -> i32,
    max_candidates: i32,
) -> Option<T> {
    get_spelling_suggestion_impl(name, candidates, get_name, compare, max_candidates)
}

// PORT: Go's unexported `getSpellingSuggestion` collides with the exported
// `GetSpellingSuggestion` under snake_case — renamed with an `_impl` suffix.
fn get_spelling_suggestion_impl<T>(
    name: &str,
    candidates: impl IntoIterator<Item = T>,
    get_name: impl Fn(&T) -> &str,
    compare: impl Fn(&T, &T) -> i32,
    max_candidates: i32,
) -> Option<T> {
    let rune_name: Vec<char> = name.chars().collect();
    let maximum_length_difference = 2.max((rune_name.len() as f64 * 0.34) as usize);
    // If the best result is worse than this, don't bother.
    let mut best_distance = (rune_name.len() as f64 * 0.4).floor() + 0.9;
    // PORT: Go's sync.Pool of levenshtein buffers becomes a thread_local.
    LEVENSHTEIN_BUFFERS.with(|cell| {
        let mut buffers = cell.borrow_mut();
        let mut best_candidate = None;
        let mut has_best = false;
        let mut checked_candidates = 0;
        for candidate in candidates {
            checked_candidates += 1;
            if max_candidates > 0 && checked_candidates > max_candidates {
                return None;
            }
            let candidate_name = get_name(&candidate);
            let max_len = candidate_name.len().max(rune_name.len());
            let min_len = candidate_name.len().min(rune_name.len());
            if !candidate_name.is_empty() && max_len - min_len <= maximum_length_difference {
                if candidate_name == name {
                    continue;
                }
                // Only consider candidates less than 3 characters long when they differ by case.
                // Otherwise, don't bother, since a user would usually notice differences of a 2-character name.
                if candidate_name.len() < 3
                    && !stringutil::equate_string_case_insensitive(
                        candidate_name.as_bytes(),
                        name.as_bytes(),
                    )
                {
                    continue;
                }
                let candidate_runes: Vec<char> = candidate_name.chars().collect();
                let distance =
                    levenshtein_with_max(&mut buffers, &rune_name, &candidate_runes, best_distance);
                if distance < 0.0 {
                    continue;
                }
                // Else `levenshteinWithMax` should return undefined
                debug::assert_!(distance <= best_distance);
                if distance < best_distance {
                    best_distance = distance;
                    best_candidate = Some(candidate);
                    has_best = true;
                } else if !has_best || compare(&candidate, best_candidate.as_ref().unwrap()) < 0 {
                    best_candidate = Some(candidate);
                    has_best = true;
                }
            }
        }
        best_candidate
    })
}

// PORT: `iter.Seq[string]` becomes an iterator of `&str`; returns the matched
// &str instead of Go's zero-or-matched string.
pub fn get_spelling_suggestion_for_strings<'a>(
    name: &'a str,
    candidates: impl IntoIterator<Item = &'a str>,
) -> Option<&'a str> {
    get_spelling_suggestion(
        name,
        candidates,
        |s| *s,
        |a, b| stringutil::compare_strings_case_sensitive(a.as_bytes(), b.as_bytes()),
    )
}

struct LevenshteinBuffers {
    previous: Vec<f64>,
    current: Vec<f64>,
}

thread_local! {
    // PORT: `sync.Pool` becomes a per-thread cached buffer.
    static LEVENSHTEIN_BUFFERS: RefCell<LevenshteinBuffers> = const {
        RefCell::new(LevenshteinBuffers {
            previous: Vec::new(),
            current: Vec::new(),
        })
    };
}

// unicode.ToLower — Go's *simple* (1:1) Unicode case mapping.
// PORT: Rust's `char::to_lowercase` is the full mapping; a single-char result
// is the simple mapping, and a multi-char result means Go has no simple
// mapping and returns the rune unchanged. Differences vs. Go's CaseRanges
// table are possible only for runes whose full mapping is a single char but
// whose simple mapping differs — unreachable in practice for identifier
// spelling suggestions.
fn go_to_lower(ch: char) -> char {
    let mut it = ch.to_lowercase();
    let first = it.next().unwrap();
    if it.next().is_none() { first } else { ch }
}

fn levenshtein_with_max(
    buffers: &mut LevenshteinBuffers,
    s1: &[char],
    s2: &[char],
    max_value: f64,
) -> f64 {
    let buffer_size = s2.len() + 1;
    buffers.previous.clear();
    buffers.previous.resize(buffer_size, 0.0);
    buffers.current.clear();
    buffers.current.resize(buffer_size, 0.0);

    let LevenshteinBuffers { previous, current } = buffers;

    let big = max_value + 0.01;
    for (i, p) in previous.iter_mut().enumerate() {
        *p = i as f64;
    }
    for i in 1..=s1.len() {
        let c1 = s1[i - 1];
        let min_j = ((i as f64 - max_value).ceil() as i64).max(1) as usize;
        let max_j = ((max_value + i as f64).floor() as i64)
            .min(s2.len() as i64)
            .max(0) as usize;
        let mut col_min = i as f64;
        current[0] = col_min;
        for c in current.iter_mut().take(min_j).skip(1) {
            *c = big;
        }
        for j in min_j..=max_j {
            let substitution_distance = if go_to_lower(s1[i - 1]) == go_to_lower(s2[j - 1]) {
                previous[j - 1] + 0.1
            } else {
                previous[j - 1] + 2.0
            };
            let dist = if c1 == s2[j - 1] {
                previous[j - 1]
            } else {
                (previous[j] + 1.0).min((current[j - 1] + 1.0).min(substitution_distance))
            };
            current[j] = dist;
            col_min = col_min.min(dist);
        }
        for c in current.iter_mut().take(s2.len() + 1).skip(max_j + 1) {
            *c = big;
        }
        if col_min > max_value {
            // Give up -- everything in this column is > max and it can't get better in future columns.
            return -1.0;
        }
        std::mem::swap(previous, current);
    }
    let res = previous[s2.len()];
    if res > max_value {
        return -1.0;
    }
    res
}

pub fn identity<T>(t: T) -> T {
    t
}

pub fn check_each_defined<'a, S>(s: &'a [Option<S>], msg: &str) -> &'a [Option<S>] {
    for value in s {
        if value.is_none() {
            panic!("{msg}");
        }
    }
    s
}

// PORT: Go's `int` return stays i32 (-1 for no match); startIndex is usize.
pub fn index_after(s: &str, pattern: &str, start_index: usize) -> i32 {
    match s[start_index..].find(pattern) {
        None => -1,
        Some(matched) => (matched + start_index) as i32,
    }
}

pub fn should_rewrite_module_specifier(
    specifier: &str,
    compiler_options: &CompilerOptions,
) -> bool {
    compiler_options
        .rewrite_relative_import_extensions
        .is_true()
        && tspath::path_is_relative(specifier)
        && !tspath::is_declaration_file_name(specifier)
        && tspath::has_ts_file_extension(specifier)
}

// PORT: Go's `*T` becomes `Option<T>`; nil → empty Vec.
pub fn single_element_slice<T>(element: Option<T>) -> Vec<T> {
    match element {
        None => Vec::new(),
        Some(element) => vec![element],
    }
}

// PORT: `iter.Seq` values become iterators; Go's nil seqs become `None`.
pub fn concatenate_seq<T, I: Iterator<Item = T>>(
    seqs: impl IntoIterator<Item = Option<I>>,
) -> impl Iterator<Item = T> {
    seqs.into_iter().flatten().flatten()
}

// Enumerate returns a sequence of (index, value) pairs from the input sequence.
pub fn enumerate<T>(seq: impl Iterator<Item = T>) -> impl Iterator<Item = (i32, T)> {
    seq.enumerate().map(|(i, v)| (i as i32, v))
}

fn comparable_values_equal<T: PartialEq>(a: &T, b: &T) -> bool {
    a == b
}

// DiffMaps compares two maps m1 and m2 and calls the provided callbacks for added, removed, and changed entries.
// onAdded is called for each key-value pair that is in m2 but not in m1.
// onRemoved is called for each key-value pair that is in m1 but not in m2.
// onChanged is called for each key where the value in m1 differs from the value in m2.
//
// PORT: Go's nil-able `func` callbacks become `Option<&mut impl FnMut>`.
#[allow(clippy::type_complexity)]
pub fn diff_maps<K: Eq + std::hash::Hash, V: PartialEq>(
    m1: &FxHashMap<K, V>,
    m2: &FxHashMap<K, V>,
    on_added: Option<&mut dyn FnMut(&K, &V)>,
    on_removed: Option<&mut dyn FnMut(&K, &V)>,
    on_changed: Option<&mut dyn FnMut(&K, &V, &V)>,
) {
    diff_maps_func(
        m1,
        m2,
        |a, b| comparable_values_equal(a, b),
        on_added,
        on_removed,
        on_changed,
    );
}

// DiffMapsFunc compares two maps m1 and m2 and calls the provided callbacks for added, removed, and changed entries.
// onAdded is called for each key-value pair that is in m2 but not in m1.
// onRemoved is called for each key-value pair that is in m1 but not in m2.
// onChanged is called for each key where the value in m1 differs from the value in m2.
#[allow(clippy::type_complexity)]
pub fn diff_maps_func<K: Eq + std::hash::Hash, V1, V2>(
    m1: &FxHashMap<K, V1>,
    m2: &FxHashMap<K, V2>,
    equal_values: impl Fn(&V1, &V2) -> bool,
    mut on_added: Option<&mut dyn FnMut(&K, &V2)>,
    mut on_removed: Option<&mut dyn FnMut(&K, &V1)>,
    mut on_changed: Option<&mut dyn FnMut(&K, &V1, &V2)>,
) {
    if let Some(on_added) = on_added.as_mut() {
        for (k, v2) in m2 {
            if !m1.contains_key(k) {
                on_added(k, v2);
            }
        }
    }
    if on_changed.is_none() && on_removed.is_none() {
        return;
    }
    for (k, v1) in m1 {
        if let Some(v2) = m2.get(k) {
            if let Some(on_changed) = on_changed.as_mut() {
                if !equal_values(v1, v2) {
                    on_changed(k, v1, v2);
                }
            }
        } else if let Some(on_removed) = on_removed.as_mut() {
            on_removed(k, v1);
        }
    }
}

// CopyMapInto is maps.Copy, unless dst is nil, in which case it clones and returns src.
// Use CopyMapInto anywhere you would use maps.Copy preceded by a nil check and map initialization.
//
// PORT: Go's nil-able `dst` becomes `Option<FxHashMap>`; the (possibly new)
// map is returned in both cases.
pub fn copy_map_into<K: Eq + std::hash::Hash + Clone, V: Clone>(
    dst: Option<FxHashMap<K, V>>,
    src: &FxHashMap<K, V>,
) -> FxHashMap<K, V> {
    match dst {
        None => src.clone(),
        Some(mut dst) => {
            dst.extend(src.iter().map(|(k, v)| (k.clone(), v.clone())));
            dst
        }
    }
}

// UnorderedEqual returns true if s1 and s2 contain the same elements, regardless of order.
pub fn unordered_equal<T: Eq + std::hash::Hash>(s1: &[T], s2: &[T]) -> bool {
    if s1.len() != s2.len() {
        return false;
    }
    let mut counts: FxHashMap<&T, i32> = FxHashMap::default();
    for v in s1 {
        *counts.entry(v).or_default() += 1;
    }
    for v in s2 {
        let count = counts.entry(v).or_default();
        *count -= 1;
        if *count < 0 {
            return false;
        }
    }
    true
}

pub fn deduplicate<'a, T: PartialEq + Clone>(slice: &'a [T]) -> Cow<'a, [T]> {
    if slice.len() > 1 {
        for (i, value) in slice.iter().enumerate() {
            if slice[..i].contains(value) {
                let mut result = slice[..i].to_vec();
                for value in &slice[i + 1..] {
                    if !result.contains(value) {
                        result.push(value.clone());
                    }
                }
                return Cow::Owned(result);
            }
        }
    }
    Cow::Borrowed(slice)
}

// PORT: Go's `isEqual func(a, b T) bool` becomes `Fn(&T, &T) -> bool`.
pub fn deduplicate_sorted<'a, T: Clone>(
    slice: &'a [T],
    is_equal: impl Fn(&T, &T) -> bool,
) -> Cow<'a, [T]> {
    if slice.is_empty() {
        return Cow::Borrowed(slice);
    }
    let mut last = &slice[0];
    let mut deduplicated = Vec::with_capacity(slice.len());
    deduplicated.push(last.clone());
    let mut changed = false;
    for next in &slice[1..] {
        if is_equal(last, next) {
            changed = true;
            continue;
        }

        deduplicated.push(next.clone());
        last = next;
    }

    // PORT: Go's `deduplicated` is a re-slice of the input when nothing was
    // dropped, preserving slice identity; the Cow does the same.
    if !changed {
        Cow::Borrowed(slice)
    } else {
        Cow::Owned(deduplicated)
    }
}

// CompareBooleans treats true as greater than false.
pub fn compare_booleans(a: bool, b: bool) -> i32 {
    if a && !b {
        return 1;
    } else if !a && b {
        return -1;
    }
    0
}
