// Ported from tsc/internal/tspath/dynamic.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;

use crate::extension::get_declaration_file_extension;
use crate::path::{
    CaseSensitivity, DIRECTORY_SEPARATOR, get_any_extension_from_path, get_root_length,
    has_trailing_directory_separator, path_is_absolute, remove_trailing_directory_separator,
};

pub const DYNAMIC_URI_FILE_NAME_PREFIX: &str = "^/~ts-uri~/";
pub(crate) const DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX: &str = "~ts-uri-escape~";
pub(crate) const DYNAMIC_URI_MODULE_SPECIFIER_ESCAPE_PREFIX: &str = "~ts-uri-spec~";
pub(crate) const DYNAMIC_URI_NO_PATH_ESCAPE_PREFIX: &str = "~ts-uri-no-path~";

pub fn is_encoded_dynamic_file_name(path: &str) -> bool {
    path.starts_with(DYNAMIC_URI_FILE_NAME_PREFIX)
}

pub(crate) fn canonical_dynamic_uri_path(path: &str) -> Cow<'_, str> {
    if is_encoded_dynamic_file_name(path)
        && get_root_length(path) == path.len()
        && !has_trailing_directory_separator(path)
    {
        return Cow::Owned(format!("{path}{DIRECTORY_SEPARATOR}"));
    }
    Cow::Borrowed(path)
}

pub fn encode_dynamic_uri_path(path: &str) -> Cow<'_, str> {
    encode_dynamic_uri_path_root_aware(path, true)
}

pub fn encode_dynamic_uri_path_with_suffix(path: &str, suffix: &str) -> String {
    if suffix.is_empty() {
        return encode_dynamic_uri_path(path).into_owned();
    }
    let slash = path.rfind('/');
    let mut before = String::new();
    if let Some(slash) = slash {
        before = format!("{}/", encode_dynamic_uri_directory_path(&path[..slash]));
    }
    let segment = &path[slash.map_or(0, |s| s + 1)..];
    format!(
        "{before}{}",
        force_encode_dynamic_uri_path_segment_with_suffix(segment, suffix)
    )
}

pub fn encode_dynamic_uri_directory_path(path: &str) -> Cow<'_, str> {
    encode_dynamic_uri_path_root_aware(path, false)
}

fn encode_dynamic_uri_path_root_aware(path: &str, preserve_final_extension: bool) -> Cow<'_, str> {
    let encoded = encode_dynamic_uri_path_impl(path, preserve_final_extension);
    if !path_is_absolute(&encoded) {
        return encoded;
    }
    match encoded.split_once('/') {
        None => Cow::Owned(force_encode_dynamic_uri_path_segment(
            &encoded,
            preserve_final_extension,
        )),
        Some((first, rest)) => Cow::Owned(format!(
            "{}/{rest}",
            force_encode_dynamic_uri_path_segment(first, false)
        )),
    }
}

pub fn encode_dynamic_relative_uri_path(path: &str) -> String {
    encode_dynamic_relative_uri_path_impl(path, true)
}

pub fn encode_dynamic_relative_uri_directory_path(path: &str) -> String {
    encode_dynamic_relative_uri_path_impl(path, false)
}

fn encode_dynamic_relative_uri_path_impl(path: &str, preserve_final_extension: bool) -> String {
    encode_dynamic_uri_path_root_aware(path, preserve_final_extension).into_owned()
}

fn encode_dynamic_uri_path_impl(path: &str, preserve_final_extension: bool) -> Cow<'_, str> {
    if !dynamic_uri_path_needs_encoding(path) {
        return Cow::Borrowed(path);
    }

    let mut result =
        String::with_capacity(path.len() + DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX.len());
    let mut path = path;
    loop {
        let (segment, rest, found) = match path.split_once('/') {
            Some((segment, rest)) => (segment, rest, true),
            None => (path, "", false),
        };
        result.push_str(&encode_dynamic_uri_path_segment(
            segment,
            preserve_final_extension && !found,
        ));
        if !found {
            return Cow::Owned(result);
        }
        result.push('/');
        path = rest;
    }
}

pub fn force_encode_dynamic_uri_path_segment(segment: &str, preserve_extension: bool) -> String {
    force_encode_dynamic_uri_path_segment_impl(segment, preserve_extension)
}

pub fn encode_dynamic_module_specifier(specifier: &str) -> Cow<'_, str> {
    encode_dynamic_module_specifier_impl(specifier, true)
}

pub fn encode_dynamic_directory_specifier(specifier: &str) -> Cow<'_, str> {
    encode_dynamic_module_specifier_impl(specifier, false)
}

fn encode_dynamic_module_specifier_impl(
    specifier: &str,
    preserve_final_extension: bool,
) -> Cow<'_, str> {
    if !specifier.contains(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX)
        && !specifier.contains(DYNAMIC_URI_MODULE_SPECIFIER_ESCAPE_PREFIX)
    {
        return Cow::Borrowed(specifier);
    }

    let mut result =
        String::with_capacity(specifier.len() + DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX.len());
    let mut specifier = specifier;
    loop {
        match specifier.find(['/', '\\']) {
            None => {
                result.push_str(&encode_dynamic_module_specifier_segment(
                    specifier,
                    preserve_final_extension,
                ));
                return Cow::Owned(result);
            }
            Some(separator) => {
                result.push_str(&encode_dynamic_module_specifier_segment(
                    &specifier[..separator],
                    false,
                ));
                result.push(specifier.as_bytes()[separator] as char);
                specifier = &specifier[separator + 1..];
            }
        }
    }
}

fn encode_dynamic_module_specifier_segment(segment: &str, preserve_extension: bool) -> String {
    if let Some(encoded) = segment.strip_prefix(DYNAMIC_URI_MODULE_SPECIFIER_ESCAPE_PREFIX) {
        let physical = format!("{DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX}{encoded}");
        if decode_dynamic_uri_path_segment(&physical) != physical {
            return physical;
        }
    }
    if segment.starts_with(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX) {
        return force_encode_dynamic_uri_path_segment(segment, preserve_extension);
    }
    segment.to_string()
}

pub fn dynamic_uri_path_to_module_specifier(path: &str) -> Cow<'_, str> {
    if !path.contains(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX) {
        return Cow::Borrowed(path);
    }
    let mut segments: Vec<String> = path.split('/').map(str::to_string).collect();
    for segment in &mut segments {
        if segment.starts_with(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX)
            && decode_dynamic_uri_path_segment(segment) != *segment
        {
            *segment = format!(
                "{DYNAMIC_URI_MODULE_SPECIFIER_ESCAPE_PREFIX}{}",
                segment
                    .strip_prefix(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX)
                    .unwrap()
            );
        }
    }
    Cow::Owned(segments.join("/"))
}

pub fn encode_dynamic_logical_module_specifier(specifier: &str) -> Cow<'_, str> {
    if specifier.is_empty() {
        return Cow::Borrowed("");
    }
    let trailing_separator = has_trailing_directory_separator(specifier);
    let specifier = if trailing_separator {
        remove_trailing_directory_separator(specifier)
    } else {
        specifier
    };
    let mut encoded =
        dynamic_uri_path_to_module_specifier(&encode_dynamic_relative_uri_path(specifier))
            .into_owned();
    if trailing_separator {
        encoded.push(DIRECTORY_SEPARATOR);
    }
    Cow::Owned(encoded)
}

fn dynamic_uri_path_needs_encoding(path: &str) -> bool {
    let mut path = path;
    loop {
        let (segment, rest, found) = match path.split_once('/') {
            Some((segment, rest)) => (segment, rest, true),
            None => (path, "", false),
        };
        if dynamic_uri_path_segment_needs_encoding(segment) {
            return true;
        }
        if !found {
            return false;
        }
        path = rest;
    }
}

fn encode_dynamic_uri_path_segment<'a>(segment: &'a str, preserve_extension: bool) -> Cow<'a, str> {
    if dynamic_uri_path_segment_needs_encoding(segment) {
        return Cow::Owned(force_encode_dynamic_uri_path_segment(
            segment,
            preserve_extension,
        ));
    }
    Cow::Borrowed(segment)
}

fn dynamic_uri_path_segment_needs_encoding(segment: &str) -> bool {
    segment.is_empty()
        || segment == "."
        || segment == ".."
        || segment.starts_with(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX)
        || segment.starts_with(DYNAMIC_URI_MODULE_SPECIFIER_ESCAPE_PREFIX)
        || segment.starts_with(DYNAMIC_URI_NO_PATH_ESCAPE_PREFIX)
        || segment.contains('\\')
}

pub fn encode_dynamic_uri_no_path(suffix: &str) -> String {
    format!(
        "{DYNAMIC_URI_NO_PATH_ESCAPE_PREFIX}{}~",
        hex_encode(suffix.as_bytes())
    )
}

pub fn decode_dynamic_uri_no_path(path: &str) -> Option<String> {
    let encoded = path.strip_prefix(DYNAMIC_URI_NO_PATH_ESCAPE_PREFIX)?;
    let (encoded, rest) = encoded.split_once('~')?;
    if !rest.is_empty() {
        return None;
    }
    let decoded = hex_decode(encoded)?;
    if std::str::from_utf8(&decoded).is_err() {
        return None;
    }
    String::from_utf8(decoded).ok()
}

fn force_encode_dynamic_uri_path_segment_impl(segment: &str, preserve_extension: bool) -> String {
    let mut extension = Cow::Borrowed("");
    let mut segment = segment;
    if preserve_extension && segment != "." && segment != ".." {
        let (base, ext) = split_dynamic_uri_file_extension(segment);
        segment = base;
        extension = ext;
    }
    format!(
        "{DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX}{}~{extension}",
        hex_encode(segment.as_bytes())
    )
}

fn force_encode_dynamic_uri_path_segment_with_suffix(segment: &str, suffix: &str) -> String {
    let (segment, extension) = split_dynamic_uri_file_extension(segment);
    let payload = format!("{segment}\u{0}{suffix}");
    format!(
        "{DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX}{}~{extension}",
        hex_encode(payload.as_bytes())
    )
}

fn split_dynamic_uri_file_extension(segment: &str) -> (&str, Cow<'_, str>) {
    let base_name = &segment[segment.rfind('\\').map_or(0, |i| i + 1)..];
    let mut extension = get_declaration_file_extension(base_name);
    if extension.is_empty() {
        extension = get_any_extension_from_path(base_name, &[], CaseSensitivity::CaseSensitive);
    }
    if !extension.is_empty() {
        return (&segment[..segment.len() - extension.len()], extension);
    }
    (segment, extension)
}

pub fn decode_dynamic_uri_path(path: &str) -> Cow<'_, str> {
    if !path.contains(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX) {
        return Cow::Borrowed(path);
    }
    let segments: Vec<String> = path
        .split('/')
        .map(decode_dynamic_uri_path_segment)
        .collect();
    Cow::Owned(segments.join("/"))
}

pub fn try_decode_dynamic_uri_path(path: &str) -> Option<String> {
    let mut segments: Vec<String> = Vec::new();
    for segment in path.split('/') {
        {
            let decoded = try_decode_dynamic_uri_path_segment(segment)?;
            segments.push(decoded)
        }
    }
    Some(segments.join("/"))
}

pub fn decode_dynamic_uri_path_for_disk(path: &str) -> Option<String> {
    let decoded = decode_dynamic_uri_path(path).into_owned();
    if path_is_absolute(&decoded) {
        return None;
    }
    let mut remaining = decoded.as_str();
    loop {
        let (segment, rest, found) = match remaining.split_once('/') {
            Some((segment, rest)) => (segment, rest, true),
            None => (remaining, "", false),
        };
        if segment.is_empty() {
            if !found {
                return Some(decoded);
            }
            return None;
        }
        if segment == "." || segment == ".." || segment.contains('\\') {
            return None;
        }
        if !found {
            return Some(decoded);
        }
        remaining = rest;
    }
}

pub fn decode_dynamic_uri_path_segment(segment: &str) -> String {
    match try_decode_dynamic_uri_path_segment(segment) {
        None => segment.to_string(),
        Some(decoded) => decoded,
    }
}

pub fn try_decode_dynamic_uri_path_segment(segment: &str) -> Option<String> {
    let encoded = match segment.strip_prefix(DYNAMIC_URI_PATH_SEGMENT_ESCAPE_PREFIX) {
        None => {
            if dynamic_uri_path_segment_needs_encoding(segment) {
                return None;
            }
            return Some(segment.to_string());
        }
        Some(encoded) => encoded,
    };
    let (encoded, extension) = encoded.split_once('~')?;
    let decoded = hex_decode(encoded)?;
    if std::str::from_utf8(&decoded).is_err() {
        return None;
    }
    let decoded = String::from_utf8(decoded).ok()?;
    if let Some((base, suffix)) = decoded.split_once('\u{0}') {
        return Some(format!("{base}{extension}{suffix}"));
    }
    Some(format!("{decoded}{extension}"))
}

// PORT: Go's encoding/hex helpers. Lowercase hex output matches
// hex.EncodeToString; decoding rejects odd lengths and non-hex digits like
// hex.DecodeString.
fn hex_encode(bytes: &[u8]) -> String {
    const HEXDIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEXDIGITS[(b >> 4) as usize] as char);
        s.push(HEXDIGITS[(b & 0x0f) as usize] as char);
    }
    s
}

fn hex_decode(s: &str) -> Option<Vec<u8>> {
    fn hex_val(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    }
    let bytes = s.as_bytes();
    if bytes.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        out.push((hex_val(pair[0])? << 4) | hex_val(pair[1])?);
    }
    Some(out)
}
