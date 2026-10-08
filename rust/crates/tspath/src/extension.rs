// Ported from tsc/internal/tspath/extension.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;
use std::sync::LazyLock;

use crate::path::{
    CaseSensitivity, file_extension_is, get_any_extension_from_path, get_base_file_name_from_normalized,
    normalize_slashes,
};

pub const EXTENSION_TS: &str = ".ts";
pub const EXTENSION_TSX: &str = ".tsx";
pub const EXTENSION_DTS: &str = ".d.ts";
pub const EXTENSION_JS: &str = ".js";
pub const EXTENSION_JSX: &str = ".jsx";
pub const EXTENSION_JSON: &str = ".json";
pub const EXTENSION_TS_BUILD_INFO: &str = ".tsbuildinfo";
pub const EXTENSION_MJS: &str = ".mjs";
pub const EXTENSION_MTS: &str = ".mts";
pub const EXTENSION_DMTS: &str = ".d.mts";
pub const EXTENSION_CJS: &str = ".cjs";
pub const EXTENSION_CTS: &str = ".cts";
pub const EXTENSION_DCTS: &str = ".d.cts";

pub static SUPPORTED_DECLARATION_EXTENSIONS: &[&str] =
    &[EXTENSION_DTS, EXTENSION_DCTS, EXTENSION_DMTS];
pub static SUPPORTED_TS_IMPLEMENTATION_EXTENSIONS: &[&str] =
    &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_MTS, EXTENSION_CTS];
pub(crate) static SUPPORTED_TS_EXTENSIONS_FOR_EXTRACT_EXTENSION: &[&str] = &[
    EXTENSION_DTS,
    EXTENSION_DCTS,
    EXTENSION_DMTS,
    EXTENSION_TS,
    EXTENSION_TSX,
    EXTENSION_MTS,
    EXTENSION_CTS,
];
pub static ALL_SUPPORTED_EXTENSIONS: &[&[&str]] = &[
    &[
        EXTENSION_TS,
        EXTENSION_TSX,
        EXTENSION_DTS,
        EXTENSION_JS,
        EXTENSION_JSX,
    ],
    &[EXTENSION_CTS, EXTENSION_DCTS, EXTENSION_CJS],
    &[EXTENSION_MTS, EXTENSION_DMTS, EXTENSION_MJS],
];
pub static SUPPORTED_TS_EXTENSIONS: &[&[&str]] = &[
    &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_DTS],
    &[EXTENSION_CTS, EXTENSION_DCTS],
    &[EXTENSION_MTS, EXTENSION_DMTS],
];
pub static SUPPORTED_TS_EXTENSIONS_FLAT: &[&str] = &[
    EXTENSION_TS,
    EXTENSION_TSX,
    EXTENSION_DTS,
    EXTENSION_CTS,
    EXTENSION_DCTS,
    EXTENSION_MTS,
    EXTENSION_DMTS,
];
pub static SUPPORTED_JS_EXTENSIONS: &[&[&str]] =
    &[&[EXTENSION_JS, EXTENSION_JSX], &[EXTENSION_MJS], &[EXTENSION_CJS]];
pub static SUPPORTED_JS_EXTENSIONS_FLAT: &[&str] =
    &[EXTENSION_JS, EXTENSION_JSX, EXTENSION_MJS, EXTENSION_CJS];
// PORT: slices.Concat -> LazyLock-concatenated vectors (statics cannot be built
// by concatenation in Rust).
pub static ALL_SUPPORTED_EXTENSIONS_WITH_JSON: LazyLock<Vec<&'static [&'static str]>> =
    LazyLock::new(|| {
        let mut v = ALL_SUPPORTED_EXTENSIONS.to_vec();
        v.push(&[EXTENSION_JSON]);
        v
    });
pub static SUPPORTED_TS_EXTENSIONS_WITH_JSON: LazyLock<Vec<&'static [&'static str]>> =
    LazyLock::new(|| {
        let mut v = SUPPORTED_TS_EXTENSIONS.to_vec();
        v.push(&[EXTENSION_JSON]);
        v
    });
pub static SUPPORTED_TS_EXTENSIONS_WITH_JSON_FLAT: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| {
        let mut v = SUPPORTED_TS_EXTENSIONS_FLAT.to_vec();
        v.push(EXTENSION_JSON);
        v
    });
pub static EXTENSIONS_NOT_SUPPORTING_EXTENSIONLESS_RESOLUTION: &[&str] = &[
    EXTENSION_MTS,
    EXTENSION_DMTS,
    EXTENSION_MJS,
    EXTENSION_CTS,
    EXTENSION_DCTS,
    EXTENSION_CJS,
];

pub fn extension_is_ts(ext: &str) -> bool {
    ext == EXTENSION_TS
        || ext == EXTENSION_TSX
        || ext == EXTENSION_DTS
        || ext == EXTENSION_MTS
        || ext == EXTENSION_DMTS
        || ext == EXTENSION_CTS
        || ext == EXTENSION_DCTS
        || (ext.len() >= 7 && ext.starts_with(".d.") && ext.ends_with(".ts"))
}

static EXTENSIONS_TO_REMOVE: &[&str] = &[
    EXTENSION_DTS,
    EXTENSION_DMTS,
    EXTENSION_DCTS,
    EXTENSION_MJS,
    EXTENSION_MTS,
    EXTENSION_CJS,
    EXTENSION_CTS,
    EXTENSION_TS,
    EXTENSION_JS,
    EXTENSION_TSX,
    EXTENSION_JSX,
    EXTENSION_JSON,
];

pub fn remove_file_extension<'a>(path: &'a str) -> &'a str {
    // Remove any known extension even if it has more than one dot
    for &ext in EXTENSIONS_TO_REMOVE {
        if path.ends_with(ext) {
            return &path[..path.len() - ext.len()];
        }
    }

    path
}

pub fn remove_any_file_extension(path: &str) -> Cow<'_, str> {
    let without_extension = remove_file_extension(path);
    if without_extension != path {
        return Cow::Borrowed(without_extension);
    }
    let extension = get_any_extension_from_path(path, &[], CaseSensitivity::CaseSensitive);
    if !extension.is_empty() {
        return Cow::Borrowed(remove_extension(path, &extension));
    }
    Cow::Borrowed(path)
}

pub fn try_get_extension_from_path(p: &str) -> &str {
    for &ext in EXTENSIONS_TO_REMOVE {
        if file_extension_is(p, ext) {
            return ext;
        }
    }
    ""
}

pub fn remove_extension<'a>(path: &'a str, extension: &str) -> &'a str {
    &path[..path.len() - extension.len()]
}

pub fn file_extension_is_one_of(path: &str, extensions: &[&str]) -> bool {
    for &ext in extensions {
        if file_extension_is(path, ext) {
            return true;
        }
    }
    false
}

pub fn try_extract_ts_extension(file_name: &str) -> &str {
    for &ext in SUPPORTED_TS_EXTENSIONS_FOR_EXTRACT_EXTENSION {
        if file_extension_is(file_name, ext) {
            return ext;
        }
    }
    ""
}

pub fn has_ts_file_extension(path: &str) -> bool {
    file_extension_is_one_of(path, SUPPORTED_TS_EXTENSIONS_FLAT)
}

pub fn has_implementation_ts_file_extension(path: &str) -> bool {
    file_extension_is_one_of(path, SUPPORTED_TS_IMPLEMENTATION_EXTENSIONS)
        && !is_declaration_file_name(path)
}

pub fn has_js_file_extension(path: &str) -> bool {
    file_extension_is_one_of(path, SUPPORTED_JS_EXTENSIONS_FLAT)
}

pub fn has_json_file_extension(path: &str) -> bool {
    file_extension_is(path, EXTENSION_JSON)
}

pub fn is_declaration_file_name(file_name: &str) -> bool {
    !get_declaration_file_extension(file_name).is_empty()
}

pub fn extension_is_one_of(ext: &str, extensions: &[&str]) -> bool {
    extensions.contains(&ext)
}

pub fn get_declaration_file_extension(file_name: &str) -> Cow<'_, str> {
    // PORT: normalize_slashes may allocate when the input contains '\\', so this
    // returns Cow rather than &str.
    match normalize_slashes(file_name) {
        Cow::Borrowed(s) => Cow::Borrowed(get_declaration_file_extension_from_normalized(s)),
        Cow::Owned(s) => {
            Cow::Owned(get_declaration_file_extension_from_normalized(&s).to_string())
        }
    }
}

pub(crate) fn get_declaration_file_extension_from_normalized(file_name: &str) -> &str {
    let base = get_base_file_name_from_normalized(file_name);
    for &ext in SUPPORTED_DECLARATION_EXTENSIONS {
        if base.ends_with(ext) {
            return ext;
        }
    }
    if base.ends_with(EXTENSION_TS) {
        if let Some(index) = base.find(".d.") {
            return &base[index..];
        }
    }
    ""
}

pub fn get_declaration_emit_extension_for_path(path: &str) -> Cow<'_, str> {
    if file_extension_is_one_of(path, &[EXTENSION_MJS, EXTENSION_MTS]) {
        return Cow::Borrowed(EXTENSION_DMTS);
    }
    if file_extension_is_one_of(path, &[EXTENSION_CJS, EXTENSION_CTS]) {
        return Cow::Borrowed(EXTENSION_DCTS);
    }
    if file_extension_is_one_of(path, &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_JS, EXTENSION_JSX]) {
        return Cow::Borrowed(EXTENSION_DTS);
    }
    let ext = get_any_extension_from_path(path, &[], CaseSensitivity::CaseSensitive);
    if !ext.is_empty() {
        return Cow::Owned(format!(".d{ext}.ts"));
    }
    Cow::Borrowed(EXTENSION_DTS)
}

// ChangeAnyExtension changes the extension of a path to the provided extension if it has one of the provided extensions.
//
// ChangeAnyExtension("/path/to/file.ext", ".js", ".ext") === "/path/to/file.js"
// ChangeAnyExtension("/path/to/file.ext", ".js", ".ts") === "/path/to/file.ext"
// ChangeAnyExtension("/path/to/file.ext", ".js", [".ext", ".ts"]) === "/path/to/file.js"
pub fn change_any_extension<'a>(
    path: &'a str,
    ext: &str,
    extensions: &[&str],
    case_sensitivity: CaseSensitivity,
) -> Cow<'a, str> {
    let pathext = get_any_extension_from_path(path, extensions, case_sensitivity);
    if !pathext.is_empty() {
        let result = &path[..path.len() - pathext.len()];
        if ext.is_empty() {
            return Cow::Borrowed(result);
        }
        if ext.starts_with('.') {
            return Cow::Owned(format!("{result}{ext}"));
        }
        return Cow::Owned(format!("{result}.{ext}"));
    }
    Cow::Borrowed(path)
}

pub fn change_extension<'a>(path: &'a str, new_extension: &str) -> Cow<'a, str> {
    change_any_extension(path, new_extension, EXTENSIONS_TO_REMOVE, CaseSensitivity::CaseSensitive)
}

// Like `changeAnyExtension`, but declaration file extensions are recognized
// and replaced starting from the `.d`.
//
//	changeAnyExtension("file.d.ts", ".js") === "file.d.js"
//	changeFullExtension("file.d.ts", ".js") === "file.js"
pub fn change_full_extension<'a>(path: &'a str, new_extension: &str) -> Cow<'a, str> {
    let declaration_extension = get_declaration_file_extension(path);
    if !declaration_extension.is_empty() {
        let ext: Cow<str> = if new_extension.is_empty() {
            return Cow::Borrowed(&path[..path.len() - declaration_extension.len()]);
        } else if !new_extension.starts_with('.') {
            Cow::Owned(format!(".{new_extension}"))
        } else {
            Cow::Borrowed(new_extension)
        };
        return Cow::Owned(format!(
            "{}{ext}",
            &path[..path.len() - declaration_extension.len()]
        ));
    }
    change_extension(path, new_extension)
}

pub fn get_possible_original_input_extension_for_extension(path: &str) -> Vec<String> {
    if file_extension_is_one_of(path, &[EXTENSION_DMTS, EXTENSION_MJS, EXTENSION_MTS]) {
        return vec![EXTENSION_MTS.to_string(), EXTENSION_MJS.to_string()];
    }
    if file_extension_is_one_of(path, &[EXTENSION_DCTS, EXTENSION_CJS, EXTENSION_CTS]) {
        return vec![EXTENSION_CTS.to_string(), EXTENSION_CJS.to_string()];
    }
    // Handle any custom .d.x.ts extension (e.g., .d.json.ts -> .json, .d.css.ts -> .css)
    let ext = get_declaration_file_extension(path);
    if !ext.is_empty() && ext != EXTENSION_DTS {
        let inner = &ext[".d.".len()..ext.len() - ".ts".len()];
        return vec![format!(".{inner}")];
    }
    vec![
        EXTENSION_TSX.to_string(),
        EXTENSION_TS.to_string(),
        EXTENSION_JSX.to_string(),
        EXTENSION_JS.to_string(),
    ]
}
