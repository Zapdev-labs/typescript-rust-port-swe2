// Ported from tsc/internal/tsoptions/enummaps.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashSet;
use std::sync::LazyLock;

use tsc_core::options_generated::{CompilerOptions, ScriptTarget};
use tsc_tspath as tspath;

use crate::generated::declarations::{self, LIB_MAP};
use crate::value::Value;

/// `var Libs = slices.Collect(LibMap.Keys())`.
pub fn libs() -> &'static [String] {
    static LIBS: LazyLock<Vec<String>> = LazyLock::new(|| LIB_MAP.keys().cloned().collect());
    &LIBS
}

/// `var LibFilesSet = collections.NewSetFromItems(...)`.
fn lib_files_set() -> &'static HashSet<String> {
    static SET: LazyLock<HashSet<String>> = LazyLock::new(|| {
        LIB_MAP
            .values()
            .map(|v| match v {
                Value::Str(s) => s.clone(),
                _ => unreachable!(),
            })
            .collect()
    });
    &SET
}

/// `GetLibFileName` — checks if the libName is a valid lib name or file name
/// and converts the lib name to the filename if needed.
pub fn get_lib_file_name(lib_name: &str) -> Option<String> {
    let lib_name = tspath::to_file_name_lower_case(lib_name);
    if lib_files_set().contains(lib_name.as_ref()) {
        return Some(lib_name.into_owned());
    }
    match LIB_MAP.get(lib_name.as_ref()) {
        Some(Value::Str(s)) => Some(s.clone()),
        _ => None,
    }
}

/// `TargetToLibMap` — Go returns the live map; callers only read it, so the
/// generated lookup function is exposed instead.
pub fn target_to_lib_map() -> impl Fn(ScriptTarget) -> Option<&'static str> {
    declarations::target_to_lib_map
}

/// `GetDefaultLibFileName`.
pub fn get_default_lib_file_name(options: &CompilerOptions) -> &'static str {
    match declarations::target_to_lib_map(options.get_emit_script_target()) {
        Some(name) => name,
        None => "lib.d.ts",
    }
}
