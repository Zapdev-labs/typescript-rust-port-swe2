// Ported from tsc/internal/module/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::LazyLock;

use tsc_ast::ast_generated::SourceFile;
use tsc_core::options_generated::{CompilerOptions, JsxEmit};
use tsc_diagnostics::Message;
use tsc_semver::{Version, must_parse, try_parse_version_range};
use tsc_tspath::{self, RootedDirectoryPath, RootedFilePath};

use crate::resolver::move_to_next_directory_separator_if_available;

/// `var typeScriptVersion = semver.MustParse(core.Version())`
static TYPE_SCRIPT_VERSION: LazyLock<Version> =
    LazyLock::new(|| must_parse(tsc_core::version::version()));

/// `const InferredTypesContainingFile = "__inferred type names__.ts"`
pub const INFERRED_TYPES_CONTAINING_FILE: &str = "__inferred type names__.ts";

/// `func IsApplicableVersionedTypesKey(key string) bool`
pub fn is_applicable_versioned_types_key(key: &str) -> bool {
    if !key.starts_with("types@") {
        return false;
    }
    let (range, ok) = try_parse_version_range(&key["types@".len()..]);
    if !ok {
        return false;
    }
    range.test(Some(&TYPE_SCRIPT_VERSION))
}

/// `func NodeModulePackageRootForFile(resolved tspath.RootedFilePath) tspath.RootedDirectoryPath`
pub fn node_module_package_root_for_file(resolved: &RootedFilePath) -> RootedDirectoryPath {
    parse_node_module_package_root(resolved.as_string(), false /*isDirectory*/)
}

/// `func NodeModulePackageRootForDirectory(resolved tspath.RootedDirectoryPath) tspath.RootedDirectoryPath`
pub fn node_module_package_root_for_directory(
    resolved: &RootedDirectoryPath,
) -> RootedDirectoryPath {
    parse_node_module_package_root(resolved.as_string(), true /*isDirectory*/)
}

fn parse_node_module_package_root(path: &str, is_directory: bool) -> RootedDirectoryPath {
    let Some(idx) = path.rfind("/node_modules/") else {
        return RootedDirectoryPath::default();
    };

    let index_after_node_modules = idx + "/node_modules/".len();
    let mut index_after_package_name =
        move_to_next_directory_separator_if_available(path, index_after_node_modules, is_directory);
    // PORT: `path[indexAfterNodeModules] == '@'` panics on a path ending in
    // "/node_modules/" — the byte index preserves Go's panic semantics.
    if path.as_bytes()[index_after_node_modules] == b'@' {
        index_after_package_name = move_to_next_directory_separator_if_available(
            path,
            index_after_package_name,
            is_directory,
        );
    }
    tsc_tspath::rooted_directory_path_from_absolute(&path[..index_after_package_name])
}

/// `func ParsePackageName(moduleName string) (packageName, rest string)`
pub fn parse_package_name(module_name: &str) -> (&str, &str) {
    let mut idx = module_name.find('/').map_or(-1i64, |i| i as i64);
    if !module_name.is_empty() && module_name.as_bytes()[0] == b'@' {
        let offset = (idx + 1) as usize;
        idx = module_name[offset..]
            .find('/')
            .map_or(-1, |i| i as i64 + offset as i64);
    }
    if idx == -1 {
        return (module_name, "");
    }
    let idx = idx as usize;
    (&module_name[..idx], &module_name[idx + 1..])
}

/// `func MangleScopedPackageName(packageName string) string`
pub fn mangle_scoped_package_name(package_name: &str) -> String {
    if !package_name.is_empty() && package_name.as_bytes()[0] == b'@' {
        match package_name.find('/') {
            None => return package_name.to_string(),
            Some(idx) => {
                return format!("{}__{}", &package_name[1..idx], &package_name[idx + 1..]);
            }
        }
    }
    package_name.to_string()
}

/// `func UnmangleScopedPackageName(packageName string) string`
pub fn unmangle_scoped_package_name(package_name: &str) -> String {
    match package_name.split_once("__") {
        Some((before, after)) => format!("@{before}/{after}"),
        None => package_name.to_string(),
    }
}

/// `func GetTypesPackageName(packageName string) string`
pub fn get_types_package_name(package_name: &str) -> String {
    format!("@types/{}", mangle_scoped_package_name(package_name))
}

/// `func GetPackageNameFromTypesPackageName(mangledName string) string`
pub fn get_package_name_from_types_package_name(mangled_name: &str) -> String {
    match mangled_name.strip_prefix("@types/") {
        Some(without_at_type_prefix) => unmangle_scoped_package_name(without_at_type_prefix),
        None => mangled_name.to_string(),
    }
}

/// `func ComparePatternKeys(a, b string) int`
///
/// Returns -1/0/1 ordering like `slices.SortFunc` expects.
pub fn compare_pattern_keys(a: &str, b: &str) -> std::cmp::Ordering {
    let a_pattern_index = a.find('*');
    let b_pattern_index = b.find('*');
    let base_len_a = a_pattern_index.map_or(a.len(), |i| i + 1);
    let base_len_b = b_pattern_index.map_or(b.len(), |i| i + 1);

    use std::cmp::Ordering::*;
    if base_len_a > base_len_b {
        return Less;
    }
    if base_len_b > base_len_a {
        return Greater;
    }
    if a_pattern_index.is_none() {
        return Greater;
    }
    if b_pattern_index.is_none() {
        return Less;
    }
    if a.len() > b.len() {
        return Less;
    }
    if b.len() > a.len() {
        return Greater;
    }
    Equal
}

/// Returns a DiagnosticMessage if we won't include a resolved module due to its extension.
/// The DiagnosticMessage's parameters are the imported module name, and the filename it resolved to.
/// This returns a diagnostic even if the module will be an untyped module.
///
/// `func GetResolutionDiagnostic(options *core.CompilerOptions, resolvedModule *ResolvedModule, file *ast.SourceFile) *diagnostics.Message`
pub fn get_resolution_diagnostic(
    options: &CompilerOptions,
    resolved_module: &crate::types::ResolvedModule,
    file: &SourceFile,
) -> Option<&'static Message> {
    let need_jsx = || {
        if options.jsx != JsxEmit::None {
            return None;
        }
        Some(&tsc_diagnostics::Module_0_was_resolved_to_1_but_jsx_is_not_set)
    };

    let need_allow_js = || {
        if options.get_allow_js()
            || !options
                .no_implicit_any
                .default_if_unknown(options.strict)
                .is_true()
        {
            return None;
        }
        Some(
            &tsc_diagnostics::Could_not_find_a_declaration_file_for_module_0_1_implicitly_has_an_any_type,
        )
    };

    let need_resolve_json_module = || {
        if options.get_resolve_json_module() {
            return None;
        }
        Some(&tsc_diagnostics::Module_0_was_resolved_to_1_but_resolveJsonModule_is_not_used)
    };

    let need_allow_arbitrary_extensions = || {
        if file.is_declaration_file || options.allow_arbitrary_extensions.is_true() {
            return None;
        }
        Some(&tsc_diagnostics::Module_0_was_resolved_to_1_but_allowArbitraryExtensions_is_not_set)
    };

    if resolved_module.resolved_using_extra_extensions {
        return None;
    }

    match resolved_module.extension.as_str() {
        tsc_tspath::EXTENSION_TS
        | tsc_tspath::EXTENSION_DTS
        | tsc_tspath::EXTENSION_MTS
        | tsc_tspath::EXTENSION_DMTS
        | tsc_tspath::EXTENSION_CTS
        | tsc_tspath::EXTENSION_DCTS => {
            // These are always allowed.
            None
        }
        tsc_tspath::EXTENSION_TSX => need_jsx(),
        tsc_tspath::EXTENSION_JSX => need_jsx().or_else(need_allow_js),
        tsc_tspath::EXTENSION_JS | tsc_tspath::EXTENSION_MJS | tsc_tspath::EXTENSION_CJS => {
            need_allow_js()
        }
        tsc_tspath::EXTENSION_JSON => need_resolve_json_module(),
        _ => need_allow_arbitrary_extensions(),
    }
}

/// TryGetJSExtensionForFile maps TS/JS/DTS extensions to the output JS-side extension.
/// Returns an empty string if the extension is unsupported.
///
/// `func TryGetJSExtensionForFile(fileName string, options *core.CompilerOptions) string`
pub fn try_get_js_extension_for_file(file_name: &str, options: &CompilerOptions) -> &'static str {
    let ext = tsc_tspath::try_get_extension_from_path(file_name);
    match ext {
        tsc_tspath::EXTENSION_TS | tsc_tspath::EXTENSION_DTS => tsc_tspath::EXTENSION_JS,
        tsc_tspath::EXTENSION_TSX => {
            if options.jsx == JsxEmit::Preserve {
                return tsc_tspath::EXTENSION_JSX;
            }
            tsc_tspath::EXTENSION_JS
        }
        tsc_tspath::EXTENSION_JS | tsc_tspath::EXTENSION_JSX | tsc_tspath::EXTENSION_JSON => {
            // PORT: returns the same static extension constant Go returns.
            match ext {
                tsc_tspath::EXTENSION_JS => tsc_tspath::EXTENSION_JS,
                tsc_tspath::EXTENSION_JSX => tsc_tspath::EXTENSION_JSX,
                _ => tsc_tspath::EXTENSION_JSON,
            }
        }
        tsc_tspath::EXTENSION_DMTS | tsc_tspath::EXTENSION_MTS | tsc_tspath::EXTENSION_MJS => {
            tsc_tspath::EXTENSION_MJS
        }
        tsc_tspath::EXTENSION_DCTS | tsc_tspath::EXTENSION_CTS | tsc_tspath::EXTENSION_CJS => {
            tsc_tspath::EXTENSION_CJS
        }
        _ => "",
    }
}

/// `func TryGetJSExtensionForFileName(fileName tspath.RootedFilePath, options *core.CompilerOptions) string`
pub fn try_get_js_extension_for_file_name(
    file_name: &RootedFilePath,
    options: &CompilerOptions,
) -> &'static str {
    try_get_js_extension_for_file(file_name.as_string(), options)
}
