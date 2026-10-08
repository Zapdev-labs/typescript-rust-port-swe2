// Ported from tsc/internal/tsoptions/parsinghelpers.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;

use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_collections::OrderedMap;
use tsc_contentmapper::contentmapper::{Definition, Mapper};
use tsc_core::core;
use tsc_core::options_generated::{CompilerOptions, PluginImport};
use tsc_core::projectreference::ProjectReference;
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN, Tristate};
use tsc_diagnostics as diagnostics;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::commandlineoption::CommandLineOptionKind;
use crate::errors::{extra_key_diagnostics, extra_key_did_you_mean_diagnostics};
use crate::generated::options;
use crate::tsconfigparsing::{
    CommandLineOptionNameMap, ParsedCompilerOptions, UnresolvedCompilerOptionPaths,
    command_line_compiler_options_map, starts_with_config_dir_template,
};
use crate::value::Value;

/// `ParseTristate`.
pub fn parse_tristate(value: &Value) -> Tristate {
    if value.is_null() {
        return TS_UNKNOWN;
    }
    if let Value::Tristate(v) = value {
        return *v;
    }
    if *value == Value::Bool(true) {
        TS_TRUE
    } else {
        TS_FALSE
    }
}

/// `ParseStringArray` — Go returns `nil` unless `value` is `[]any`;
/// `Value::StringList` (`[]string`) is accepted too since a `[]string`
/// argument is already the target type (Go's assertion would fail, but the
/// only `[]string` source is `options.Set(name, []string{})` which the
/// tsconfig paths never feed back through here; keeping the coercion makes
/// command-line round-trips work — documented divergence if ever observed).
// PORT: `[]string` is accepted where Go would return nil; see note above.
pub fn parse_string_array(value: &Value) -> Option<Vec<String>> {
    match value {
        Value::List(arr) => Some(
            arr.iter()
                .filter_map(|v| v.as_str().map(str::to_string))
                .collect(),
        ),
        Value::StringList(arr) => Some(arr.clone()),
        _ => None,
    }
}

/// `parseStringMap` — Go: `value.(*OrderedMap[string, any])`, else nil.
pub fn parse_string_map(value: &Value) -> Option<OrderedMap<String, Option<Vec<String>>>> {
    let m = value.as_map()?;
    let mut result = OrderedMap::with_size_hint(m.size());
    for (k, v) in m.entries() {
        result.set(k.clone(), parse_string_array(v));
    }
    Some(result)
}

/// `ParseString`.
pub fn parse_string(value: &Value) -> String {
    value.as_str().unwrap_or_default().to_string()
}

/// `parseFileName`.
pub fn parse_file_name(value: &Value) -> RootedFilePath {
    let path = parse_string(value);
    if path.is_empty() {
        return RootedFilePath::default();
    }
    tspath::rooted_file_path_from_normalized(&path)
}

/// `parseDirectoryName`.
pub fn parse_directory_name(value: &Value) -> RootedDirectoryPath {
    let path = parse_string(value);
    if path.is_empty() {
        return RootedDirectoryPath::default();
    }
    tspath::rooted_directory_path_from_normalized(&path)
}

/// `parseFileOrDirectoryName`.
pub fn parse_file_or_directory_name(value: &Value) -> RootedPath {
    let path = parse_string(value);
    if path.is_empty() {
        return RootedPath::default();
    }
    tspath::rooted_path_from_normalized(&path)
}

/// `parseDirectoryNames`.
pub fn parse_directory_names(value: &Value) -> Option<Vec<RootedDirectoryPath>> {
    parse_string_array(value).map(|paths| {
        paths
            .into_iter()
            .map(|path| {
                if path.is_empty() {
                    RootedDirectoryPath::default()
                } else {
                    tspath::rooted_directory_path_from_normalized(&path)
                }
            })
            .collect()
    })
}

/// `parseNumber` — Go `*int` → `Option<i32>`.
// PORT: Go `int` is 64-bit; the only fields using this (`checkers`,
// `builders`, `maxNodeModuleJsDepth`) are `Option<i32>` in tsc_core.
pub fn parse_number(value: &Value) -> Option<i32> {
    match value {
        Value::Int(n) => Some(*n as i32),
        Value::Float(f) => Some(*f as i32),
        _ => None,
    }
}

/// `projectReferenceParseResult`.
pub(crate) struct ProjectReferenceParseResult {
    pub reference: ProjectReference,
    pub path: String,
    pub has_path: bool,
    pub path_valid: bool,
    pub has_circular: bool,
    pub circular_valid: bool,
}

/// `parseProjectReference`.
pub(crate) fn parse_project_reference(json: &Value) -> Option<ProjectReferenceParseResult> {
    let v = json.as_map()?;
    let mut result = ProjectReferenceParseResult {
        reference: ProjectReference::default(),
        path: String::new(),
        has_path: false,
        path_valid: false,
        has_circular: false,
        circular_valid: false,
    };
    if let Some(value) = v.get("path") {
        result.has_path = true;
        if let Some(path) = value.as_str() {
            result.path = path.to_string();
            result.path_valid = true;
        }
    }
    if let Some(value) = v.get("circular") {
        result.has_circular = true;
        if let Some(circular) = value.as_bool() {
            result.reference.circular = circular;
            result.circular_valid = true;
        }
    }
    Some(result)
}

/// `parseContentMapper`.
///
/// PORT: `mapper.Options` is `json.Marshal(options)`'d in Go (bytes); the
/// Rust `Definition.options` field is a `serde_json::Value`, so the raw map
/// is converted to `serde_json::Value` instead of bytes.
pub(crate) fn parse_content_mapper(value: &Value) -> (Option<Mapper>, Vec<DiagnosticRef>) {
    let Some(v) = value.as_map() else {
        return (None, Vec::new());
    };
    let mut errors: Vec<DiagnosticRef> = Vec::new();
    let mut mapper = Mapper::default();
    match v.get("package") {
        Some(pkg) => {
            if let Some(s) = pkg.as_str().filter(|s| !s.is_empty()) {
                mapper.package = s.to_string();
            } else {
                errors.push(new_compiler_diagnostic(
                    &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                    &[
                        Value::Str("contentMapper.package".to_string()),
                        Value::Str("string".to_string()),
                    ],
                ));
            }
        }
        None => {
            errors.push(new_compiler_diagnostic(
                &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                &[
                    Value::Str("contentMapper.package".to_string()),
                    Value::Str("string".to_string()),
                ],
            ));
        }
    }
    match v.get("extensions") {
        Some(extensions) => {
            if let Some(strs) = parse_string_array_strict(extensions) {
                mapper.extensions = Some(strs);
            } else {
                errors.push(new_compiler_diagnostic(
                    &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                    &[
                        Value::Str("contentMapper.extensions".to_string()),
                        Value::Str("string[]".to_string()),
                    ],
                ));
            }
        }
        None => {
            errors.push(new_compiler_diagnostic(
                &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                &[
                    Value::Str("contentMapper.extensions".to_string()),
                    Value::Str("string[]".to_string()),
                ],
            ));
        }
    }
    if let Some(options_v) = v.get("options") {
        if options_v.as_map().is_none() {
            errors.push(new_compiler_diagnostic(
                &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                &[
                    Value::Str("contentMapper.options".to_string()),
                    Value::Str("object".to_string()),
                ],
            ));
        } else {
            // Go: `mapper.Options, _ = json.Marshal(options)` — the marshal
            // error is discarded; serializing to serde_json::Value cannot
            // fail for this Value population.
            mapper.options = Some(crate::value::value_to_json(options_v));
        }
    }
    if !errors.is_empty() {
        return (None, errors);
    }
    (Some(mapper), errors)
}

/// `parseStringArrayStrict` returns the string slice only if value is an
/// array whose elements are all strings.
pub fn parse_string_array_strict(value: &Value) -> Option<Vec<String>> {
    let arr = value.as_list()?;
    let mut result = Vec::with_capacity(arr.len());
    for v in arr {
        result.push(v.as_str()?.to_string());
    }
    Some(result)
}

/// `parseJsonToStringKey`.
///
/// PORT: the `extends` double-set quirk is preserved — a string value is
/// wrapped in a list then immediately overwritten by the raw value, so the
/// raw value wins (Go writes `[]any{str}` then `v` over the same key).
pub fn parse_json_to_string_key(json: &Value) -> OrderedMap<String, Value> {
    let mut result = OrderedMap::with_size_hint(6);
    if let Some(m) = json.as_map() {
        for key in [
            "include",
            "exclude",
            "files",
            "references",
            "contentMappers",
        ] {
            if let Some(v) = m.get(key) {
                result.set(key.to_string(), v.clone());
            }
        }
        if let Some(v) = m.get("extends") {
            if let Some(str_) = v.as_str() {
                result.set(
                    "extends".to_string(),
                    Value::List(vec![Value::Str(str_.to_string())]),
                );
            }
            result.set("extends".to_string(), v.clone());
        }
        for key in ["compilerOptions", "excludes", "typeAcquisition"] {
            if let Some(v) = m.get(key) {
                result.set(key.to_string(), v.clone());
            }
        }
    }
    result
}

/// `optionParser` interface.
pub trait OptionParser {
    fn parse_option(&mut self, key: &str, value: &Value);
    fn unknown_option_diagnostic(&self) -> &'static diagnostics::Message;
    fn unknown_did_you_mean_diagnostic(&self) -> &'static diagnostics::Message;
}

/// `compilerOptionsParser`.
pub struct CompilerOptionsParser<'a> {
    pub compiler_options: &'a mut CompilerOptions,
    pub unresolved_paths: Option<&'a mut UnresolvedCompilerOptionPaths>,
}

impl OptionParser for CompilerOptionsParser<'_> {
    fn parse_option(&mut self, key: &str, value: &Value) {
        if let Some(unresolved) = self.unresolved_paths.as_deref_mut() {
            if compiler_option_contains_config_dir_template(key, value) {
                unresolved.insert(key.to_string(), value.clone());
                return;
            }
        }
        parse_compiler_options(key, value, self.compiler_options);
    }

    fn unknown_option_diagnostic(&self) -> &'static diagnostics::Message {
        extra_key_diagnostics("compilerOptions").unwrap()
    }

    fn unknown_did_you_mean_diagnostic(&self) -> &'static diagnostics::Message {
        extra_key_did_you_mean_diagnostics("compilerOptions").unwrap()
    }
}

/// `unresolvedCompilerOptionPaths` lives in `tsconfigparsing` (defined there
/// in Go too via `parsedCompilerOptions`).

/// `compilerOptionContainsConfigDirTemplate`.
pub fn compiler_option_contains_config_dir_template(key: &str, value: &Value) -> bool {
    let Some(option) =
        crate::tsconfigparsing::name_map_get(command_line_compiler_options_map(), key)
    else {
        return false;
    };
    let mut path_kind = option.path_kind;
    if option.kind == CommandLineOptionKind::List {
        let Some(element) = option.elements() else {
            return false;
        };
        path_kind = element.path_kind;
    }
    if !path_kind.is_rooted() {
        return false;
    }
    if option.kind == CommandLineOptionKind::List {
        return core::some(&parse_string_array(value).unwrap_or_default(), |s| {
            starts_with_config_dir_template(s)
        });
    }
    value.as_str().is_some_and(starts_with_config_dir_template)
}

/// `typeAcquisitionParser`.
pub struct TypeAcquisitionParser<'a> {
    pub type_acquisition: &'a mut tsc_core::options_generated::TypeAcquisition,
}

impl OptionParser for TypeAcquisitionParser<'_> {
    fn parse_option(&mut self, key: &str, value: &Value) {
        options::parse_type_acquisition(key, value, self.type_acquisition);
    }

    fn unknown_option_diagnostic(&self) -> &'static diagnostics::Message {
        extra_key_diagnostics("typeAcquisition").unwrap()
    }

    fn unknown_did_you_mean_diagnostic(&self) -> &'static diagnostics::Message {
        extra_key_did_you_mean_diagnostics("typeAcquisition").unwrap()
    }
}

/// `buildOptionsParser`.
pub struct BuildOptionsParser<'a> {
    pub build_options: &'a mut tsc_core::options_generated::BuildOptions,
}

impl OptionParser for BuildOptionsParser<'_> {
    fn parse_option(&mut self, key: &str, value: &Value) {
        options::parse_build_options(key, value, self.build_options);
    }

    fn unknown_option_diagnostic(&self) -> &'static diagnostics::Message {
        extra_key_diagnostics("buildOptions").unwrap()
    }

    fn unknown_did_you_mean_diagnostic(&self) -> &'static diagnostics::Message {
        extra_key_did_you_mean_diagnostics("buildOptions").unwrap()
    }
}

/// `ParseCompilerOptions`.
pub fn parse_compiler_options(key: &str, value: &Value, all_options: &mut CompilerOptions) {
    if value.is_null() {
        return;
    }
    options::parse_compiler_options(key, value, all_options);
}

/// `floatOrInt32ToFlag[T ~int32]`.
///
/// PORT: Go's second arm does `T(value.(float64))` — a raw int32 cast that
/// never validates. Rust enum newtypes are real enums, so an out-of-range
/// numeric (e.g. `"target": 999`) saturates to `T::default()` instead of
/// producing an invalid discriminant (Go would carry `T(999)`).
pub fn float_or_int32_to_flag<T>(value: &Value) -> T
where
    T: TryFrom<i32> + Default,
{
    T::try_from(value.as_i32_flag()).unwrap_or_default()
}

/// `mergeCompilerOptions` — merges the source compiler options into the
/// target compiler options with optional awareness of explicitly set null
/// values in the raw JSON.
pub fn merge_compiler_options(
    target_options: &mut CompilerOptions,
    source_options: Option<&CompilerOptions>,
    raw_source: &Value,
) {
    let Some(source_options) = source_options else {
        return;
    };

    // Collect explicitly null field names from raw JSON
    let mut explicit_null_fields = tsc_collections::Set::new();
    if let Some(raw_map) = raw_source.as_map() {
        // Options are nested under "compilerOptions" in both tsconfig.json
        // and wrapped command line options
        if let Some(compiler_options_raw) = raw_map.get("compilerOptions") {
            if let Some(compiler_options_map) = compiler_options_raw.as_map() {
                for (key, value) in compiler_options_map.entries() {
                    if value.is_null() {
                        explicit_null_fields.add(key.clone());
                    }
                }
            }
        }
    }

    options::merge_compiler_option_fields(target_options, source_options, &explicit_null_fields);
}

/// `mergeParsedCompilerOptions` — Go takes/returns `*parsedCompilerOptions`;
/// `None` models nil. A non-nil source allocates a fresh target when the
/// target is nil, so `Some` is returned whenever `source_options` is `Some`.
pub fn merge_parsed_compiler_options(
    target_options: Option<ParsedCompilerOptions>,
    source_options: Option<&ParsedCompilerOptions>,
    raw_source: &Value,
) -> Option<ParsedCompilerOptions> {
    let Some(source_options) = source_options else {
        return target_options;
    };
    let mut target_options = target_options.unwrap_or_else(|| ParsedCompilerOptions {
        compiler_options: Some(Box::new(CompilerOptions::default())),
        unresolved_paths: UnresolvedCompilerOptionPaths::new(),
    });
    merge_compiler_options(
        target_options
            .compiler_options
            .as_deref_mut()
            .expect("parsedCompilerOptions.CompilerOptions set"),
        source_options.compiler_options.as_deref(),
        raw_source,
    );
    if let Some(raw_map) = raw_source.as_map() {
        if let Some(compiler_options_raw) = raw_map.get("compilerOptions") {
            if let Some(compiler_options_map) = compiler_options_raw.as_map() {
                for key in compiler_options_map.keys() {
                    target_options.unresolved_paths.remove(key);
                }
            }
        }
    }
    for (k, v) in source_options.unresolved_paths.iter() {
        target_options.unresolved_paths.insert(k.clone(), v.clone());
    }
    Some(target_options)
}

/// `convertToOptionsWithAbsolutePaths` — done pre-conversion, as in Go
/// (see the `!!!` note in the Go source).
pub fn convert_to_options_with_absolute_paths(
    options_base: &mut OrderedMap<String, Value>,
    option_map: &CommandLineOptionNameMap,
    cwd: RootedDirectoryPath,
) {
    // PORT: Go mutates `optionsBase` inside the `Entries()` iterator (the Go
    // OrderedMap iterator is live); Rust borrows prevent that, so the keys
    // and replacements are collected first. `Set` on an existing key does
    // not change iteration order in either implementation.
    let replacements: Vec<(String, Value)> = options_base
        .entries()
        .filter_map(|(o, v)| {
            convert_option_to_absolute_path(o, v, option_map, &cwd).map(|r| (o.clone(), r))
        })
        .collect();
    for (o, result) in replacements {
        options_base.set(o, result);
    }
}

/// `ConvertOptionToAbsolutePath` — returns the converted value and whether
/// conversion applied (Go's `(any, bool)`).
pub fn convert_option_to_absolute_path(
    o: &str,
    v: &Value,
    option_map: &CommandLineOptionNameMap,
    cwd: &RootedDirectoryPath,
) -> Option<Value> {
    let option = option_map.get(o)?;
    if option.kind == CommandLineOptionKind::List {
        let element = option.elements()?;
        if element.is_file_path {
            if let Some(arr) = v.as_string_list() {
                return Some(Value::StringList(
                    arr.iter()
                        .map(|item| tspath::get_normalized_absolute_path(item, cwd).into_owned())
                        .collect(),
                ));
            }
            if let Some(arr) = v.as_list() {
                return Some(Value::List(
                    arr.iter()
                        .map(|item| {
                            if let Some(s) = item.as_str() {
                                Value::Str(
                                    tspath::get_normalized_absolute_path(s, cwd).into_owned(),
                                )
                            } else {
                                item.clone()
                            }
                        })
                        .collect(),
                ));
            }
        }
    } else if option.is_file_path {
        if let Some(value) = v.as_str() {
            return Some(Value::Str(
                tspath::get_normalized_absolute_path(value, cwd).into_owned(),
            ));
        }
    }
    None
}

// keep imports used
#[allow(dead_code)]
type _Unused = (
    PluginImport,
    HashMap<String, Value>,
    RootedFilePath,
    Definition,
);
