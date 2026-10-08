// Ported from tsc/internal/tsoptions/tsconfigparsing.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;
use std::sync::{Arc, LazyLock, Mutex};

use tsc_ast::ast_generated::PropertyAssignment;
use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic, new_diagnostic};
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::utilities::{
    get_text_of_property_name, is_computed_non_literal_name, try_get_text_of_property_name,
};
use tsc_ast::{Kind, Node, NodeFactory, NodeId};
use tsc_collections::OrderedMap;
use tsc_contentmapper::{Mapper, OptionPathSegment};
use tsc_core::core;
use tsc_core::options_generated::{CompilerOptions, TypeAcquisition};
use tsc_core::projectreference::ProjectReference;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::TextRange;
use tsc_diagnostics::{self as diagnostics, Message};
use tsc_module as module;
use tsc_parser as parser;
use tsc_scanner::scanner::skip_trivia;
use tsc_tspath::{
    self as tspath, CaseSensitivity, FileSpec, PathKey, PathPattern, RootedDirectoryPath,
    RootedFilePath,
};
use tsc_vfs::Vfs;
use tsc_vfs::vfsmatch;

use crate::commandlineoption::{CommandLineOptionKind, CommandLineOptionRef, ExtraValidation};
use crate::contentmappers::resolve_content_mapper_manifest;
use crate::errors::{
    create_diagnostic_for_invalid_enum_type, create_diagnostic_for_node_in_source_file,
    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic, create_unknown_option_error,
    extra_key_diagnostics, extra_key_did_you_mean_diagnostics,
    get_compiler_option_value_type_string,
};
use crate::generated::{declarations, options};
use crate::parsedcommandline::ParsedCommandLine;
use crate::parsinghelpers::parse_project_reference;
use crate::parsinghelpers::{
    self, OptionParser, merge_parsed_compiler_options, parse_json_to_string_key,
};
use crate::value::Value;

/// `configDirTemplate`.
pub const CONFIG_DIR_TEMPLATE: &str = "${configDir}";

/// `startsWithConfigDirTemplate` — Go lowercases both sides (`strings.HasPrefix(
/// strings.ToLower(value), strings.ToLower(configDirTemplate))`), so the
/// prefix check is case-insensitive even though the substitution in
/// `getSubstitutedPathWithConfigDirTemplate` only replaces the exact
/// `${configDir}` casing — a deliberate Go quirk preserved here.
pub fn starts_with_config_dir_template(value: &str) -> bool {
    value
        .get(..CONFIG_DIR_TEMPLATE.len())
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case(CONFIG_DIR_TEMPLATE))
}

/// `getSubstitutedPathWithConfigDirTemplate`.
pub(crate) fn get_substituted_path_with_config_dir_template(
    value: &str,
    base_path: &RootedDirectoryPath,
) -> String {
    // TODO: Match the case-insensitive prefix check; Replace currently only
    // substitutes "${configDir}" with this exact casing.
    tspath::get_normalized_absolute_path(&value.replacen(CONFIG_DIR_TEMPLATE, "./", 1), base_path)
        .into_owned()
}

/// `getSubstitutedStringArrayWithConfigDirTemplate[T ~string]` — returns
/// `None` when no element needed substitution (the `result == nil` case),
/// otherwise a clone of `list` with the prefixed entries substituted.
pub(crate) fn get_substituted_string_array_with_config_dir_template(
    list: &[String],
    base_path: &RootedDirectoryPath,
) -> Option<Vec<String>> {
    let mut result: Option<Vec<String>> = None;
    for (i, element) in list.iter().enumerate() {
        if starts_with_config_dir_template(element) {
            let result = result.get_or_insert_with(|| list.to_vec());
            result[i] = get_substituted_path_with_config_dir_template(element, base_path);
        }
    }
    result
}

/// `getSubstitutedStringArrayWithConfigDirTemplateOpt` — helper used by the
/// generated option-parsing tables (`[T ~string]` over `[]T` slices).
pub(crate) fn get_substituted_string_array_with_config_dir_template_opt(
    list: Option<Vec<String>>,
    base_path: &RootedDirectoryPath,
) -> Option<Vec<String>> {
    let list = list?;
    get_substituted_string_array_with_config_dir_template(&list, base_path).or(Some(list))
}

// ---------------------------------------------------------------------------
// TsConfigSourceFile
// ---------------------------------------------------------------------------

/// `type TsConfigSourceFile struct`.
///
/// PORT: `SourceFile *ast.SourceFile` splits into `source_file: NodeId` +
/// `nodes: Vec<Node>` (the arena owning every `NodeId` in the file). The two
/// fields Go mutates during/after parsing (`ExtendedSourceFiles`,
/// `configFileSpecs`) live behind `Mutex` so the file can be shared through
/// `Arc` in `ParsedCommandLine`/`ExtendedConfigCacheEntry`, exactly as the Go
/// pointer is.
pub struct TsConfigSourceFile {
    pub extended_source_files: Mutex<Vec<RootedFilePath>>,
    pub config_file_specs: Mutex<Option<Arc<ConfigFileSpecs>>>,
    pub source_file: NodeId,
    pub nodes: Vec<Node>,
}

impl std::fmt::Debug for TsConfigSourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TsConfigSourceFile")
            .field("file_name", &self.file_name())
            .finish_non_exhaustive()
    }
}

impl TsConfigSourceFile {
    /// The `*ast.SourceFile` view bundled with its arena.
    pub fn as_ctx(&self) -> SourceFileCtx<'_> {
        SourceFileCtx {
            file: self.source_file,
            nodes: &self.nodes,
        }
    }

    /// `source_file` arena indexing for `&TsConfigSourceFile`/`Arc` callers.
    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id]
    }

    /// `sourceFile.SourceFile.FileName()`.
    pub fn file_name(&self) -> &RootedFilePath {
        self.nodes[self.source_file].as_source_file().file_name()
    }

    /// `sourceFile.SourceFile.Text()`.
    pub fn text(&self) -> &str {
        self.nodes[self.source_file].as_source_file().text()
    }

    /// `sourceFile.SourceFile.Diagnostics()` — parse diagnostics stored on
    /// the node.
    pub fn diagnostics(&self) -> &[DiagnosticRef] {
        self.nodes[self.source_file].as_source_file().diagnostics()
    }

    /// `sourceFile.ExtendedSourceFiles` — cloned; Go callers only read it
    /// after parsing completes.
    pub fn extended_source_files(&self) -> Vec<RootedFilePath> {
        self.extended_source_files
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// `sourceFile.configFileSpecs`.
    pub fn config_file_specs(&self) -> Option<Arc<ConfigFileSpecs>> {
        self.config_file_specs
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }
}

/// `tsconfigToSourceFile` result — Go's `*ast.SourceFile` parameter becomes
/// the `NodeId` + arena pair.
#[derive(Clone, Copy)]
pub struct SourceFileCtx<'a> {
    pub file: NodeId,
    pub nodes: &'a [Node],
}

impl<'a> SourceFileCtx<'a> {
    pub fn node(&self, id: NodeId) -> &'a Node {
        &self.nodes[id]
    }

    pub fn file_name(&self) -> &'a RootedFilePath {
        self.node(self.file).as_source_file().file_name()
    }

    pub fn text(&self) -> &'a str {
        self.node(self.file).as_source_file().text()
    }
}

/// `tsconfigToSourceFile`.
pub(crate) fn tsconfig_to_source_file<'a>(
    tsconfig_source_file: Option<&'a TsConfigSourceFile>,
) -> Option<SourceFileCtx<'a>> {
    tsconfig_source_file.map(|s| s.as_ctx())
}

/// `NewTsconfigSourceFileFromFilePath`.
pub fn new_tsconfig_source_file_from_file_path(
    config_file_name: RootedFilePath,
    config_path: PathKey,
    config_source_text: &str,
) -> TsConfigSourceFile {
    let (source_file, nodes) = parser::parse_source_file(
        SourceFileParseOptions {
            file_name: config_file_name,
            path_key: config_path,
            ..Default::default()
        },
        config_source_text,
        ScriptKind::Json,
    );
    TsConfigSourceFile {
        source_file,
        nodes,
        extended_source_files: Mutex::new(Vec::new()),
        config_file_specs: Mutex::new(None),
    }
}

// ---------------------------------------------------------------------------
// configFileSpecs
// ---------------------------------------------------------------------------

/// `type configFileSpecs struct`.
#[derive(Clone, Default)]
pub struct ConfigFileSpecs {
    /// Go `any` — the raw `"files"`/`"include"`/`"exclude"` values.
    pub files_specs: Option<Value>,
    /// Present to report errors (user specified specs); `validated_include_specs`
    /// are used for file name matching.
    pub include_specs: Option<Value>,
    pub exclude_specs: Option<Value>,
    pub validated_files_spec: Vec<FileSpec>,
    pub validated_file_names: Vec<RootedFilePath>,
    // PORT: Go `map[tspath.PathKey]tspath.FileSpec` — iteration order is
    // never observed.
    pub file_spec_by_path: HashMap<PathKey, FileSpec>,
    pub validated_include_specs: Vec<PathPattern>,
    pub validated_exclude_specs: Vec<PathPattern>,
    pub validated_files_spec_before_substitution: Vec<FileSpec>,
    pub validated_include_specs_before_substitution: Vec<PathPattern>,
    pub is_default_include_spec: bool,
}

impl ConfigFileSpecs {
    /// `getMatchedIncludeSpec`.
    pub fn get_matched_include_spec(
        &self,
        file_name: &RootedFilePath,
        current_directory: &RootedDirectoryPath,
        case_sensitivity: CaseSensitivity,
    ) -> PathPattern {
        if self.validated_include_specs.is_empty() {
            return PathPattern::default();
        }
        for (index, spec) in self.validated_include_specs.iter().enumerate() {
            let include_matcher = vfsmatch::new_spec_matcher(
                &[spec.clone()],
                current_directory,
                vfsmatch::USAGE_FILES,
                case_sensitivity,
            );
            if include_matcher
                .as_ref()
                .is_some_and(|m| m.match_file_name(file_name))
            {
                return self.validated_include_specs_before_substitution[index].clone();
            }
        }
        PathPattern::default()
    }

    /// `getMatchedFileSpec`.
    pub fn get_matched_file_spec(&self, file_path: &PathKey) -> FileSpec {
        self.file_spec_by_path
            .get(file_path)
            .cloned()
            .unwrap_or_default()
    }
}

// ---------------------------------------------------------------------------
// ExtendedConfigCache
// ---------------------------------------------------------------------------

/// `type ExtendedConfigCache interface`.
///
/// PORT: Go `GetExtendedConfig` always returns a non-nil entry; Rust
/// implementations may return `None` to defer to `parse_extended_config`
/// (equivalent to a cache miss).
pub trait ExtendedConfigCache {
    fn get_extended_config(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        resolution_stack: &[PathKey],
        fs: &Arc<dyn Vfs>,
    ) -> Option<ExtendedConfigCacheEntry>;
}

/// `type ExtendedConfigCacheEntry struct`.
#[derive(Clone, Default)]
pub struct ExtendedConfigCacheEntry {
    pub extended_result: Option<Arc<TsConfigSourceFile>>,
    pub extended_config: Option<Arc<ParsedTsconfig>>,
    pub errors: Vec<DiagnosticRef>,
}

impl std::fmt::Debug for ExtendedConfigCacheEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedConfigCacheEntry")
            .field("extended_result", &self.extended_result)
            .finish_non_exhaustive()
    }
}

impl ExtendedConfigCacheEntry {
    /// `(e) ExtendedFileNames`.
    pub fn extended_file_names(&self) -> Vec<RootedFilePath> {
        self.extended_result
            .as_ref()
            .map(|r| r.extended_source_files())
            .unwrap_or_default()
    }
}

// ---------------------------------------------------------------------------
// parsedTsconfig / parsedCompilerOptions / extendsResult
// ---------------------------------------------------------------------------

/// `type parsedTsconfig struct`.
#[derive(Default)]
pub struct ParsedTsconfig {
    /// PORT: Go `any`; `Value` covers every produced shape.
    pub raw: Option<Value>,
    /// `options *parsedCompilerOptions` — `None` is Go nil (circularity path).
    pub options: Option<ParsedCompilerOptions>,
    /// `typeAcquisition *core.TypeAcquisition`.
    pub type_acquisition: Option<Box<TypeAcquisition>>,
    /// `extendedConfigPaths []tspath.RootedFilePath`.
    pub extended_config_paths: Vec<RootedFilePath>,
}

/// `type parsedCompilerOptions struct` — Go embeds `*core.CompilerOptions`.
#[derive(Default)]
pub struct ParsedCompilerOptions {
    /// `*core.CompilerOptions` — `None` is Go nil.
    pub compiler_options: Option<Box<CompilerOptions>>,
    /// `unresolvedPaths` — `Value`s stored verbatim; `clear`ed after the
    /// config-dir substitution pass.
    pub unresolved_paths: UnresolvedCompilerOptionPaths,
}

/// `type unresolvedCompilerOptionPaths map[string]any`.
pub type UnresolvedCompilerOptionPaths = HashMap<String, Value>;

impl ParsedCompilerOptions {
    /// `(o) ParseOption`.
    pub fn parse_option(&mut self, key: &str, value: &Value) {
        let unresolved_paths = if !self.unresolved_paths.is_empty() || true {
            // Go: `o.unresolvedPaths != nil` — always non-nil here.
            Some(&mut self.unresolved_paths)
        } else {
            None
        };
        parsinghelpers::CompilerOptionsParser {
            compiler_options: self
                .compiler_options
                .as_deref_mut()
                .expect("parsedCompilerOptions.CompilerOptions is always set"),
            unresolved_paths,
        }
        .parse_option(key, value);
    }
}

/// `type extendsResult struct`.
#[derive(Default)]
pub(crate) struct ExtendsResult {
    pub options: Option<ParsedCompilerOptions>,
    /// PORT: `[]any` → `Vec<Value>`.
    pub include: Option<Vec<Value>>,
    pub exclude: Option<Vec<Value>>,
    pub files: Option<Vec<Value>>,
    pub compile_on_save: bool,
    pub extended_source_files: tsc_collections::Set<RootedFilePath>,
    /// PORT: `contentMappers []any` — raw, unvalidated elements.
    pub content_mappers: Option<Vec<Value>>,
}

// ---------------------------------------------------------------------------
// CommandLineOptionNameMap
// ---------------------------------------------------------------------------

/// `type CommandLineOptionNameMap map[string]*CommandLineOption`.
///
/// PORT: `get` checks the exact key first and then its lowercased form — Go
/// stores both spellings in `commandLineOptionsToMap`.
pub type CommandLineOptionNameMap = HashMap<String, CommandLineOptionRef>;

pub fn name_map_get(map: &CommandLineOptionNameMap, name: &str) -> Option<CommandLineOptionRef> {
    map.get(name)
        .or_else(|| map.get(&name.to_lowercase()))
        .copied()
}

pub fn name_map_get_spelling_suggestion(
    map: &CommandLineOptionNameMap,
    name: &str,
) -> Option<CommandLineOptionRef> {
    core::get_spelling_suggestion(
        name,
        map.values().copied(),
        |option: &CommandLineOptionRef| option.name,
        |a: &CommandLineOptionRef, b: &CommandLineOptionRef| a.name.cmp(b.name) as i32,
    )
}

/// `commandLineOptionsToMap`.
pub fn command_line_options_to_map(
    compiler_options: &[CommandLineOptionRef],
) -> CommandLineOptionNameMap {
    let mut result = HashMap::with_capacity(compiler_options.len() * 2);
    for option in compiler_options {
        result.insert(option.name.to_string(), *option);
        result.insert(option.name.to_lowercase(), *option);
    }
    result
}

static COMMAND_LINE_COMPILER_OPTIONS_MAP: LazyLock<CommandLineOptionNameMap> =
    LazyLock::new(|| {
        command_line_options_to_map(&declarations::options_declarations().collect::<Vec<_>>())
    });

/// `var CommandLineCompilerOptionsMap`.
pub fn command_line_compiler_options_map() -> &'static CommandLineOptionNameMap {
    &COMMAND_LINE_COMPILER_OPTIONS_MAP
}

// ---------------------------------------------------------------------------
// jsonConversionNotifier + JSON → any conversion
// ---------------------------------------------------------------------------

/// The `onPropertySet` half of `jsonConversionNotifier`. A trait lets
/// `OwnConfigState` expose the callback directly — Go closures become a
/// method on the owning state.
pub(crate) trait OnPropertySet {
    fn on_property_set(
        &mut self,
        key_text: &str,
        value: &Value,
        property_assignment: NodeId,
        parent_option: Option<CommandLineOptionRef>,
        option: Option<CommandLineOptionRef>,
    ) -> (Value, Vec<DiagnosticRef>);
}

/// `jsonConversionNotifier`.
pub(crate) struct JsonConversionNotifier<'a> {
    pub root_options: Option<CommandLineOptionRef>,
    pub on_property_set: &'a mut dyn OnPropertySet,
}

/// `isCompilerOptionsValue`.
fn is_compiler_options_value(option: Option<CommandLineOptionRef>, value: &Value) -> bool {
    let Some(option) = option else {
        return false;
    };
    if value.is_null() {
        return !option.disallow_null_or_undefined();
    }
    match option.kind {
        CommandLineOptionKind::List => matches!(value, Value::List(_)),
        CommandLineOptionKind::ListOrElement => {
            if matches!(value, Value::List(_)) {
                true
            } else {
                is_compiler_options_value(option.elements(), value)
            }
        }
        CommandLineOptionKind::String => matches!(value, Value::Str(_)),
        CommandLineOptionKind::Boolean => matches!(value, Value::Bool(_)),
        CommandLineOptionKind::Number => matches!(value, Value::Float(_)),
        CommandLineOptionKind::Object => matches!(value, Value::Map(_)),
        CommandLineOptionKind::Enum => matches!(value, Value::Str(_)),
    }
}

/// `validateJsonOptionValue`.
pub(crate) fn validate_json_option_value(
    opt: CommandLineOptionRef,
    val: &Value,
    value_expression: Option<NodeId>,
    source_file: Option<SourceFileCtx<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    if val.is_null() {
        return (Value::Null, Vec::new());
    }

    let mut errors = Vec::new();
    if opt.extra_validation == Some(ExtraValidation::Locale)
        && !tsc_locale::parse(val.as_str().unwrap_or_default()).1
    {
        errors.push(
            create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                source_file,
                value_expression,
                &diagnostics::Locale_must_be_an_IETF_BCP_47_language_tag_Examples_Colon_0_1,
                &[Value::Str("en".into()), Value::Str("ja-jp".into())],
            ),
        );
    }

    if !errors.is_empty() {
        return (Value::Null, errors);
    }
    (val.clone(), Vec::new())
}

/// `convertJsonOptionOfListType`.
fn convert_json_option_of_list_type(
    option: CommandLineOptionRef,
    values: &Value,
    base_path: &RootedDirectoryPath,
    property_assignment: Option<NodeId>,
    value_expression: Option<NodeId>,
    source_file: Option<SourceFileCtx<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    let mut errors = Vec::new();
    if let Some(values) = values.as_list() {
        let element_option = option.elements().expect("list has elements");
        let mut mapped_values = Vec::with_capacity(values.len());
        for (index, v) in values.iter().enumerate() {
            let expression = value_expression.and_then(|value_expression| {
                source_file
                    .map(|sf| sf.node(value_expression))
                    .filter(|n| n.kind == Kind::ArrayLiteralExpression)
                    .and_then(|n| {
                        n.as_array_literal_expression()
                            .elements
                            .as_ref()
                            .and_then(|l| l.nodes.get(index))
                            .copied()
                    })
            });
            let (result, err) = convert_json_option(
                element_option,
                v,
                base_path,
                property_assignment,
                expression,
                source_file,
            );
            errors.extend(err);
            mapped_values.push(result);
        }
        let filtered_values = if option.list_preserve_falsy_values {
            mapped_values
        } else {
            mapped_values
                .into_iter()
                .filter(|v| {
                    !(v.is_null()
                        || *v == Value::Bool(false)
                        || *v == Value::Int(0)
                        || v.as_str() == Some(""))
                })
                .collect()
        };
        return (Value::List(filtered_values), errors);
    }
    (Value::Null, errors)
}

/// `normalizeNonListOptionValue`.
fn normalize_non_list_option_value(
    option: CommandLineOptionRef,
    base_path: &RootedDirectoryPath,
    value: Value,
) -> Value {
    if option.path_kind.is_rooted() {
        let mut path = tspath::normalize_slashes(value.as_str().unwrap_or_default()).into_owned();
        if !starts_with_config_dir_template(&path) {
            path = tspath::get_normalized_absolute_path(&path, base_path).into_owned();
        }
        if path.is_empty() {
            path = ".".to_string();
        }
        return Value::Str(path);
    }
    value
}

/// `convertJsonOption`.
pub(crate) fn convert_json_option(
    opt: CommandLineOptionRef,
    value: &Value,
    base_path: &RootedDirectoryPath,
    property_assignment: Option<NodeId>,
    value_expression: Option<NodeId>,
    source_file: Option<SourceFileCtx<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    if opt.is_command_line_only {
        let node_value = property_assignment.and_then(|pa| {
            source_file
                .expect("propertyAssignment implies sourceFile")
                .node(pa)
                .as_property_assignment()
                .named_member_base
                .name
        });
        if source_file.is_none() && node_value.is_none() {
            return (
                Value::Null,
                vec![new_compiler_diagnostic(
                    &diagnostics::Option_0_can_only_be_specified_on_command_line,
                    &[Value::Str(opt.name.into())],
                )],
            );
        }
        return (
            Value::Null,
            vec![
                create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                    source_file,
                    node_value,
                    &diagnostics::Option_0_can_only_be_specified_on_command_line,
                    &[Value::Str(opt.name.into())],
                ),
            ],
        );
    }
    if is_compiler_options_value(Some(opt), value) {
        match opt.kind {
            CommandLineOptionKind::List => {
                // as ArrayLiteralExpression | undefined
                return convert_json_option_of_list_type(
                    opt,
                    value,
                    base_path,
                    property_assignment,
                    value_expression,
                    source_file,
                );
            }
            CommandLineOptionKind::ListOrElement => {
                if matches!(value, Value::List(_)) {
                    return convert_json_option_of_list_type(
                        opt,
                        value,
                        base_path,
                        property_assignment,
                        value_expression,
                        source_file,
                    );
                }
                return convert_json_option(
                    opt.elements().expect("listOrElement has elements"),
                    value,
                    base_path,
                    property_assignment,
                    value_expression,
                    source_file,
                );
            }
            CommandLineOptionKind::Enum => {
                if value.is_null() {
                    return (Value::Null, Vec::new());
                }
                return convert_json_option_of_enum_type(
                    opt,
                    value.as_str().unwrap_or_default(),
                    value_expression,
                    source_file,
                );
            }
            _ => {}
        }

        let (validated_value, errors) =
            validate_json_option_value(opt, value, value_expression, source_file);
        if !errors.is_empty() || validated_value.is_null() {
            (validated_value, errors)
        } else {
            (
                normalize_non_list_option_value(opt, base_path, validated_value),
                errors,
            )
        }
    } else {
        (
            Value::Null,
            vec![
                create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                    source_file,
                    value_expression,
                    &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                    &[
                        Value::Str(opt.name.into()),
                        Value::Str(get_compiler_option_value_type_string(opt)),
                    ],
                ),
            ],
        )
    }
}

/// `convertJsonOptionOfEnumType`.
pub(crate) fn convert_json_option_of_enum_type(
    opt: CommandLineOptionRef,
    value: &str,
    value_expression: Option<NodeId>,
    source_file: Option<SourceFileCtx<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    if value.is_empty() {
        return (Value::Null, Vec::new());
    }
    let key = value.to_lowercase();
    let Some(type_map) = opt.enum_map() else {
        return (Value::Null, Vec::new());
    };
    if let Some(val) = type_map.get(&key) {
        return validate_json_option_value(opt, val, value_expression, source_file);
    }
    (
        Value::Null,
        vec![create_diagnostic_for_invalid_enum_type(
            opt,
            source_file,
            value_expression,
        )],
    )
}

/// `getExtendsConfigPathOrArray`.
fn get_extends_config_path_or_array(
    value: &Value,
    fs: &Arc<dyn Vfs>,
    base_path: &RootedDirectoryPath,
    config_file_name: &RootedFilePath,
    property_assignment: Option<NodeId>,
    value_expression: Option<NodeId>,
    source_file: Option<SourceFileCtx<'_>>,
) -> (Vec<RootedFilePath>, Vec<DiagnosticRef>) {
    let mut extended_config_path_array = Vec::new();
    let new_base = if !config_file_name.as_string().is_empty() {
        config_file_name.directory()
    } else {
        base_path.clone()
    };
    if value.is_null() {
        let (_, errors) = convert_json_option(
            declarations::extends_option_declaration(),
            value,
            base_path,
            property_assignment,
            value_expression,
            source_file,
        );
        return (extended_config_path_array, errors);
    }
    if let Some(s) = value.as_str() {
        let (val, errors) =
            get_extends_config_path(s, fs, &new_base, value_expression, source_file);
        if !val.as_string().is_empty() {
            extended_config_path_array.push(val);
        }
        return (extended_config_path_array, errors);
    }
    let mut errors = Vec::new();
    if let Some(list) = value.as_list() {
        for (index, file_name) in list.iter().enumerate() {
            let expression = value_expression.and_then(|value_expression| {
                source_file
                    .map(|sf| sf.node(value_expression))
                    .filter(|n| n.kind == Kind::ArrayLiteralExpression)
                    .and_then(|n| {
                        n.as_array_literal_expression()
                            .elements
                            .as_ref()
                            .and_then(|l| l.nodes.get(index))
                            .copied()
                    })
            });
            if let Some(file_name_str) = file_name.as_str() {
                let (val, err) =
                    get_extends_config_path(file_name_str, fs, &new_base, expression, source_file);
                if !val.as_string().is_empty() {
                    extended_config_path_array.push(val);
                }
                errors.extend(err);
            } else {
                let (_, err) = convert_json_option(
                    declarations::extends_option_declaration()
                        .elements()
                        .expect("extends has elements"),
                    value,
                    base_path,
                    property_assignment,
                    expression,
                    source_file,
                );
                errors.extend(err);
            }
        }
    } else {
        let (_, errs) = convert_json_option(
            declarations::extends_option_declaration(),
            value,
            base_path,
            property_assignment,
            value_expression,
            source_file,
        );
        errors = errs;
    }
    (extended_config_path_array, errors)
}

/// `getExtendsConfigPath`.
fn get_extends_config_path(
    extended_config: &str,
    fs: &Arc<dyn Vfs>,
    base_path: &RootedDirectoryPath,
    value_expression: Option<NodeId>,
    source_file: Option<SourceFileCtx<'_>>,
) -> (RootedFilePath, Vec<DiagnosticRef>) {
    let extended_config = tspath::normalize_slashes(extended_config).into_owned();
    let mut errors = Vec::new();
    if tspath::is_rooted_disk_path(&extended_config)
        || extended_config.starts_with("./")
        || extended_config.starts_with("../")
    {
        let mut extended_config_path = tspath::to_rooted_file_path(&extended_config, base_path);
        if !fs.file_exists(&extended_config_path)
            && !extended_config_path.extension_is(tspath::EXTENSION_JSON)
        {
            extended_config_path = extended_config_path.append_suffix(tspath::EXTENSION_JSON);
            if !fs.file_exists(&extended_config_path) {
                errors.push(
                    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                        source_file,
                        value_expression,
                        &diagnostics::File_0_not_found,
                        &[Value::Str(extended_config.clone())],
                    ),
                );
                return (RootedFilePath::default(), errors);
            }
        }
        return (extended_config_path, errors);
    }
    // If the path isn't a rooted or relative path, resolve like a module
    let resolved = module::resolve_config(
        &extended_config,
        &base_path.resolve_file("tsconfig.json"),
        fs.clone(),
    );
    if resolved.is_resolved() {
        return (resolved.resolved_file_name, errors);
    }
    if extended_config.is_empty() {
        errors.push(
            create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                source_file,
                value_expression,
                &diagnostics::Compiler_option_0_cannot_be_given_an_empty_string,
                &[Value::Str("extends".into())],
            ),
        );
    } else {
        errors.push(
            create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                source_file,
                value_expression,
                &diagnostics::File_0_not_found,
                &[Value::Str(extended_config)],
            ),
        );
    }
    (RootedFilePath::default(), errors)
}

// `tsConfigOptions` was dead code in Go (declared, never used); omitted.

/// `convertMapToOptions` — values have already been validated and converted.
pub(crate) fn convert_map_to_options<P: OptionParser>(
    compiler_options: &OrderedMap<String, Value>,
    result: &mut P,
) {
    for (key, value) in compiler_options.entries() {
        result.parse_option(key, value);
    }
}

/// `convertOptionsFromJson`.
pub(crate) fn convert_options_from_json<P: OptionParser>(
    options_name_map: &CommandLineOptionNameMap,
    json_options: &Value,
    base_path: &RootedDirectoryPath,
    result: &mut P,
) -> Vec<DiagnosticRef> {
    if json_options.is_null() {
        return Vec::new();
    }
    let Some(json_map) = json_options.as_map() else {
        // !!! probably should be an error
        return Vec::new();
    };
    let mut errors = Vec::new();
    for (key, value) in json_map.entries() {
        let opt = name_map_get(options_name_map, key);
        match opt {
            Some(opt) if opt.name != key => {
                // Case-insensitive match found but exact case doesn't match -
                // provide "did you mean" suggestion
                errors.push(
                    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                        None,
                        None,
                        result.unknown_did_you_mean_diagnostic(),
                        &[Value::Str(key.clone()), Value::Str(opt.name.into())],
                    ),
                );
                continue;
            }
            None => {
                errors.push(create_unknown_option_error(
                    key,
                    result.unknown_option_diagnostic(),
                    "",
                    None,
                    None,
                    None,
                    Some(result.unknown_did_you_mean_diagnostic()),
                    Some(options_name_map),
                ));
                continue;
            }
            _ => {}
        }
        let (convert_json, err) =
            convert_json_option(opt.unwrap(), value, base_path, None, None, None);
        errors.extend(err);
        result.parse_option(key, &convert_json);
    }
    errors
}

/// `convertArrayLiteralExpressionToJson`.
fn convert_array_literal_expression_to_json(
    source_file: SourceFileCtx<'_>,
    elements: &[NodeId],
    element_option: Option<CommandLineOptionRef>,
    return_value: bool,
) -> (Value, Vec<DiagnosticRef>) {
    if !return_value {
        for element in elements {
            // PORT: Go passes `nil` for the notifier; children of array
            // elements never notify.
            convert_property_value_to_json(
                source_file,
                *element,
                element_option,
                return_value,
                None,
            );
        }
        return (Value::Null, Vec::new());
    }
    // Filter out invalid values
    if elements.is_empty() {
        // Always return an empty array, even if elements is nil.
        return (Value::List(Vec::new()), Vec::new());
    }
    let mut errors = Vec::new();
    let mut value = Vec::new();
    for element in elements {
        let (converted_value, err) = convert_property_value_to_json(
            source_file,
            *element,
            element_option,
            return_value,
            None,
        );
        errors.extend(err);
        if !converted_value.is_null() {
            value.push(converted_value);
        }
    }
    (Value::List(value), errors)
}

/// `ParseConfigFileTextToJson`.
pub fn parse_config_file_text_to_json(
    file_name: RootedFilePath,
    path: PathKey,
    json_text: &str,
) -> (Value, Vec<DiagnosticRef>) {
    let (file, nodes) = parser::parse_source_file(
        SourceFileParseOptions {
            file_name,
            path_key: path,
            ..Default::default()
        },
        json_text,
        ScriptKind::Json,
    );
    let ctx = SourceFileCtx {
        file,
        nodes: &nodes,
    };
    let (config, mut errors) = convert_config_file_to_object(ctx, None);
    let parse_diagnostics = nodes[file].as_source_file().diagnostics();
    if !parse_diagnostics.is_empty() {
        errors = vec![parse_diagnostics[0].clone()];
    }
    (config, errors)
}

/// `ParseJsonSourceFileConfigFileContent`.
///
/// PORT: `sourceFile` is `Arc<TsConfigSourceFile>` — Go mutates the caller's
/// file (`ExtendedSourceFiles`, `configFileSpecs`) via interior `Mutex`
/// fields, so sharing matches Go pointer semantics.
pub fn parse_json_source_file_config_file_content(
    source_file: &Arc<TsConfigSourceFile>,
    fs: &Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
    existing_options: Option<&CompilerOptions>,
    existing_options_raw: Option<&OrderedMap<String, Value>>,
    resolution_stack: &[PathKey],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> ParsedCommandLine {
    parse_json_config_file_content_worker(
        None,
        Some(source_file),
        fs,
        base_path,
        existing_options,
        existing_options_raw,
        source_file.file_name().clone(),
        resolution_stack,
        extended_config_cache,
    )
}

/// `convertObjectLiteralExpressionToJson`.
fn convert_object_literal_expression_to_json(
    source_file: SourceFileCtx<'_>,
    return_value: bool,
    node: NodeId,
    object_option: Option<CommandLineOptionRef>,
    mut notifier: Option<&mut JsonConversionNotifier<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    let mut result = OrderedMap::new();
    let mut errors = Vec::new();
    let object_literal = source_file.node(node).as_object_literal_expression();
    let diagnostic_file =
        tsc_ast::diagnostic::DiagnosticFile::from_node(source_file.file, source_file.nodes);
    for element in object_literal
        .properties
        .as_ref()
        .map(|l| l.nodes.iter().copied())
        .into_iter()
        .flatten()
    {
        let element_node = source_file.node(element);
        if element_node.kind != Kind::PropertyAssignment {
            errors.push(new_diagnostic(
                Some(diagnostic_file.clone()),
                element_node.loc,
                &diagnostics::Property_assignment_expected,
                &Vec::<Value>::new(),
            ));
            continue;
        }

        let property_assignment = element_node.as_property_assignment();
        if let Some(token) = element_node.question_token(source_file.nodes) {
            errors.push(new_diagnostic(
                Some(diagnostic_file.clone()),
                source_file.node(token).loc,
                &diagnostics::The_0_modifier_can_only_be_used_in_TypeScript_files,
                &[Value::Str("?".into())],
            ));
        }
        let mut text_of_key = String::new();
        // PORT: `Name()` nil maps to `None` — `isComputedNonLiteralName(nil)`
        // is false and `tryGetTextOfPropertyName(nil)` yields no text.
        if !property_assignment
            .named_member_base
            .name
            .is_some_and(|name| {
                is_computed_non_literal_name(source_file.node(name), source_file.nodes)
            })
        {
            if let Some(name) = property_assignment.named_member_base.name {
                let (text, _ok) = try_get_text_of_property_name(name, source_file.nodes);
                text_of_key = text.unwrap_or_default();
            }
        }
        let key_text = text_of_key;
        let mut option: Option<CommandLineOptionRef> = None;
        if !key_text.is_empty() {
            if let Some(element_options) = object_option.and_then(|o| o.element_options_map()) {
                option = name_map_get(element_options, &key_text);
                if option.is_some_and(|o| o.name != key_text) {
                    option = None;
                }
            }
        }
        let (value, err) = convert_property_value_to_json(
            source_file,
            // PORT: Go passes `Initializer` (nilable) straight into
            // `valueExpression.Kind` which would panic on nil; JSON-parsed
            // property assignments always have an initializer.
            property_assignment.initializer.expect("initializer"),
            option,
            return_value,
            notifier.as_mut().map(|n| &mut **n),
        );
        errors.extend(err);
        if !key_text.is_empty() {
            if return_value {
                result.set(key_text.clone(), value.clone());
            }
            // Notify key value set, if user asked for it
            if let Some(notifier) = notifier.as_mut() {
                let (_, err) = notifier.on_property_set.on_property_set(
                    &key_text,
                    &value,
                    element,
                    object_option,
                    option,
                );
                errors.extend(err);
            }
        }
    }
    (Value::Map(result), errors)
}

/// `convertConfigFileToObject`.
fn convert_config_file_to_object(
    source_file: SourceFileCtx<'_>,
    json_conversion_notifier: Option<&mut JsonConversionNotifier<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    let json_conversion_notifier = json_conversion_notifier;
    let mut root_expression = None;
    if let Some(statements) = source_file
        .node(source_file.file)
        .as_source_file()
        .statements
        .as_ref()
    {
        if !statements.nodes.is_empty() {
            root_expression = source_file.node(statements.nodes[0]).expression();
        }
    }
    if let Some(expression) = root_expression {
        let expression_node = source_file.node(expression);
        if expression_node.kind != Kind::ObjectLiteralExpression {
            let mut base_file_name = "tsconfig.json";
            if source_file
                .node(source_file.file)
                .as_source_file()
                .file_name()
                .base_name()
                == "jsconfig.json"
            {
                base_file_name = "jsconfig.json";
            }
            let errors = vec![create_diagnostic_for_node_in_source_file(
                source_file,
                expression,
                &diagnostics::The_root_value_of_a_0_file_must_be_an_object,
                &[Value::Str(base_file_name.into())],
            )];
            // Last-ditch error recovery. Somewhat useful because the JSON parser will recover from some parse errors by
            // synthesizing a top-level array literal expression. There's a reasonable chance the first element of that
            // array is a well-formed configuration object, made into an array element by stray characters.
            if expression_node.kind == Kind::ArrayLiteralExpression {
                let elements = expression_node
                    .as_array_literal_expression()
                    .elements
                    .as_ref()
                    .map(|l| &l.nodes[..])
                    .unwrap_or(&[]);
                if let Some(first_object) = elements
                    .iter()
                    .copied()
                    .find(|e| source_file.node(*e).kind == Kind::ObjectLiteralExpression)
                {
                    return convert_to_json(
                        source_file,
                        Some(first_object),
                        true,
                        json_conversion_notifier,
                    );
                }
            }
            return (Value::Map(OrderedMap::new()), errors);
        }
    }
    convert_to_json(source_file, root_expression, true, json_conversion_notifier)
}

/// `convertToJson` — returns the json value (apart from checking errors)
/// only if `return_value` is true.
fn convert_to_json(
    source_file: SourceFileCtx<'_>,
    root_expression: Option<NodeId>,
    return_value: bool,
    notifier: Option<&mut JsonConversionNotifier<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    let Some(root_expression) = root_expression else {
        if return_value {
            // `struct{}{}`
            return (Value::EmptyStruct, Vec::new());
        }
        return (Value::Null, Vec::new());
    };
    let root_options = notifier.as_ref().and_then(|n| n.root_options);
    convert_property_value_to_json(
        source_file,
        root_expression,
        root_options,
        return_value,
        notifier,
    )
}

/// `isDoubleQuotedString`.
fn is_double_quoted_string(node: &Node) -> bool {
    node.kind == Kind::StringLiteral
}

/// `convertPropertyValueToJson`.
fn convert_property_value_to_json(
    source_file: SourceFileCtx<'_>,
    value_expression: NodeId,
    option: Option<CommandLineOptionRef>,
    return_value: bool,
    notifier: Option<&mut JsonConversionNotifier<'_>>,
) -> (Value, Vec<DiagnosticRef>) {
    let node = source_file.node(value_expression);
    let diagnostic_file =
        || tsc_ast::diagnostic::DiagnosticFile::from_node(source_file.file, source_file.nodes);
    match node.kind {
        Kind::TrueKeyword => (Value::Bool(true), Vec::new()),
        Kind::FalseKeyword => (Value::Bool(false), Vec::new()),
        // todo: how to manage null
        Kind::NullKeyword => (Value::Null, Vec::new()),

        Kind::StringLiteral => {
            let text = node.text(source_file.nodes).into_owned();
            if !is_double_quoted_string(node) {
                return (
                    Value::Str(text),
                    vec![new_diagnostic(
                        Some(diagnostic_file()),
                        node.loc,
                        &diagnostics::String_literal_with_double_quotes_expected,
                        &Vec::<Value>::new(),
                    )],
                );
            }
            (Value::Str(text), Vec::new())
        }
        Kind::NumericLiteral => (
            Value::Float(tsc_jsnum::from_string(&node.text(source_file.nodes)).into()),
            Vec::new(),
        ),
        Kind::PrefixUnaryExpression => {
            let unary = node.as_prefix_unary_expression();
            let operand = source_file.node(unary.operand.expect("operand"));
            if unary.operator != Kind::MinusToken || operand.kind != Kind::NumericLiteral {
                // not valid JSON syntax
                return invalid_json_value(source_file, node, option);
            }
            (
                Value::Float(-f64::from(tsc_jsnum::from_string(
                    &operand.text(source_file.nodes),
                ))),
                Vec::new(),
            )
        }
        Kind::ObjectLiteralExpression => {
            // Currently having element option declaration in the tsconfig with
            // type "object" determines if it needs
            // onSetValidOptionKeyValueInParent callback or not. At moment there
            // are only "compilerOptions", "typeAcquisition" and "typingOptions"
            // that satisfies it and need it to modify options set in them (for
            // normalizing file paths) vs what we set in the json. If need
            // arises, we can modify this interface and callbacks as needed.
            convert_object_literal_expression_to_json(
                source_file,
                return_value,
                value_expression,
                option,
                notifier,
            )
        }
        Kind::ArrayLiteralExpression => convert_array_literal_expression_to_json(
            source_file,
            node.as_array_literal_expression()
                .elements
                .as_ref()
                .map(|l| &l.nodes[..])
                .unwrap_or(&[]),
            option,
            return_value,
        ),
        _ => invalid_json_value(source_file, node, option),
    }
}

/// The trailing "Not in expected format" arm of `convertPropertyValueToJson`.
fn invalid_json_value(
    source_file: SourceFileCtx<'_>,
    node: &Node,
    option: Option<CommandLineOptionRef>,
) -> (Value, Vec<DiagnosticRef>) {
    let (message, message_args): (&'static Message, Vec<Value>) = match option {
        Some(option) => (
            &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
            vec![
                Value::Str(option.name.into()),
                Value::Str(get_compiler_option_value_type_string(option)),
            ],
        ),
        None => (
            &diagnostics::Property_value_can_only_be_string_literal_numeric_literal_true_false_null_object_literal_or_array_literal,
            Vec::new(),
        ),
    };
    (
        Value::Null,
        vec![new_diagnostic(
            Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
                source_file.file,
                source_file.nodes,
            )),
            node.loc,
            message,
            &message_args,
        )],
    )
}

/// `ParseJsonConfigFileContent`.
pub fn parse_json_config_file_content(
    json: &Value,
    fs: &Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
    existing_options: Option<&CompilerOptions>,
    config_file_name: RootedFilePath,
    resolution_stack: &[PathKey],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> ParsedCommandLine {
    let normalized = normalize_json_value(json);
    let json_object = match normalized.as_map() {
        Some(_) => normalized,
        None => Value::empty_map(),
    };
    parse_json_config_file_content_worker(
        Some(&json_object),
        None,
        fs,
        base_path,
        existing_options,
        None,
        config_file_name,
        resolution_stack,
        extended_config_cache,
    )
}

/// `normalizeJsonValue`.
fn normalize_json_value(value: &Value) -> Value {
    match value {
        Value::Map(map) => {
            let mut result = OrderedMap::with_size_hint(map.size());
            for (key, child) in map.entries() {
                result.set(key.clone(), normalize_json_value(child));
            }
            Value::Map(result)
        }
        Value::List(list) => Value::List(list.iter().map(normalize_json_value).collect()),
        // Go `map[string]any` — converted to `*OrderedMap[string, any]` with
        // keys inserted in `slices.Sorted(maps.Keys(value))` order.
        Value::GoMap(map) => {
            let mut keys: Vec<&String> = map.keys().collect();
            keys.sort();
            let mut result = OrderedMap::with_size_hint(map.size());
            for key in keys {
                result.set(key.clone(), normalize_json_value(map.get(key).unwrap()));
            }
            Value::Map(result)
        }
        // Arbitrary reflect-visible slices — converted element-wise to `[]any`.
        // (Go returns `nil` for a nil slice; Rust cannot distinguish nil from
        // empty `Vec`, so an empty list becomes `[]any{}`.)
        Value::StringList(list) => {
            Value::List(list.iter().map(|s| Value::Str(s.clone())).collect())
        }
        Value::FilePathList(list) => {
            Value::List(list.iter().map(|s| Value::FilePath(s.clone())).collect())
        }
        Value::DirPathList(list) => {
            Value::List(list.iter().map(|s| Value::DirPath(s.clone())).collect())
        }
        // `[]core.PluginImport`: struct elements are not maps/slices, so Go
        // keeps them as-is in the `[]any` — `EmptyStruct` is the closest
        // non-nil non-map representation.
        Value::Plugins(list) => Value::List(list.iter().map(|_| Value::EmptyStruct).collect()),
        // `*OrderedMap[string, []string]` is a pointer type in Go, not a
        // `*OrderedMap[string, any]`, so it is returned unchanged.
        _ => value.clone(),
    }
}

/// `convertToObject`.
fn convert_to_object(source_file: SourceFileCtx<'_>) -> (Value, Vec<DiagnosticRef>) {
    let root_expression = root_expression(source_file);
    convert_to_json(source_file, root_expression, true, None)
}

/// `rootExpression` — `sourceFile.Statements.Nodes[0].Expression()`.
fn root_expression(source_file: SourceFileCtx<'_>) -> Option<NodeId> {
    let statements = source_file
        .node(source_file.file)
        .as_source_file()
        .statements
        .as_ref()?;
    let stmt = statements.nodes.first().copied()?;
    let stmt_node = source_file.node(stmt);
    match stmt_node.kind {
        Kind::ExpressionStatement => stmt_node.as_expression_statement().expression,
        _ => None,
    }
}

/// `convertCompilerOptionsFromJsonWorker`.
fn convert_compiler_options_from_json_worker(
    json_options: &Value,
    base_path: &RootedDirectoryPath,
    config_file_name: &RootedFilePath,
) -> (ParsedCompilerOptions, Vec<DiagnosticRef>) {
    let mut options = options::get_default_compiler_options(config_file_name.clone());
    {
        let mut parser_impl = parsinghelpers::CompilerOptionsParser {
            compiler_options: options
                .compiler_options
                .as_deref_mut()
                .expect("getDefaultCompilerOptions always produces CompilerOptions"),
            unresolved_paths: Some(&mut options.unresolved_paths),
        };
        let errors = convert_options_from_json(
            command_line_compiler_options_map(),
            json_options,
            base_path,
            &mut parser_impl,
        );
        if !config_file_name.as_string().is_empty() {
            options
                .compiler_options
                .as_deref_mut()
                .unwrap()
                .config_file_path = config_file_name.clone();
        }
        (options, errors)
    }
}

/// `convertTypeAcquisitionFromJsonWorker`.
fn convert_type_acquisition_from_json_worker(
    json_options: &Value,
    base_path: &RootedDirectoryPath,
    config_file_name: &RootedFilePath,
) -> (TypeAcquisition, Vec<DiagnosticRef>) {
    let mut type_acquisition = options::get_default_type_acquisition(config_file_name.clone());
    let mut parser_impl = parsinghelpers::TypeAcquisitionParser {
        type_acquisition: &mut type_acquisition,
    };
    let errors = convert_options_from_json(
        declarations::type_acquisition_declaration()
            .element_options_map()
            .expect("typeAcquisitionDeclaration has ElementOptions"),
        json_options,
        base_path,
        &mut parser_impl,
    );
    (type_acquisition, errors)
}

/// `parseOwnConfigOfJson`.
fn parse_own_config_of_json(
    json: &OrderedMap<String, Value>,
    fs: &Arc<dyn Vfs>,
    base_path: &RootedDirectoryPath,
    config_file_name: &RootedFilePath,
) -> (ParsedTsconfig, Vec<DiagnosticRef>) {
    let mut errors = Vec::new();
    if json.get("excludes").is_some() {
        errors.push(new_compiler_diagnostic(
            &diagnostics::Unknown_option_excludes_Did_you_mean_exclude,
            &Vec::<Value>::new(),
        ));
    }
    let (options, err) = convert_compiler_options_from_json_worker(
        json.get("compilerOptions")
            .cloned()
            .as_ref()
            .unwrap_or(&Value::Null),
        base_path,
        config_file_name,
    );
    let (type_acquisition, err2) = convert_type_acquisition_from_json_worker(
        json.get("typeAcquisition")
            .cloned()
            .as_ref()
            .unwrap_or(&Value::Null),
        base_path,
        config_file_name,
    );
    errors.extend(err);
    errors.extend(err2);
    // PORT: Go mutates `json` in place (`json.Set("compileOnSave", ...)`);
    // `raw` is captured into the result after mutation, so cloning here is
    // unobservable to callers.
    let mut json = json.clone();
    if let Some(compile_on_save) = json.get("compileOnSave").cloned() {
        let (converted, compile_on_save_errors) = convert_json_option(
            declarations::compile_on_save_command_line_option(),
            &compile_on_save,
            base_path,
            None,
            None,
            None,
        );
        errors.extend(compile_on_save_errors);
        json.set("compileOnSave".to_string(), converted);
    }
    let mut extended_config_paths = Vec::new();
    let extends = json.get("extends").cloned().unwrap_or(Value::Null);
    if !extends.is_null() && extends != Value::Str(String::new()) {
        let (paths, err) = get_extends_config_path_or_array(
            &extends,
            fs,
            base_path,
            config_file_name,
            None,
            None,
            None,
        );
        extended_config_paths = paths;
        errors.extend(err);
    }
    let parsed_config = ParsedTsconfig {
        raw: Some(Value::Map(json)),
        options: Some(options),
        type_acquisition: Some(Box::new(type_acquisition)),
        extended_config_paths,
    };
    (parsed_config, errors)
}

/// `parseOwnConfigOfJsonSourceFile`.
fn parse_own_config_of_json_source_file(
    source_file: SourceFileCtx<'_>,
    fs: &Arc<dyn Vfs>,
    base_path: &RootedDirectoryPath,
    config_file_name: &RootedFilePath,
) -> (ParsedTsconfig, Vec<DiagnosticRef>) {
    let mut state = OwnConfigState {
        compiler_options: options::get_default_compiler_options(config_file_name.clone()),
        type_acquisition: options::get_default_type_acquisition(config_file_name.clone()),
        extended_config_paths: Vec::new(),
        root_compiler_options: Vec::new(),
        errors: Vec::new(),
        fs: fs.clone(),
        base_path: base_path.clone(),
        config_file_name: config_file_name.clone(),
        source_file,
    };

    let (json, err) = {
        let mut notifier = JsonConversionNotifier {
            root_options: Some(declarations::tsconfig_root_options_map()),
            on_property_set: &mut state,
        };
        convert_config_file_to_object(source_file, Some(&mut notifier))
    };
    state.errors.extend(err);
    if !state.root_compiler_options.is_empty() {
        if let Some(json_object) = json.as_map() {
            if json_object.get("compilerOptions").is_none() {
                let first = state.root_compiler_options[0];
                state.errors.push(create_diagnostic_for_node_in_source_file(
                    source_file,
                    first,
                    &diagnostics::X_0_should_be_set_inside_the_compilerOptions_object_of_the_config_json_file,
                    &[Value::Str(get_text_of_property_name(
                        first,
                        source_file.nodes,
                    ))],
                ));
            }
        }
    }
    (
        ParsedTsconfig {
            raw: Some(json),
            options: Some(state.compiler_options),
            type_acquisition: Some(Box::new(state.type_acquisition)),
            extended_config_paths: state.extended_config_paths,
        },
        state.errors,
    )
}

/// Mutable state standing in for the Go `onPropertySet` closure captures.
struct OwnConfigState<'a> {
    compiler_options: ParsedCompilerOptions,
    type_acquisition: TypeAcquisition,
    extended_config_paths: Vec<RootedFilePath>,
    root_compiler_options: Vec<NodeId>,
    errors: Vec<DiagnosticRef>,
    fs: Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
    config_file_name: RootedFilePath,
    source_file: SourceFileCtx<'a>,
}

impl<'a> OnPropertySet for OwnConfigState<'a> {
    /// `onPropertySet` from `parseOwnConfigOfJsonSourceFile`.
    fn on_property_set(
        &mut self,
        key_text: &str,
        value: &Value,
        property_assignment: NodeId,
        parent_option: Option<CommandLineOptionRef>,
        option: Option<CommandLineOptionRef>,
    ) -> (Value, Vec<DiagnosticRef>) {
        // Ensure value is verified except for extends which is handled in its
        // own way for error reporting
        let mut property_set_errors: Vec<DiagnosticRef> = Vec::new();
        let mut value = value.clone();
        let initializer = self
            .source_file
            .node(property_assignment)
            .as_property_assignment()
            .initializer;
        if let Some(option) = option {
            if !std::ptr::eq(option, declarations::extends_option_declaration()) {
                let (v, errs) = convert_json_option(
                    option,
                    &value,
                    &self.base_path,
                    Some(property_assignment),
                    initializer,
                    Some(self.source_file),
                );
                value = v;
                property_set_errors.extend(errs);
            }
        }
        if parent_option.is_some_and(|p| p.name != "undefined") && !value.is_null() {
            if let Some(option) = option {
                if !option.name.is_empty() {
                    match parent_option.unwrap().name {
                        "compilerOptions" => {
                            self.compiler_options.parse_option(option.name, &value);
                        }
                        "typeAcquisition" => {
                            options::parse_type_acquisition(
                                option.name,
                                &value,
                                &mut self.type_acquisition,
                            );
                        }
                        _ => {}
                    }
                }
            } else if !key_text.is_empty() {
                let parent_option = parent_option.unwrap();
                if extra_key_diagnostics(parent_option.name).is_some() {
                    let unknown_name_diag = extra_key_diagnostics(parent_option.name).unwrap();
                    if let Some(element_options) = parent_option.element_options_map() {
                        let possible_option =
                            name_map_get(element_options, key_text).or_else(|| {
                                name_map_get_spelling_suggestion(element_options, key_text)
                            });
                        match possible_option {
                            Some(possible_option) if possible_option.name != key_text => {
                                property_set_errors.push(
                                    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                                        Some(self.source_file),
                                        self.source_file
                                            .node(property_assignment)
                                            .as_property_assignment()
                                            .named_member_base
                                            .name,
                                        extra_key_did_you_mean_diagnostics(
                                            parent_option.name,
                                        )
                                        .unwrap(),
                                        &[
                                            Value::Str(key_text.into()),
                                            Value::Str(possible_option.name.into()),
                                        ],
                                    ),
                                );
                            }
                            _ => {
                                property_set_errors.push(create_unknown_option_error(
                                    key_text,
                                    unknown_name_diag,
                                    "",
                                    self.source_file
                                        .node(property_assignment)
                                        .as_property_assignment()
                                        .named_member_base
                                        .name,
                                    Some(self.source_file),
                                    None,
                                    None,
                                    None,
                                ));
                            }
                        }
                    }
                }
            }
        } else if parent_option
            .is_some_and(|p| std::ptr::eq(p, declarations::tsconfig_root_options_map()))
        {
            if option.is_some_and(|o| std::ptr::eq(o, declarations::extends_option_declaration())) {
                let (config_path, err) = get_extends_config_path_or_array(
                    &value,
                    &self.fs,
                    &self.base_path,
                    &self.config_file_name,
                    Some(property_assignment),
                    initializer,
                    Some(self.source_file),
                );
                self.extended_config_paths = config_path;
                property_set_errors.extend(err);
            } else if option.is_none() {
                if key_text == "excludes" {
                    if let Some(name) = self
                        .source_file
                        .node(property_assignment)
                        .as_property_assignment()
                        .named_member_base
                        .name
                    {
                        property_set_errors.push(create_diagnostic_for_node_in_source_file(
                            self.source_file,
                            name,
                            &diagnostics::Unknown_option_excludes_Did_you_mean_exclude,
                            &Vec::<Value>::new(),
                        ));
                    }
                }
                if declarations::OPTIONS_DECLARATIONS
                    .iter()
                    .copied()
                    .any(|o| o.name == key_text)
                {
                    // PORT: Go pushes `Name()` which may be nil; names are
                    // always present on parsed JSON property assignments.
                    if let Some(name) = self
                        .source_file
                        .node(property_assignment)
                        .as_property_assignment()
                        .named_member_base
                        .name
                    {
                        self.root_compiler_options.push(name);
                    }
                }
            }
        }
        (value, property_set_errors)
    }
}

// ---------------------------------------------------------------------------
// readJsonConfigFile / getExtendedConfig / ParseExtendedConfig / parseConfig
// ---------------------------------------------------------------------------

/// `tryReadFile` (declared in commandlineparser.go in Go; hoisted here
/// because `readJsonConfigFile` uses it too).
pub(crate) fn try_read_file(
    file_name: &RootedFilePath,
    read_file: impl FnOnce(&RootedFilePath) -> Option<String>,
    mut errors: Vec<DiagnosticRef>,
) -> (String, Vec<DiagnosticRef>) {
    let text = read_file(file_name);
    let Some(text) = text else {
        // !!! Divergence: the returned error will not give a useful message
        errors.push(new_compiler_diagnostic(
            &diagnostics::Cannot_read_file_0,
            &[Value::Str(file_name.as_string().into())],
        ));
        return (String::new(), errors);
    };
    (text, errors)
}

/// `readJsonConfigFile`.
fn read_json_config_file(
    file_name: &RootedFilePath,
    path: &PathKey,
    fs: &Arc<dyn Vfs>,
) -> (TsConfigSourceFile, Vec<DiagnosticRef>) {
    let (text, diagnostic) = try_read_file(file_name, |f| fs.read_file(f), Vec::new());
    if !text.is_empty() {
        let (file, nodes) = parser::parse_source_file(
            SourceFileParseOptions {
                file_name: file_name.clone(),
                path_key: path.clone(),
                ..Default::default()
            },
            &text,
            ScriptKind::Json,
        );
        (
            TsConfigSourceFile {
                source_file: file,
                nodes,
                extended_source_files: Mutex::new(Vec::new()),
                config_file_specs: Mutex::new(None),
            },
            diagnostic,
        )
    } else {
        let mut factory = NodeFactory::default();
        let mut nodes = Vec::new();
        let eof = factory.new_token(&mut nodes, Kind::EndOfFile);
        let statements = factory.new_node_list(Vec::new());
        let file = factory.new_source_file(
            &mut nodes,
            &SourceFileParseOptions {
                file_name: file_name.clone(),
                path_key: path.clone(),
                ..Default::default()
            },
            "",
            Some(statements),
            Some(eof),
        );
        nodes[file]
            .as_source_file_mut()
            .set_diagnostics(diagnostic.clone());
        (
            TsConfigSourceFile {
                source_file: file,
                nodes,
                extended_source_files: Mutex::new(Vec::new()),
                config_file_specs: Mutex::new(None),
            },
            diagnostic,
        )
    }
}

/// `getExtendedConfig`.
///
/// PORT: Go's `result` parameter (`*extendsResult`) collects
/// `extendedSourceFiles`; passed by reference here.
fn get_extended_config(
    source_file: Option<&TsConfigSourceFile>,
    extended_config_file_name: &RootedFilePath,
    fs: &Arc<dyn Vfs>,
    resolution_stack: &[PathKey],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
    result: &mut ExtendsResult,
) -> (Option<Arc<ParsedTsconfig>>, Vec<DiagnosticRef>) {
    let mut errors = Vec::new();
    let extended_config_path = fs
        .case_sensitivity()
        .path_key(&extended_config_file_name.as_path());

    let cache_entry =
        // Bypass the cache when we detect a cycle in the resolution stack.
        // The cache locks entries during parsing, and a cycle would cause the
        // same goroutine to re-lock the same entry, resulting in a deadlock.
        // Let parseConfig handle the circularity error via its own resolution
        // stack check.
        if let Some(cache) = extended_config_cache
            && !resolution_stack.contains(&extended_config_path)
        {
            cache.get_extended_config(
                extended_config_file_name,
                &extended_config_path,
                resolution_stack,
                fs,
            )
            .unwrap_or_else(|| {
                parse_extended_config(
                    extended_config_file_name,
                    &extended_config_path,
                    resolution_stack,
                    fs,
                    extended_config_cache,
                )
            })
        } else {
            parse_extended_config(
                extended_config_file_name,
                &extended_config_path,
                resolution_stack,
                fs,
                extended_config_cache,
            )
        };

    errors.extend(cache_entry.errors.iter().cloned());

    if let Some(extended_result) = &cache_entry.extended_result {
        if source_file.is_some() {
            result
                .extended_source_files
                .add(extended_result.file_name().clone());
            for extended_source_file in extended_result.extended_source_files() {
                result.extended_source_files.add(extended_source_file);
            }
        }
    }
    (cache_entry.extended_config.clone(), errors)
}

/// `ParseExtendedConfig`.
pub fn parse_extended_config(
    file_name: &RootedFilePath,
    path: &PathKey,
    resolution_stack: &[PathKey],
    fs: &Arc<dyn Vfs>,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> ExtendedConfigCacheEntry {
    let (extended_result, read_errors) = read_json_config_file(file_name, path, fs);
    let extended_result = Arc::new(extended_result);
    let mut entry = ExtendedConfigCacheEntry {
        extended_result: Some(extended_result.clone()),
        ..Default::default()
    };

    if !read_errors.is_empty() {
        entry.errors = read_errors;
        return entry;
    }

    let parse_diagnostics = extended_result.diagnostics().to_vec();
    if !parse_diagnostics.is_empty() {
        entry.errors = parse_diagnostics;
        return entry;
    }

    let (extended_config, parse_errors) = parse_config(
        None,
        Some(&extended_result),
        fs,
        file_name.directory(),
        file_name.clone(),
        resolution_stack.to_vec(),
        extended_config_cache,
    );
    entry.errors = parse_errors;
    entry.extended_config = Some(Arc::new(extended_config));
    entry
}

/// `parseConfig` — just extracts options/include/exclude/files out of a
/// config file. It does not resolve the included files.
#[allow(clippy::too_many_arguments)]
fn parse_config(
    json: Option<&Value>,
    source_file: Option<&TsConfigSourceFile>,
    fs: &Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
    config_file_name: RootedFilePath,
    mut resolution_stack: Vec<PathKey>,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> (ParsedTsconfig, Vec<DiagnosticRef>) {
    let case_sensitivity = fs.case_sensitivity();
    let mut resolved_path = case_sensitivity.path_key(&base_path.as_path());
    if !config_file_name.as_string().is_empty() {
        resolved_path = case_sensitivity.path_key(&config_file_name.as_path());
    }
    let mut errors = Vec::new();
    if resolution_stack.contains(&resolved_path) {
        errors.push(new_compiler_diagnostic(
            &diagnostics::Circularity_detected_while_resolving_configuration_Colon_0,
            &Vec::<Value>::new(),
        ));
        let json_val = json.cloned();
        if json_val
            .as_ref()
            .and_then(|j| j.as_map())
            .is_none_or(|m| m.size() == 0)
        {
            // Go stores `raw: json` — nil `any` when no JSON was supplied.
            return (
                ParsedTsconfig {
                    raw: json_val,
                    ..Default::default()
                },
                errors,
            );
        }
        let (raw_result, err) =
            convert_to_object(source_file.expect("sourceFile present").as_ctx());
        errors.extend(err);
        return (
            ParsedTsconfig {
                raw: Some(raw_result),
                ..Default::default()
            },
            errors,
        );
    }

    #[allow(unused_assignments)] // PORT: Go initializes `ownConfig` unconditionally
    let mut own_config = ParsedTsconfig::default();
    let err;
    if let Some(json) = json {
        // PORT: Go asserts `json` is `*OrderedMap`; anything else is treated
        // as an empty map (the `nil` case is a `None` json).
        let empty_map = OrderedMap::new();
        let json_map = json.as_map().unwrap_or(&empty_map);
        let (config, e) = parse_own_config_of_json(json_map, fs, &base_path, &config_file_name);
        own_config = config;
        err = e;
    } else {
        let (config, e) = parse_own_config_of_json_source_file(
            source_file.expect("json or sourceFile required").as_ctx(),
            fs,
            &base_path,
            &config_file_name,
        );
        own_config = config;
        err = e;
    }
    errors.extend(err);
    if let Some(own_options) = own_config.options.as_mut() {
        if let Some(compiler_options) = own_options.compiler_options.as_mut() {
            if compiler_options.paths.is_some() {
                // If we end up needing to resolve relative paths from 'paths'
                // relative to the config file location, we'll need to know
                // where that config file was. Since 'paths' can be inherited
                // from an extended config in another directory, we wouldn't
                // know which directory to use unless we store it here.
                compiler_options.paths_base_path = base_path.clone();
            }
        }
    }

    if !own_config.extended_config_paths.is_empty() {
        // copy the resolution stack so it is never reused between branches in
        // potential diamond-problem scenarios.
        resolution_stack.push(resolved_path);
        let mut result = ExtendsResult {
            options: Some(ParsedCompilerOptions {
                compiler_options: Some(Box::new(CompilerOptions::default())),
                unresolved_paths: UnresolvedCompilerOptionPaths::new(),
            }),
            ..Default::default()
        };
        for extended_config_path in own_config.extended_config_paths.clone() {
            apply_extended_config(
                &mut result,
                source_file,
                &extended_config_path,
                fs,
                &resolution_stack,
                extended_config_cache,
                &mut errors,
                &base_path,
                case_sensitivity,
                &own_config.raw,
            );
        }
        let raw_map = own_config.raw.as_mut().and_then(|r| r.as_map_mut());
        if let Some(raw_map) = raw_map {
            if let Some(include) = result.include.take() {
                raw_map.set("include".to_string(), Value::List(include));
            }
            if let Some(exclude) = result.exclude.take() {
                raw_map.set("exclude".to_string(), Value::List(exclude));
            }
            if let Some(files) = result.files.take() {
                raw_map.set("files".to_string(), Value::List(files));
            }
            if let Some(content_mappers) = result.content_mappers.take() {
                if !raw_map.has("contentMappers") {
                    raw_map.set("contentMappers".to_string(), Value::List(content_mappers));
                }
            }
            if result.compile_on_save && !raw_map.has("compileOnSave") {
                raw_map.set(
                    "compileOnSave".to_string(),
                    Value::Bool(result.compile_on_save),
                );
            }
        } else {
            // PORT: Go would panic on a non-map `ownConfig.raw`; unreachable
            // for JSON input (raw is always a map or empty struct), so a
            // no-op keeps empty configs from crashing.
            debug_assert!(
                matches!(own_config.raw, Some(Value::EmptyStruct) | None),
                "expected empty raw config"
            );
        }
        if let Some(source_file) = source_file {
            let mut guard = source_file
                .extended_source_files
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            for extended_source_file in result.extended_source_files.keys() {
                *guard = core::insert_sorted(
                    &guard,
                    extended_source_file.clone(),
                    |a: &RootedFilePath, b: &RootedFilePath| a.compare(b),
                );
            }
        }
        let own_raw = own_config.raw.clone().unwrap_or(Value::Null);
        own_config.options =
            merge_parsed_compiler_options(result.options, own_config.options.as_ref(), &own_raw);
    }
    (own_config, errors)
}

/// The `applyExtendedConfig` closure in `parseConfig`.
#[allow(clippy::too_many_arguments)]
fn apply_extended_config(
    result: &mut ExtendsResult,
    source_file: Option<&TsConfigSourceFile>,
    extended_config_path: &RootedFilePath,
    fs: &Arc<dyn Vfs>,
    resolution_stack: &[PathKey],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
    errors: &mut Vec<DiagnosticRef>,
    base_path: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    own_raw: &Option<Value>,
) {
    let (extended_config, extended_errors) = get_extended_config(
        source_file,
        extended_config_path,
        fs,
        resolution_stack,
        extended_config_cache,
        result,
    );
    errors.extend(extended_errors);
    let Some(extended_config) = extended_config else {
        return;
    };
    let Some(extended_options) = extended_config.options.as_ref() else {
        return;
    };
    let extends_raw = extended_config.raw.clone();
    let mut relative_difference = String::new();
    // `setPropertyValue` closure
    let mut set_property_value = |property_name: &str, result: &mut ExtendsResult| {
        if let Some(raw_map) = own_raw.as_ref().and_then(|r| r.as_map()) {
            if raw_map.has(property_name) {
                return;
            }
        }
        if !matches!(property_name, "include" | "exclude" | "files") {
            return;
        }
        let Some(extends_map) = extends_raw.as_ref().and_then(|r| r.as_map()) else {
            return;
        };
        if !extends_map.has(property_name) {
            return;
        }
        let slice = extends_map.get(property_name).and_then(|v| v.as_list());
        let Some(slice) = slice else {
            return;
        };
        let value: Vec<Value> = slice
            .iter()
            .map(|path| {
                let Some(path_str) = path.as_str() else {
                    return path.clone();
                };
                if starts_with_config_dir_template(path_str)
                    || tspath::is_rooted_disk_path(path_str)
                {
                    Value::Str(path_str.to_string())
                } else {
                    if relative_difference.is_empty() {
                        relative_difference = tspath::convert_to_relative_path(
                            extended_config_path.directory().as_string(),
                            base_path,
                            case_sensitivity,
                        );
                    }
                    Value::Str(tspath::combine_paths(&relative_difference, &[path_str]))
                }
            })
            .collect();
        match property_name {
            "include" => result.include = Some(value),
            "exclude" => result.exclude = Some(value),
            "files" => result.files = Some(value),
            _ => {}
        }
    };

    set_property_value("include", result);
    set_property_value("exclude", result);
    set_property_value("files", result);
    if let Some(extended_raw_map) = extends_raw.as_ref().and_then(|r| r.as_map()) {
        if extended_raw_map.has("contentMappers") {
            result.content_mappers = extended_raw_map
                .get("contentMappers")
                .and_then(|v| v.as_list())
                .cloned();
        }
        if extended_raw_map.has("compileOnSave") {
            if let Some(compile_on_save) = extended_raw_map
                .get("compileOnSave")
                .and_then(|v| v.as_bool())
            {
                result.compile_on_save = compile_on_save;
            }
        }
    }
    // `mergeParsedCompilerOptions(result.options, extendedConfig.options, extendsRaw)`
    // — Go ignores the return because `result.options` is already non-nil.
    let null = Value::Null;
    result.options = merge_parsed_compiler_options(
        result.options.take(),
        Some(extended_options),
        extends_raw.as_ref().unwrap_or(&null),
    );
}

pub(crate) const DEFAULT_INCLUDE_SPEC: &str = "**/*";

/// `propOfRaw`.
struct PropOfRaw {
    slice_value: Option<Vec<Value>>,
    /// `""`, `"no-prop"`, or `"not-array"` — the Go zero value is "".
    wrong_value: &'static str,
}

fn is_string_value(value: &Value) -> bool {
    value.as_str().is_some()
}

/// `parseJsonConfigFileContentWorker`.
#[allow(clippy::too_many_arguments)]
fn parse_json_config_file_content_worker(
    json: Option<&Value>,
    source_file: Option<&Arc<TsConfigSourceFile>>,
    fs: &Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
    existing_options: Option<&CompilerOptions>,
    existing_options_raw: Option<&OrderedMap<String, Value>>,
    config_file_name: RootedFilePath,
    resolution_stack: &[PathKey],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> ParsedCommandLine {
    debug_assert!(
        (json.is_none() && source_file.is_some()) || (json.is_some() && source_file.is_none())
    );

    let base_directory = base_path.clone();
    let base_path_for_file_names = if !config_file_name.as_string().is_empty() {
        config_file_name.directory()
    } else {
        base_directory.clone()
    };

    let mut errors = Vec::new();
    let (mut parsed_config, errs) = parse_config(
        json,
        source_file.map(|s| s.as_ref()),
        fs,
        base_directory,
        config_file_name.clone(),
        resolution_stack.to_vec(),
        extended_config_cache,
    );
    errors.extend(errs);
    // Go passes `&parsedCompilerOptions{CompilerOptions: existingOptions}` —
    // always non-nil even when `existingOptions` is nil, so
    // `parsedConfig.options` is guaranteed non-nil afterwards.
    let existing_parsed = ParsedCompilerOptions {
        compiler_options: existing_options.map(|o| Box::new(o.clone())),
        unresolved_paths: UnresolvedCompilerOptionPaths::new(),
    };
    let existing_raw = existing_options_raw
        .map(|m| Value::Map(m.clone()))
        .unwrap_or(Value::Null);
    parsed_config.options = merge_parsed_compiler_options(
        parsed_config.options.take(),
        Some(&existing_parsed),
        &existing_raw,
    );
    if let Some(parsed_options) = parsed_config.options.as_mut() {
        options::handle_option_config_dir_template_substitution(
            Some(parsed_options),
            base_path_for_file_names.clone(),
        );
    }
    let empty = Value::Null;
    let raw_config = parse_json_to_string_key(parsed_config.raw.as_ref().unwrap_or(&empty));
    if !config_file_name.as_string().is_empty() {
        if let Some(options) = parsed_config.options.as_mut() {
            options
                .compiler_options
                .as_deref_mut()
                .expect("options")
                .config_file_path = config_file_name.clone();
        }
    }

    // `getPropFromRaw`
    macro_rules! get_prop_from_raw {
        ($prop:expr, $validate:expr, $element_type_name:expr) => {{
            let prop: &str = $prop;
            let validate_element: &dyn Fn(&Value) -> bool = $validate;
            let element_type_name: &str = $element_type_name;
            let mut result = PropOfRaw {
                slice_value: None,
                wrong_value: "no-prop",
            };
            if let Some(value) = raw_config.get(prop) {
                if !value.is_null() {
                    if let Value::List(_) = value {
                        // Go `propOfRaw{sliceValue: result.([]any)}` — the
                        // struct literal leaves `wrongValue` at its "" zero
                        // value, so a present array prop is neither
                        // "no-prop" nor "not-array".
                        result.wrong_value = "";
                        let result_value = raw_config.get(prop).cloned().unwrap();
                        if let Some(list) = result_value.as_list() {
                            if source_file.is_none() && !core::every(list, |v| validate_element(v))
                            {
                                errors.push(new_compiler_diagnostic(
                                    &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                                    &[
                                        Value::Str(prop.into()),
                                        Value::Str(element_type_name.into()),
                                    ],
                                ));
                            }
                        }
                        result.slice_value = result_value.as_list().cloned();
                    } else if source_file.is_none() {
                        errors.push(new_compiler_diagnostic(
                            &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                            &[Value::Str(prop.into()), Value::Str("Array".into())],
                        ));
                        result.wrong_value = "not-array";
                        result.slice_value = None;
                    }
                }
            }
            result
        }};
    }

    let references_of_raw = get_prop_from_raw!(
        "references",
        &|element: &Value| { element.as_map().is_some() },
        "object"
    );
    let file_specs = get_prop_from_raw!("files", &is_string_value, "string");
    if file_specs.slice_value.is_some() || file_specs.wrong_value.is_empty() {
        let has_zero_or_no_references = references_of_raw.wrong_value == "no-prop"
            || references_of_raw.wrong_value == "not-array"
            || references_of_raw
                .slice_value
                .as_ref()
                .is_none_or(|s| s.is_empty());
        let has_extends = raw_config.get("extends");
        if file_specs
            .slice_value
            .as_ref()
            .is_some_and(|s| s.is_empty())
            && has_zero_or_no_references
            && has_extends.is_none_or(|v| v.is_null())
        {
            if let Some(source_file) = source_file {
                let file_name = if !config_file_name.as_string().is_empty() {
                    config_file_name.as_string().to_string()
                } else {
                    "tsconfig.json".to_string()
                };
                let node_value = for_each_ts_config_prop_array(
                    Some(source_file.as_ctx()),
                    "files",
                    &mut |property| property.initializer,
                );
                errors.push(create_diagnostic_for_node_in_source_file(
                    source_file.as_ctx(),
                    node_value.expect("files property exists"),
                    &diagnostics::The_files_list_in_config_file_0_is_empty,
                    &[Value::Str(file_name)],
                ));
            } else {
                errors.push(new_compiler_diagnostic(
                    &diagnostics::The_files_list_in_config_file_0_is_empty,
                    &[Value::Str(config_file_name.as_string().into())],
                ));
            }
        }
    }
    let include_specs = get_prop_from_raw!("include", &is_string_value, "string");
    let mut exclude_specs = get_prop_from_raw!("exclude", &is_string_value, "string");
    let mut is_default_include_spec = false;
    if exclude_specs.wrong_value == "no-prop" && parsed_config.options.is_some() {
        let compiler_options = parsed_config
            .options
            .as_ref()
            .and_then(|o| o.compiler_options.as_deref());
        let out_dir = compiler_options
            .map(|o| o.out_dir.clone())
            .unwrap_or_default();
        let declaration_dir = compiler_options
            .map(|o| o.declaration_dir.clone())
            .unwrap_or_default();
        if !out_dir.as_string().is_empty() || !declaration_dir.as_string().is_empty() {
            let mut values = Vec::new();
            if !out_dir.as_string().is_empty() {
                values.push(Value::Str(out_dir.as_string().to_string()));
            }
            if !declaration_dir.as_string().is_empty() {
                values.push(Value::Str(declaration_dir.as_string().to_string()));
            }
            exclude_specs.slice_value = Some(values);
        }
    }
    let mut include_specs = include_specs;
    if file_specs.slice_value.is_none() && include_specs.slice_value.is_none() {
        include_specs.slice_value = Some(vec![Value::Str(DEFAULT_INCLUDE_SPEC.to_string())]);
        is_default_include_spec = true;
    }
    let mut validated_include_specs: Vec<PathPattern> = Vec::new();
    let mut validated_include_specs_before_substitution: Vec<PathPattern> = Vec::new();
    let mut validated_exclude_specs: Vec<PathPattern> = Vec::new();
    let mut validated_files_spec: Vec<FileSpec> = Vec::new();
    let mut validated_files_spec_before_substitution: Vec<FileSpec> = Vec::new();
    // The exclude spec list is converted into a regular expression, which
    // allows us to quickly test whether a file or directory should be
    // excluded before recursively traversing the file system.
    if let Some(include_slice) = &include_specs.slice_value {
        let (specs, err) = validate_specs(
            include_slice,
            true, /*disallowTrailingRecursion*/
            tsconfig_to_source_file(source_file.map(|s| s.as_ref())),
            "include",
        );
        errors.extend(err);
        validated_include_specs_before_substitution = specs;
        let substituted: Vec<String> = validated_include_specs_before_substitution
            .iter()
            .map(|p| p.as_string().to_string())
            .collect();
        validated_include_specs = match get_substituted_string_array_with_config_dir_template(
            &substituted,
            &base_path_for_file_names,
        ) {
            Some(substituted) => substituted
                .iter()
                .map(|s| tspath::to_path_pattern(s))
                .collect(),
            None => validated_include_specs_before_substitution.clone(),
        };
    }
    if let Some(exclude_slice) = &exclude_specs.slice_value {
        let (specs, err) = validate_specs(
            exclude_slice,
            false,
            tsconfig_to_source_file(source_file.map(|s| s.as_ref())),
            "exclude",
        );
        errors.extend(err);
        validated_exclude_specs = specs;
        let strings: Vec<String> = validated_exclude_specs
            .iter()
            .map(|p| p.as_string().to_string())
            .collect();
        if let Some(substituted) = get_substituted_string_array_with_config_dir_template(
            &strings,
            &base_path_for_file_names,
        ) {
            validated_exclude_specs = substituted
                .iter()
                .map(|s| tspath::to_path_pattern(s))
                .collect();
        }
    }
    if let Some(file_slice) = &file_specs.slice_value {
        let file_strings: Vec<&Value> = file_slice.iter().filter(|v| is_string_value(v)).collect();
        for spec in &file_strings {
            if let Some(spec) = spec.as_str() {
                validated_files_spec_before_substitution.push(tspath::to_file_spec(spec));
            }
        }
        let strings: Vec<String> = validated_files_spec_before_substitution
            .iter()
            .map(|f| f.as_string().to_string())
            .collect();
        validated_files_spec = match get_substituted_string_array_with_config_dir_template(
            &strings,
            &base_path_for_file_names,
        ) {
            Some(substituted) => substituted
                .iter()
                .map(|s| tspath::to_file_spec(s))
                .collect(),
            None => validated_files_spec_before_substitution.clone(),
        };
    }
    let case_sensitivity = fs.case_sensitivity();
    let mut validated_file_names: Vec<RootedFilePath> =
        Vec::with_capacity(validated_files_spec.len());
    let mut file_spec_by_path: HashMap<PathKey, FileSpec> =
        HashMap::with_capacity(validated_files_spec.len());
    for (i, spec) in validated_files_spec.iter().enumerate() {
        let file_name = if spec.as_string().is_empty() {
            RootedFilePath::from(base_path_for_file_names.as_string().to_string())
        } else {
            tspath::to_rooted_file_path(spec.as_string(), &base_path_for_file_names)
        };
        validated_file_names.push(file_name.clone());
        let path = case_sensitivity.path_key(&file_name.as_path());
        file_spec_by_path
            .entry(path)
            .or_insert_with(|| validated_files_spec_before_substitution[i].clone());
    }
    let config_file_specs = Arc::new(ConfigFileSpecs {
        files_specs: file_specs.slice_value.clone().map(Value::List),
        include_specs: include_specs.slice_value.clone().map(Value::List),
        exclude_specs: exclude_specs.slice_value.clone().map(Value::List),
        validated_files_spec,
        validated_file_names,
        file_spec_by_path,
        validated_include_specs,
        validated_exclude_specs,
        validated_files_spec_before_substitution,
        validated_include_specs_before_substitution,
        is_default_include_spec,
    });

    if let Some(source_file) = source_file {
        *source_file
            .config_file_specs
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(config_file_specs.clone());
    }

    let content_mapper_source_file = source_file.map(|s| s.as_ctx());
    let mut content_mappers: Vec<Mapper> = Vec::new();
    let mut content_mapper_indices: Vec<usize> = Vec::new();
    let content_mappers_of_raw = get_prop_from_raw!(
        "contentMappers",
        &|element: &Value| element.as_map().is_some(),
        "object"
    );
    if let Some(slice) = &content_mappers_of_raw.slice_value {
        for (i, element) in slice.iter().enumerate() {
            let (mapper, mapper_errors) = parsinghelpers::parse_content_mapper(element);
            for mapper_error in mapper_errors {
                errors.push(set_content_mapper_diagnostic_location(
                    mapper_error,
                    content_mapper_source_file,
                    get_content_mapper_syntax(content_mapper_source_file, i as i64, ""),
                ));
            }
            if let Some(mut mapper) = mapper {
                let _ = &mut mapper;
                content_mappers.push(mapper);
                content_mapper_indices.push(i);
            }
        }
    }
    let total_content_mapper_extensions: usize = content_mappers
        .iter()
        .map(|m| m.extensions.as_ref().map(|e| e.len()).unwrap_or_default())
        .sum();
    let mut seen_content_mapper_extensions: HashMap<String, ()> =
        HashMap::with_capacity(total_content_mapper_extensions);
    let mut content_mapper_extensions: Vec<String> =
        Vec::with_capacity(total_content_mapper_extensions);
    // PORT: `tspath.AllSupportedExtensionsWithJson` is `[][]string` in Go; the
    // Rust static holds `&[&str]` groups — flatten to a `Vec<&str>`.
    let native_extensions: Vec<&str> = tspath::ALL_SUPPORTED_EXTENSIONS_WITH_JSON
        .iter()
        .flat_map(|group| group.iter().copied())
        .collect();
    let canonical_extension =
        |extension: &str| -> String { fs.case_sensitivity().canonicalize(extension).into_owned() };
    for (j, mapper) in content_mappers.iter_mut().enumerate() {
        let mut valid_extensions = Vec::with_capacity(
            mapper
                .extensions
                .as_deref()
                .map(<[_]>::len)
                .unwrap_or_default(),
        );
        for ext in mapper.extensions.clone().unwrap_or_default() {
            let ext_node = get_content_mapper_extension_syntax(
                content_mapper_source_file,
                content_mapper_indices[j] as i64,
                &ext,
            );
            let canonical_ext = canonical_extension(&ext);
            if !ext.starts_with('.') {
                errors.push(set_content_mapper_diagnostic_location(
                    new_compiler_diagnostic(
                        &diagnostics::Content_mapper_file_extension_0_must_begin_with_a,
                        &[Value::Str(ext.clone())],
                    ),
                    content_mapper_source_file,
                    ext_node,
                ));
            } else if native_extensions
                .iter()
                .any(|native_extension| native_extension.eq_ignore_ascii_case(&ext))
            {
                errors.push(set_content_mapper_diagnostic_location(
                    new_compiler_diagnostic(
                        &diagnostics::Content_mapper_file_extension_0_is_a_built_in_extension_and_cannot_be_registered_by_a_content_mapper,
                        &[Value::Str(ext.clone())],
                    ),
                    content_mapper_source_file,
                    ext_node,
                ));
            } else if seen_content_mapper_extensions.contains_key(&canonical_ext) {
                errors.push(set_content_mapper_diagnostic_location(
                    new_compiler_diagnostic(
                        &diagnostics::Content_mapper_file_extension_0_is_registered_by_more_than_one_content_mapper,
                        &[Value::Str(ext.clone())],
                    ),
                    content_mapper_source_file,
                    ext_node,
                ));
            } else {
                seen_content_mapper_extensions.insert(canonical_ext, ());
                content_mapper_extensions.push(ext.clone());
                valid_extensions.push(ext);
            }
        }
        mapper.extensions = Some(valid_extensions);
    }
    let run_external_code = parsed_config
        .options
        .as_ref()
        .and_then(|o| o.compiler_options.as_deref())
        .is_some_and(|o| o.run_external_code.is_true());
    if !content_mappers.is_empty() && !run_external_code {
        errors.push(set_content_mapper_diagnostic_location(
            new_compiler_diagnostic(
                &diagnostics::Content_mappers_require_the_runExternalCode_command_line_flag_to_be_enabled,
                &Vec::<Value>::new(),
            ),
            content_mapper_source_file,
            get_content_mappers_key_syntax(content_mapper_source_file),
        ));
        // Without the flag the mappers are not trusted to run, so drop them
        // entirely: their extensions are not registered and their files are
        // not intercepted (they are treated as unknown foreign files).
        content_mappers = Vec::new();
        content_mapper_extensions = Vec::new();
    } else if !content_mappers.is_empty() {
        // Resolve each mapper's package.json now so its name, version, and
        // run command are available to everything downstream (diagnostics,
        // build-info staleness) without executing anything.
        let containing_file = if !config_file_name.as_string().is_empty() {
            config_file_name.clone()
        } else {
            base_path_for_file_names.resolve_file("tsconfig.json")
        };
        let mut resolved_content_mappers = Vec::with_capacity(content_mappers.len());
        for (j, mapper) in content_mappers.iter_mut().enumerate() {
            let (manifest, package_directory, diagnostic) =
                resolve_content_mapper_manifest(fs, &containing_file, &mapper.package);
            mapper.package_directory = package_directory;
            if let Some(diagnostic) = diagnostic {
                errors.push(set_content_mapper_diagnostic_location(
                    diagnostic,
                    content_mapper_source_file,
                    get_content_mapper_syntax(
                        content_mapper_source_file,
                        content_mapper_indices[j] as i64,
                        "package",
                    ),
                ));
                continue;
            }
            if let Some(manifest) = manifest {
                mapper.name = manifest.name;
                mapper.version = manifest.version;
                mapper.exec = manifest.exec;
                mapper.compiler_options = manifest.compiler_options;
                mapper.dynamic_config = manifest.dynamic_config;
            }
            resolved_content_mappers.push(mapper.clone());
        }
        content_mappers = resolved_content_mappers;
        content_mapper_extensions = core::flat_map(&content_mappers, |mapper| {
            mapper.extensions.clone().unwrap_or_default()
        });
    }

    let can_json_report_no_input_files = can_json_report_no_input_files(&raw_config);
    let resolution_stack_empty = resolution_stack.is_empty();

    let get_file_names = |base_path: &RootedDirectoryPath,
                          errors: &mut Vec<DiagnosticRef>|
     -> (Vec<RootedFilePath>, usize) {
        let parsed_config_options = parsed_config.options.as_ref();
        let (file_names, literal_file_names_len) = get_file_names_from_config_specs(
            &config_file_specs,
            base_path,
            parsed_config_options
                .and_then(|o| o.compiler_options.as_deref())
                .expect("parsedConfig.options"),
            fs,
            &content_mapper_extensions,
        );
        if should_report_no_input_files(
            &file_names,
            can_json_report_no_input_files,
            resolution_stack_empty,
        ) {
            let include_specs = config_file_specs
                .include_specs
                .clone()
                .unwrap_or_else(|| Value::List(Vec::new()));
            let exclude_specs = config_file_specs
                .exclude_specs
                .clone()
                .unwrap_or_else(|| Value::List(Vec::new()));
            errors.push(new_compiler_diagnostic(
                    &diagnostics::No_inputs_were_found_in_config_file_0_Specified_include_paths_were_1_and_exclude_paths_were_2,
                    &[
                        Value::Str(config_file_name.as_string().into()),
                        Value::Str(
                            core::stringify_json(&include_specs, "", "")
                                .expect("JSON stringify"),
                        ),
                        Value::Str(
                            core::stringify_json(&exclude_specs, "", "")
                                .expect("JSON stringify"),
                        ),
                    ],
                ));
        }
        (file_names, literal_file_names_len)
    };

    let get_project_references = |errors: &mut Vec<DiagnosticRef>| -> Vec<ProjectReference> {
        let mut project_references = Vec::new();
        let new_references_of_raw = {
            let mut result = PropOfRaw {
                slice_value: None,
                wrong_value: "no-prop",
            };
            if let Some(value) = raw_config.get("references") {
                if !value.is_null() {
                    if let Value::List(_) = value {
                        result.wrong_value = "";
                        result.slice_value = value.as_list().cloned();
                        if source_file.is_none()
                            && !core::every(result.slice_value.as_deref().unwrap_or(&[]), |v| {
                                v.as_map().is_some()
                            })
                        {
                            errors.push(new_compiler_diagnostic(
                                &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                                &[Value::Str("references".into()), Value::Str("object".into())],
                            ));
                        }
                    } else if source_file.is_none() {
                        errors.push(new_compiler_diagnostic(
                            &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                            &[Value::Str("references".into()), Value::Str("Array".into())],
                        ));
                        result.wrong_value = "not-array";
                    }
                }
            }
            result
        };
        if let Some(slice) = &new_references_of_raw.slice_value {
            for (index, reference) in slice.iter().enumerate() {
                let Some(ref_) = parse_project_reference(reference) else {
                    continue;
                };
                if !ref_.has_path || !ref_.path_valid {
                    errors.push(create_diagnostic_at_project_reference_property(
                        source_file.map(|s| s.as_ref()),
                        index,
                        "path",
                        &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                        &[
                            Value::Str("reference.path".into()),
                            Value::Str("string".into()),
                        ],
                    ));
                    continue;
                }
                if ref_.path.is_empty() {
                    errors.push(create_diagnostic_at_project_reference_property(
                        source_file.map(|s| s.as_ref()),
                        index,
                        "path",
                        &diagnostics::Compiler_option_0_cannot_be_given_an_empty_string,
                        &[Value::Str("reference.path".into())],
                    ));
                    continue;
                }
                if ref_.has_circular && !ref_.circular_valid {
                    errors.push(create_diagnostic_at_project_reference_property(
                        source_file.map(|s| s.as_ref()),
                        index,
                        "circular",
                        &diagnostics::Compiler_option_0_requires_a_value_of_type_1,
                        &[
                            Value::Str("reference.circular".into()),
                            Value::Str("boolean".into()),
                        ],
                    ));
                }
                project_references.push(ProjectReference {
                    path: tspath::to_rooted_path(&ref_.path, &base_path_for_file_names),
                    original_path: ref_.path.clone(),
                    circular: ref_.reference.circular,
                    ..Default::default()
                });
            }
        }
        project_references
    };

    let (file_names, literal_file_names_len) =
        get_file_names(&base_path_for_file_names, &mut errors);
    // Go: compileOnSave := new(false) — non-nil false by default.
    let mut compile_on_save = Some(false);
    if let Some(raw) = parsed_config.raw.as_ref().and_then(|r| r.as_map()) {
        if let Some(value) = raw.get("compileOnSave").and_then(|v| v.as_bool()) {
            compile_on_save = Some(value);
        }
    }
    let parsed_config_compiler_options = parsed_config
        .options
        .as_ref()
        .and_then(|o| o.compiler_options.as_deref())
        .cloned()
        .unwrap_or_default();
    let content_mapper_extensions_cache = content_mapper_extensions;
    ParsedCommandLine {
        parsed_config: Some(crate::parsedoptions::ParsedOptions {
            compiler_options: Some(parsed_config_compiler_options),
            type_acquisition: parsed_config.type_acquisition.map(|t| *t),
            file_names,
            project_references: get_project_references(&mut errors),
            content_mappers: content_mappers.into_iter().map(Arc::new).collect(),
        }),
        config_file: source_file.cloned(),
        raw: parsed_config.raw,
        errors: Mutex::new(errors),
        compile_on_save,

        config_file_specs: Some(config_file_specs),
        base_directory: base_path_for_file_names,
        case_sensitivity: fs.case_sensitivity(),
        literal_file_names_len,
        content_mapper_extensions_cache,
        ..Default::default()
    }
}

/// `canJsonReportNoInputFiles`.
fn can_json_report_no_input_files(raw_config: &OrderedMap<String, Value>) -> bool {
    raw_config.get("files").is_none() && raw_config.get("references").is_none()
}

/// `shouldReportNoInputFiles`.
fn should_report_no_input_files(
    file_names: &[RootedFilePath],
    can_json_report_no_input_files: bool,
    resolution_stack_empty: bool,
) -> bool {
    file_names.is_empty() && can_json_report_no_input_files && resolution_stack_empty
}

/// `validateSpecs`.
fn validate_specs(
    specs: &[Value],
    disallow_trailing_recursion: bool,
    json_source_file: Option<SourceFileCtx<'_>>,
    spec_key: &str,
) -> (Vec<PathPattern>, Vec<DiagnosticRef>) {
    let create_diagnostic = |message: &'static Message, spec: &str| -> DiagnosticRef {
        let element = get_ts_config_prop_array_element_value(json_source_file, spec_key, spec);
        let node = element.or_else(|| {
            // Go falls back to the element node when found, or nil
            element
        });
        create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
            json_source_file,
            node,
            message,
            &[Value::Str(spec.to_string())],
        )
    };
    let mut errors = Vec::new();
    let mut final_specs = Vec::new();
    for value in specs {
        let Some(spec) = value.as_str() else {
            continue;
        };
        if let Some(diag) = spec_to_diagnostic(spec, disallow_trailing_recursion) {
            errors.push(create_diagnostic(diag, spec));
        } else {
            final_specs.push(tspath::to_path_pattern(spec));
        }
    }
    (final_specs, errors)
}

/// `specToDiagnostic`.
fn spec_to_diagnostic(spec: &str, disallow_trailing_recursion: bool) -> Option<&'static Message> {
    if disallow_trailing_recursion && invalid_trailing_recursion(spec) {
        return Some(&diagnostics::File_specification_cannot_end_in_a_recursive_directory_wildcard_Asterisk_Asterisk_Colon_0);
    }
    if invalid_dot_dot_after_recursive_wildcard(spec) {
        return Some(&diagnostics::File_specification_cannot_contain_a_parent_directory_that_appears_after_a_recursive_directory_wildcard_Asterisk_Asterisk_Colon_0);
    }
    None
}

/// `invalidTrailingRecursion`.
fn invalid_trailing_recursion(spec: &str) -> bool {
    // Matches **, /**, **/, and /**/, but not a**b.
    let s = spec.strip_suffix('/').unwrap_or(spec);
    s == "**" || s.ends_with("/**")
}

/// `invalidDotDotAfterRecursiveWildcard`.
fn invalid_dot_dot_after_recursive_wildcard(s: &str) -> bool {
    let wildcard_index = if s.starts_with("**/") {
        Some(0)
    } else {
        s.find("/**/")
    };
    let Some(wildcard_index) = wildcard_index else {
        return false;
    };
    let last_dot_index = if s.ends_with("/..") {
        Some(s.len())
    } else {
        s.rfind("/../")
    };
    last_dot_index.is_some_and(|i| i > wildcard_index)
}

// ---------------------------------------------------------------------------
// tsconfig property syntax helpers
// ---------------------------------------------------------------------------

/// `GetTsConfigPropArrayElementValue`.
pub fn get_ts_config_prop_array_element_value(
    ts_config_source_file: Option<SourceFileCtx<'_>>,
    prop_key: &str,
    element_value: &str,
) -> Option<NodeId> {
    ts_config_source_file.and_then(|sf| {
        let callback = find_property_assignment_by_value(sf, element_value);
        for_each_ts_config_prop_array(Some(sf), prop_key, &mut |property| callback(property))
    })
}

/// `ForEachTsConfigPropArray`.
pub fn for_each_ts_config_prop_array<T>(
    ts_config_source_file: Option<SourceFileCtx<'_>>,
    prop_key: &str,
    callback: &mut dyn FnMut(&PropertyAssignment) -> Option<T>,
) -> Option<T> {
    ts_config_source_file.and_then(|sf| {
        for_each_property_assignment(
            get_ts_config_object_literal_expression(sf),
            sf,
            prop_key,
            callback,
            None,
        )
    })
}

/// `CreateDiagnosticAtReferenceSyntax`.
pub fn create_diagnostic_at_reference_syntax(
    config: &ParsedCommandLine,
    index: usize,
    message: &'static Message,
    args: &[Value],
) -> Option<DiagnosticRef> {
    let config_file = config.config_file.as_ref()?;
    for_each_ts_config_prop_array(Some(config_file.as_ctx()), "references", &mut |property| {
        let Some(initializer) = property.initializer else {
            return None;
        };
        let node = config_file.node(initializer);
        if node.kind == Kind::ArrayLiteralExpression {
            let elements = node
                .as_array_literal_expression()
                .elements
                .as_ref()
                .map(|l| &l.nodes[..])
                .unwrap_or(&[]);
            if elements.len() > index {
                return Some(create_diagnostic_for_node_in_source_file(
                    config_file.as_ctx(),
                    elements[index],
                    message,
                    args,
                ));
            }
        }
        None
    })
}

/// `createDiagnosticAtProjectReferenceProperty`.
fn create_diagnostic_at_project_reference_property(
    source_file: Option<&TsConfigSourceFile>,
    index: usize,
    property_name: &str,
    message: &'static Message,
    args: &[Value],
) -> DiagnosticRef {
    let node = source_file.and_then(|source_file| {
        for_each_ts_config_prop_array(Some(source_file.as_ctx()), "references", &mut |property| {
            let Some(initializer) = property.initializer else {
                return None;
            };
            let node = source_file.node(initializer);
            if node.kind != Kind::ArrayLiteralExpression {
                return None;
            }
            let elements = node
                .as_array_literal_expression()
                .elements
                .as_ref()
                .map(|l| &l.nodes[..])
                .unwrap_or(&[]);
            if elements.len() > index
                && source_file.node(elements[index]).kind == Kind::ObjectLiteralExpression
            {
                let property_node = for_each_property_assignment(
                    Some(elements[index]),
                    source_file.as_ctx(),
                    property_name,
                    &mut |property| property.initializer,
                    None,
                );
                if property_node.is_some() {
                    return property_node;
                }
                return Some(elements[index]);
            }
            None
        })
    });
    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
        tsconfig_to_source_file(source_file),
        node,
        message,
        args,
    )
}

// `GetCallbackForFindingPropertyAssignmentByValue` — the Go version captures
// `*ast.Node` pointers implicitly; here the callback needs the node arena, so
// it takes `SourceFileCtx`.
fn find_property_assignment_by_value<'a>(
    source_file: SourceFileCtx<'a>,
    value: &'a str,
) -> impl Fn(&PropertyAssignment) -> Option<NodeId> + 'a {
    move |property| {
        let Some(initializer) = property.initializer else {
            return None;
        };
        let node = source_file.node(initializer);
        if node.kind == Kind::ArrayLiteralExpression {
            return core::find(
                &node
                    .as_array_literal_expression()
                    .elements
                    .as_ref()
                    .map(|l| &l.nodes[..])
                    .unwrap_or(&[]),
                |element| {
                    let n = source_file.node(*element);
                    n.kind == Kind::StringLiteral && n.text(source_file.nodes) == value
                },
            );
        }
        None
    }
}

/// `GetOptionsSyntaxByArrayElementValue`.
pub fn get_options_syntax_by_array_element_value(
    object_literal: Option<NodeId>,
    source_file: SourceFileCtx<'_>,
    prop_key: &str,
    element_value: &str,
) -> Option<NodeId> {
    for_each_property_assignment(
        object_literal,
        source_file,
        prop_key,
        &mut |property| find_property_assignment_by_value(source_file, element_value)(property),
        None,
    )
}

/// `getContentMapperSyntax` — the tsconfig JSON node to attribute a
/// diagnostic about the content mapper at `index` to: the value of `subKey`
/// within that mapper's object (when `subKey` is non-empty), falling back to
/// the mapper element, then to the "contentMappers" array. An index outside
/// the array (e.g. -1) yields the array itself. Returns `None` when there is
/// no source file (JSON API).
fn get_content_mapper_syntax(
    source_file: Option<SourceFileCtx<'_>>,
    index: i64,
    sub_key: &str,
) -> Option<NodeId> {
    source_file.and_then(|source_file| {
        for_each_ts_config_prop_array(Some(source_file), "contentMappers", &mut |property| {
            let Some(initializer) = property.initializer else {
                return None;
            };
            let node = source_file.node(initializer);
            if node.kind != Kind::ArrayLiteralExpression {
                return Some(initializer);
            }
            let elements = node
                .as_array_literal_expression()
                .elements
                .as_ref()
                .map(|l| &l.nodes[..])
                .unwrap_or(&[]);
            if index < 0 || index as usize >= elements.len() {
                return Some(initializer);
            }
            let element = elements[index as usize];
            if !sub_key.is_empty()
                && source_file.node(element).kind == Kind::ObjectLiteralExpression
            {
                if let Some(node) = for_each_property_assignment(
                    Some(element),
                    source_file,
                    sub_key,
                    &mut |property| property.initializer,
                    None,
                ) {
                    return Some(node);
                }
            }
            Some(element)
        })
    })
}

/// `GetContentMapperOptionDiagnosticLocation` — returns the tsconfig source
/// file and range for a content-mapper option diagnostic.
pub fn get_content_mapper_option_diagnostic_location<'a>(
    config: Option<&'a ParsedCommandLine>,
    mapper: &Mapper,
    path: &[OptionPathSegment],
) -> Option<(SourceFileCtx<'a>, TextRange)> {
    let config = config?;
    let config_file = config.config_file.as_ref()?;
    let index = config
        .parsed_config
        .as_ref()?
        .content_mappers
        .iter()
        .position(|m| std::ptr::eq(Arc::as_ptr(m), mapper))
        .map(|i| i as i64)
        .unwrap_or(-1);
    let source_file = config_file.as_ctx();
    let mapper_node = get_content_mapper_syntax(Some(source_file), index, "");
    let mut node = get_content_mapper_syntax(Some(source_file), index, "options").or(mapper_node);
    for segment in path {
        let mut next: Option<NodeId> = None;
        if let Some(node_id) = node {
            let n = source_file.node(node_id);
            if segment.is_index && n.kind == Kind::ArrayLiteralExpression {
                let elements = n
                    .as_array_literal_expression()
                    .elements
                    .as_ref()
                    .map(|l| &l.nodes[..])
                    .unwrap_or(&[]);
                if segment.index >= 0 && (segment.index as usize) < elements.len() {
                    next = Some(elements[segment.index as usize]);
                }
            } else if !segment.is_index && n.kind == Kind::ObjectLiteralExpression {
                next = for_each_property_assignment(
                    Some(node_id),
                    source_file,
                    &segment.property,
                    &mut |property| property.initializer,
                    None,
                );
            }
        }
        let Some(next_id) = next else {
            break;
        };
        node = Some(next_id);
    }
    let node = node?;
    let loc = TextRange::new(
        skip_trivia(source_file.text(), source_file.node(node).pos()),
        source_file.node(node).end(),
    );
    Some((source_file, loc))
}

/// `getContentMappersKeySyntax` — the "contentMappers" property key node.
fn get_content_mappers_key_syntax(source_file: Option<SourceFileCtx<'_>>) -> Option<NodeId> {
    source_file.and_then(|source_file| {
        for_each_ts_config_prop_array(Some(source_file), "contentMappers", &mut |property| {
            property.named_member_base.name
        })
    })
}

/// `getContentMapperExtensionSyntax` — the node for a specific extension
/// string within the content mapper at `index`, falling back to the
/// "extensions" array or the mapper element.
fn get_content_mapper_extension_syntax(
    source_file: Option<SourceFileCtx<'_>>,
    index: i64,
    ext: &str,
) -> Option<NodeId> {
    let node = get_content_mapper_syntax(source_file, index, "extensions");
    if let Some(node) = node {
        if let Some(source_file) = source_file {
            let n = source_file.node(node);
            if n.kind == Kind::ArrayLiteralExpression {
                if let Some(element) = core::find(
                    &n.as_array_literal_expression()
                        .elements
                        .as_ref()
                        .map(|l| &l.nodes[..])
                        .unwrap_or(&[]),
                    |element| {
                        let e = source_file.node(*element);
                        e.kind == Kind::StringLiteral && e.text(source_file.nodes) == ext
                    },
                ) {
                    return Some(element);
                }
            }
        }
    }
    node
}

/// `setContentMapperDiagnosticLocation` — attaches a source location to a
/// content mapper diagnostic when a tsconfig source file and node are
/// available, leaving it as a location-less compiler diagnostic otherwise.
fn set_content_mapper_diagnostic_location(
    diagnostic: DiagnosticRef,
    source_file: Option<SourceFileCtx<'_>>,
    node: Option<NodeId>,
) -> DiagnosticRef {
    if let (Some(source_file), Some(node)) = (source_file, node) {
        let n = source_file.node(node);
        let mut d = tsc_ast::diagnostic::lock_diagnostic(&diagnostic);
        d.set_file(Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
            source_file.file,
            source_file.nodes,
        )));
        d.set_location(TextRange::new(
            skip_trivia(source_file.text(), n.pos()),
            n.end(),
        ));
    }
    diagnostic
}

/// `ForEachPropertyAssignment`.
pub fn for_each_property_assignment<T>(
    object_literal: Option<NodeId>,
    source_file: SourceFileCtx<'_>,
    key: &str,
    callback: &mut dyn FnMut(&PropertyAssignment) -> Option<T>,
    key2: Option<&str>,
) -> Option<T> {
    let object_literal = object_literal?;
    let node = source_file.node(object_literal);
    if node.kind != Kind::ObjectLiteralExpression {
        return None;
    }
    for property in node
        .as_object_literal_expression()
        .properties
        .as_ref()
        .map(|l| l.nodes.iter().copied())
        .into_iter()
        .flatten()
    {
        let p = source_file.node(property);
        if p.kind != Kind::PropertyAssignment {
            continue;
        }
        let property_assignment = p.as_property_assignment();
        // PORT: Go's `tryGetTextOfPropertyName` returns `false` for nil names.
        let Some(name) = property_assignment.named_member_base.name else {
            continue;
        };
        let (prop_name, ok) = try_get_text_of_property_name(name, source_file.nodes);
        if !ok {
            continue;
        }
        let prop_name = prop_name.unwrap_or_default();
        if prop_name == key || key2 == Some(prop_name.as_str()) {
            return callback(property_assignment);
        }
    }
    None
}

/// `getTsConfigObjectLiteralExpression`.
fn get_ts_config_object_literal_expression(
    ts_config_source_file: SourceFileCtx<'_>,
) -> Option<NodeId> {
    let statements = ts_config_source_file
        .node(ts_config_source_file.file)
        .as_source_file()
        .statements
        .as_ref()?;
    if statements.nodes.is_empty() {
        return None;
    }
    let stmt = ts_config_source_file.node(statements.nodes[0]);
    let Some(expression) = (match stmt.kind {
        Kind::ExpressionStatement => stmt.as_expression_statement().expression,
        _ => return None,
    }) else {
        return None;
    };
    if ts_config_source_file.node(expression).kind == Kind::ObjectLiteralExpression {
        return Some(expression);
    }
    None
}

// ---------------------------------------------------------------------------
// wildcard file expansion
// ---------------------------------------------------------------------------

/// `hasFileWithHigherPriorityExtension` — determines whether a literal or
/// wildcard file has already been included that has a higher extension
/// priority.
fn has_file_with_higher_priority_extension(
    file: &RootedFilePath,
    extensions: &[Vec<String>],
    has_file: &mut dyn FnMut(&RootedFilePath) -> bool,
) -> bool {
    let mut extension_group: Vec<&str> = Vec::new();
    for group in extensions {
        if file.extension_is_one_of(&group.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
            extension_group.extend(group.iter().map(|s| s.as_str()));
        }
    }
    if extension_group.is_empty() {
        return false;
    }
    for ext in extension_group {
        // d.ts files match with .ts extension and with case sensitive sorting
        // the file order for same files with ts tsx and dts extension is
        // d.ts, .ts, .tsx in that order so we need to handle tsx and dts of
        // same same name case here and in remove files with same extensions
        // So dont match .d.ts files with .ts extension
        if file.extension_is(ext)
            && !(ext == tspath::EXTENSION_TS && file.extension_is(tspath::EXTENSION_DTS))
        {
            return false;
        }
        if has_file(&file.change_extension(ext)) {
            if ext == tspath::EXTENSION_DTS
                && (file.extension_is(tspath::EXTENSION_JS)
                    || file.extension_is(tspath::EXTENSION_JSX))
            {
                // LEGACY BEHAVIOR: An off-by-one bug somewhere in the
                // extension priority system for wildcard module loading
                // allowed declaration files to be loaded alongside their
                // js(x) counterparts. We regard this as generally
                // undesirable, but retain the behavior to prevent breakage.
                continue;
            }
            return true;
        }
    }
    false
}

/// `removeWildcardFilesWithLowerPriorityExtension` — removes files included
/// via wildcard expansion with a lower extension priority that have already
/// been included.
fn remove_wildcard_files_with_lower_priority_extension<V>(
    file: &RootedFilePath,
    wildcard_files: &mut OrderedMap<PathKey, V>,
    extensions: &[Vec<String>],
    key_mapper: &dyn Fn(&RootedFilePath) -> PathKey,
) {
    let mut extension_group: Vec<&str> = Vec::new();
    for group in extensions {
        if file.extension_is_one_of(&group.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
            extension_group.extend(group.iter().map(|s| s.as_str()));
        }
    }
    if extension_group.is_empty() {
        return;
    }
    for ext in extension_group.iter().rev() {
        if file.extension_is(ext) {
            return;
        }
        let lower_priority_path = key_mapper(&file.change_extension(ext));
        wildcard_files.delete(&lower_priority_path);
    }
}

/// `getFileNamesFromConfigSpecs`.
pub(crate) fn get_file_names_from_config_specs(
    config_file_specs: &ConfigFileSpecs,
    base_path: &RootedDirectoryPath,
    options: &CompilerOptions,
    host: &Arc<dyn Vfs>,
    extra_extensions: &[String],
) -> (Vec<RootedFilePath>, usize) {
    let key_mapper = |file_name: &RootedFilePath| -> PathKey {
        host.case_sensitivity().path_key(&file_name.as_path())
    };
    // Literal file names (provided via the "files" array in tsconfig.json)
    // are stored in a file map with a possibly case insensitive key.
    let mut literal_file_map: OrderedMap<PathKey, RootedFilePath> = OrderedMap::new();
    // Wildcard paths (provided via the "includes" array in tsconfig.json) are
    // stored in a file map with a possibly case insensitive key. We use this
    // map to store paths matched via wildcard, and to handle extension
    // priority.
    let mut wildcard_file_map: OrderedMap<PathKey, RootedFilePath> = OrderedMap::new();
    // Wildcard paths of json files (provided via the "includes" array in
    // tsconfig.json) are stored in a file map with a possibly case
    // insensitive key. We use this map to store paths matched via wildcard of
    // *.json kind
    let mut wild_card_json_file_map: OrderedMap<PathKey, RootedFilePath> = OrderedMap::new();
    let validated_files_spec = &config_file_specs.validated_files_spec;
    let validated_file_names = &config_file_specs.validated_file_names;
    let validated_include_specs = &config_file_specs.validated_include_specs;
    let validated_exclude_specs = &config_file_specs.validated_exclude_specs;
    // Rather than re-query this for each file and filespec, we query the
    // supported extensions once and store it on the expansion context.
    let supported_extensions = get_supported_extensions(options, extra_extensions);
    let supported_extensions_with_json_if_resolve_json_module =
        get_supported_extensions_with_json_if_resolve_json_module(
            Some(options),
            &supported_extensions,
        );
    // Literal files are always included verbatim. An "include" or "exclude"
    // specification cannot remove a literal file.
    for i in 0..validated_files_spec.len() {
        literal_file_map.set(
            key_mapper(&validated_file_names[i]),
            validated_file_names[i].clone(),
        );
    }

    let mut json_only_include_matchers: Option<vfsmatch::SpecMatcher> = None;
    if !validated_include_specs.is_empty() {
        let flat_extensions: Vec<&str> = supported_extensions_with_json_if_resolve_json_module
            .iter()
            .flat_map(|g| g.iter().map(|s| s.as_str()))
            .collect();
        let files = vfsmatch::read_directory(
            host,
            base_path,
            &flat_extensions,
            validated_exclude_specs,
            validated_include_specs,
            vfsmatch::UNLIMITED_DEPTH,
        );
        for file in files {
            if file.extension_is(tspath::EXTENSION_JSON) {
                if json_only_include_matchers.is_none() {
                    let includes: Vec<PathPattern> = validated_include_specs
                        .iter()
                        .filter(|include| include.as_string().ends_with(tspath::EXTENSION_JSON))
                        .cloned()
                        .collect();
                    json_only_include_matchers = vfsmatch::new_spec_matcher(
                        &includes,
                        base_path,
                        vfsmatch::USAGE_FILES,
                        host.case_sensitivity(),
                    );
                }
                let include_index = json_only_include_matchers
                    .as_ref()
                    .map(|m| m.match_file_name_index(&file))
                    .unwrap_or(-1);
                if include_index != -1 {
                    let key = key_mapper(&file);
                    if !literal_file_map.has(&key) && !wild_card_json_file_map.has(&key) {
                        wild_card_json_file_map.set(key, file);
                    }
                }
                continue;
            }
            // If we have already included a literal or wildcard path with a
            // higher priority extension, we should skip this file.
            //
            // This handles cases where we may encounter both <file>.ts and
            // <file>.d.ts (or <file>.js if "allowJs" is enabled) in the same
            // directory when they are compilation outputs.
            let mut has_file = |file_name: &RootedFilePath| -> bool {
                let canonical_file_name = key_mapper(file_name);
                literal_file_map.has(&canonical_file_name)
                    || wildcard_file_map.has(&canonical_file_name)
            };
            if has_file_with_higher_priority_extension(&file, &supported_extensions, &mut has_file)
            {
                continue;
            }
            // We may have included a wildcard path with a lower priority
            // extension due to the user-defined order of entries in the
            // "include" array. If there is a lower priority extension in the
            // same directory, we should remove it.
            remove_wildcard_files_with_lower_priority_extension(
                &file,
                &mut wildcard_file_map,
                &supported_extensions,
                &key_mapper,
            );
            let key = key_mapper(&file);
            if !literal_file_map.has(&key) && !wildcard_file_map.has(&key) {
                wildcard_file_map.set(key, file);
            }
        }
    }
    let mut files = Vec::with_capacity(
        literal_file_map.size() + wildcard_file_map.size() + wild_card_json_file_map.size(),
    );
    files.extend(literal_file_map.values().cloned());
    files.extend(wildcard_file_map.values().cloned());
    files.extend(wild_card_json_file_map.values().cloned());
    (files, literal_file_map.size())
}

/// `GetSupportedExtensions`.
pub fn get_supported_extensions(
    compiler_options: &CompilerOptions,
    extra_extensions: &[String],
) -> Vec<Vec<String>> {
    let need_js_extensions = compiler_options.get_allow_js();
    let builtins: Vec<Vec<String>> = if need_js_extensions {
        tspath::ALL_SUPPORTED_EXTENSIONS
            .iter()
            .map(|g| g.iter().map(|s| s.to_string()).collect())
            .collect()
    } else {
        tspath::SUPPORTED_TS_EXTENSIONS
            .iter()
            .map(|g| g.iter().map(|s| s.to_string()).collect())
            .collect()
    };
    if extra_extensions.is_empty() {
        return builtins;
    }
    let flat_builtins = core::flatten(&builtins);
    let mut result: Vec<Vec<String>> = Vec::new();
    for ext in extra_extensions {
        if !flat_builtins.iter().any(|b| b == ext) {
            result.push(vec![ext.clone()]);
        }
    }
    if result.is_empty() {
        return builtins;
    }
    let mut out = builtins;
    out.extend(result);
    out
}

/// `GetSupportedExtensionsWithJsonIfResolveJsonModule`.
pub fn get_supported_extensions_with_json_if_resolve_json_module(
    compiler_options: Option<&CompilerOptions>,
    supported_extensions: &[Vec<String>],
) -> Vec<Vec<String>> {
    let resolve_json = compiler_options
        .map(|o| o.get_resolve_json_module())
        .unwrap_or(false);
    if !resolve_json {
        return supported_extensions.to_vec();
    }
    let all_supported: Vec<Vec<String>> = tspath::ALL_SUPPORTED_EXTENSIONS
        .iter()
        .map(|g| g.iter().map(|s| s.to_string()).collect())
        .collect();
    if core::same(supported_extensions, &all_supported) {
        return tspath::ALL_SUPPORTED_EXTENSIONS_WITH_JSON
            .iter()
            .map(|g| g.iter().map(|s| s.to_string()).collect())
            .collect();
    }
    let supported_ts: Vec<Vec<String>> = tspath::SUPPORTED_TS_EXTENSIONS
        .iter()
        .map(|g| g.iter().map(|s| s.to_string()).collect())
        .collect();
    if core::same(supported_extensions, &supported_ts) {
        return tspath::SUPPORTED_TS_EXTENSIONS_WITH_JSON
            .iter()
            .map(|g| g.iter().map(|s| s.to_string()).collect())
            .collect();
    }
    let mut out = supported_extensions.to_vec();
    out.push(vec![tspath::EXTENSION_JSON.to_string()]);
    out
}

/// `GetParsedCommandLineOfConfigFile` — reads the config file and reports
/// errors.
pub fn get_parsed_command_line_of_config_file(
    config_file_name: RootedFilePath,
    options: Option<&CompilerOptions>,
    options_raw: Option<&OrderedMap<String, Value>>,
    fs: &Arc<dyn Vfs>,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> Result<ParsedCommandLine, Vec<DiagnosticRef>> {
    get_parsed_command_line_of_config_file_path(
        config_file_name.clone(),
        fs.case_sensitivity().path_key(&config_file_name.as_path()),
        options,
        options_raw,
        fs,
        extended_config_cache,
    )
}

/// `GetParsedCommandLineOfConfigFilePath`.
pub fn get_parsed_command_line_of_config_file_path(
    config_file_name: RootedFilePath,
    path: PathKey,
    options: Option<&CompilerOptions>,
    options_raw: Option<&OrderedMap<String, Value>>,
    fs: &Arc<dyn Vfs>,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> Result<ParsedCommandLine, Vec<DiagnosticRef>> {
    let (config_file_text, errors) =
        try_read_file(&config_file_name, |f| fs.read_file(f), Vec::new());
    if !errors.is_empty() {
        // these are unrecoverable errors--exit to report them as diagnostics
        return Err(errors);
    }

    let ts_config_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name.clone(),
        path,
        &config_file_text,
    ));
    Ok(parse_json_source_file_config_file_content(
        &ts_config_source_file,
        fs,
        config_file_name.directory(),
        options,
        options_raw,
        &[],
        extended_config_cache,
    ))
}
