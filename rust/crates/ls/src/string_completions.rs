// Ported from tsc/internal/ls/string_completions.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(arena): Go `*ast.Node`/`*ast.Symbol`/`*checker.Type` map to
// `NodeId`/`SymbolId`/`TypeId`; arenas are fetched per access via
// `program.nodes(file_index)` / `program.nodes_mut(file_index)` and
// `checker.types`/`checker.signature_arena` guards are held in locals to
// satisfy the borrow checker.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::ast::{NodeFactory, NodeFactoryHooks};
use tsc_ast::{self as ast, Kind, Node, NodeId, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{ContextFlags, TypeId};
use tsc_collections::{OrderedMap, Set};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::{TextPos, TextRange};
use tsc_lsproto::{self as lsproto};
use tsc_lsutil::symbol_display::{ScriptElementKind, ScriptElementKindModifier};
use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RelativePath, RootedDirectoryPath};

use crate::api::Error;
use crate::completions::{self, CompletionItem, CompletionList, get_default_commit_characters};
use crate::languageservice::LanguageService;
use crate::utilities;

/// `type completionsFromTypes struct` — `types` are the `TypeId`s of string
/// literal types (`*checker.StringLiteralType` in Go).
pub(crate) struct CompletionsFromTypes {
    /// `types`.
    pub(crate) types: Vec<TypeId>,
    /// `isNewIdentifier`.
    pub(crate) is_new_identifier: bool,
}

/// `type completionsFromProperties struct`.
pub(crate) struct CompletionsFromProperties {
    /// `symbols`.
    pub(crate) symbols: Vec<SymbolId>,
    /// `hasIndexSignature`.
    pub(crate) has_index_signature: bool,
}

/// `type pathCompletion struct`.
pub(crate) struct PathCompletion {
    /// `name`.
    pub(crate) name: String,
    /// `kind`.
    pub(crate) kind: ScriptElementKind,
    /// `extension`.
    pub(crate) extension: String,
}

/// `type pathCompletions struct`.
pub(crate) struct PathCompletions {
    /// `entries`.
    pub(crate) entries: Vec<PathCompletion>,
    /// `replacementSpan`.
    pub(crate) replacement_span: Option<lsproto::Range>,
}

/// `type stringLiteralCompletions struct`.
#[derive(Default)]
pub(crate) struct StringLiteralCompletions {
    /// `fromTypes`.
    pub(crate) from_types: Option<CompletionsFromTypes>,
    /// `fromProperties`.
    pub(crate) from_properties: Option<CompletionsFromProperties>,
    /// `fromPaths`.
    pub(crate) from_paths: Option<PathCompletions>,
}

/// `type extensionOptions struct`.
pub(crate) struct ExtensionOptions {
    /// `extensionsToSearch`.
    pub(crate) extensions_to_search: Vec<String>,
    /// `referenceKind`.
    pub(crate) reference_kind: ReferenceKind,
    /// `importingSourceFile`.
    pub(crate) importing_source_file: NodeId,
    /// `endingPreference`.
    pub(crate) ending_preference: tsc_modulespecifiers::ImportModuleSpecifierEndingPreference,
    /// `resolutionMode`.
    pub(crate) resolution_mode: tsc_core::compileroptions::ResolutionMode,
}

/// `type referenceKind int`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReferenceKind {
    /// `referenceKindFileName`.
    FileName,
    /// `referenceKindModuleSpecifier`.
    ModuleSpecifier,
}

/// `type moduleCompletionKind int`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ModuleCompletionKind {
    /// `moduleCompletionKindDirectory`.
    Directory,
    /// `moduleCompletionKindFile`.
    File,
    /// `moduleCompletionKindExternalModuleName`.
    ExternalModuleName,
}

/// `type moduleCompletionNameAndKind struct`.
#[derive(Clone)]
pub(crate) struct ModuleCompletionNameAndKind {
    /// `name`.
    pub(crate) name: String,
    /// `kind`.
    pub(crate) kind: ModuleCompletionKind,
    /// `extension`.
    pub(crate) extension: String,
}

/// `type moduleCompletionNameAndKindSet struct`.
#[derive(Default)]
pub(crate) struct ModuleCompletionNameAndKindSet {
    /// `names` — `OrderedMap` keeps deterministic iteration order (Go uses an
    /// unordered `map` and collects values).
    pub(crate) names: OrderedMap<String, ModuleCompletionNameAndKind>,
}

impl ModuleCompletionNameAndKindSet {
    /// `(s *moduleCompletionNameAndKindSet) add`.
    pub(crate) fn add(&mut self, entry: ModuleCompletionNameAndKind) {
        let replace = match self.names.get(&entry.name) {
            None => true,
            Some(existing) => existing.kind < entry.kind,
        };
        if replace {
            self.names.set(entry.name.clone(), entry);
        }
    }

    /// `slices.Collect(maps.Values(s.names))`.
    pub(crate) fn into_values(self) -> Vec<ModuleCompletionNameAndKind> {
        self.names.values().cloned().collect()
    }
}

/// `walkUpParentheses`.
fn walk_up_parentheses(node: NodeId, nodes: &[Node]) -> NodeId {
    match nodes[node].kind {
        Kind::ParenthesizedType => ast::walk_up_parenthesized_types(node, nodes).unwrap_or(node),
        Kind::ParenthesizedExpression => {
            ast::walk_up_parenthesized_expressions(node, nodes).unwrap_or(node)
        }
        _ => node,
    }
}

/// `fromContextualType`.
fn from_contextual_type(
    context_flags: ContextFlags,
    node: NodeId,
    type_checker: &mut Checker,
) -> Option<CompletionsFromTypes> {
    // Get completion for string literal from string literal type
    // i.e. var x: "hi" | "hello" = "/*completion position*/"
    to_completions_from_types(get_string_literal_types(
        utilities::get_contextual_type_from_parent(node, type_checker, context_flags),
        None,
        type_checker,
    ))
}

/// `toCompletionsFromTypes`.
fn to_completions_from_types(types: Vec<TypeId>) -> Option<CompletionsFromTypes> {
    if types.is_empty() {
        return None;
    }
    Some(CompletionsFromTypes {
        types,
        is_new_identifier: false,
    })
}

/// `toStringLiteralCompletionsFromTypes`.
fn to_string_literal_completions_from_types(
    types: Vec<TypeId>,
) -> Option<StringLiteralCompletions> {
    let result = to_completions_from_types(types)?;
    Some(StringLiteralCompletions {
        from_types: Some(result),
        ..Default::default()
    })
}

/// `getStringLiteralTypes` — `t` may be `Option` (Go `nil`) and the result
/// contains only the `TypeId`s of string literal types.
pub(crate) fn get_string_literal_types(
    t: Option<TypeId>,
    uniques: Option<&mut Set<String>>,
    type_checker: &mut Checker,
) -> Vec<TypeId> {
    let Some(t) = t else {
        return Vec::new();
    };
    let mut owned_uniques = Set::default();
    let uniques = match uniques {
        Some(u) => u,
        None => &mut owned_uniques,
    };
    let t = utilities::skip_constraint(t, type_checker);
    let t_ref = type_checker.types.get(t);
    if t_ref.is_union() {
        let element_types = t_ref.types().to_vec();
        drop(t_ref);
        let mut types = Vec::new();
        for element_type in element_types {
            types.extend(get_string_literal_types(
                Some(element_type),
                Some(&mut *uniques),
                type_checker,
            ));
        }
        return types;
    }
    if t_ref.is_string_literal() && !t_ref.is_enum_literal() {
        let value_is_new = match &t_ref.as_literal_type().value {
            Some(tsc_evaluator::Value::String(s)) => uniques.add_if_absent(s.clone()),
            _ => false,
        };
        if value_is_new {
            return vec![t];
        }
    }
    Vec::new()
}

/// `getAlreadyUsedTypesInStringLiteralUnion`.
fn get_already_used_types_in_string_literal_union(
    union: NodeId,
    current: NodeId,
    nodes: &[Node],
) -> Vec<String> {
    let Some(types_list) = nodes[union]
        .as_union_type_node()
        .union_or_intersection_type_node_base
        .types
        .clone()
    else {
        return Vec::new();
    };
    let mut values = Vec::new();
    for &type_node in &types_list.nodes {
        if type_node != current
            && ast::is_literal_type_node(&nodes[type_node])
            && nodes[type_node]
                .as_literal_type_node()
                .literal
                .is_some_and(|lit| ast::is_string_literal(&nodes[lit]))
        {
            let lit = nodes[type_node].as_literal_type_node().literal.unwrap();
            values.push(nodes[lit].text(&nodes).into_owned());
        }
    }
    values
}

/// `hasIndexSignature`.
fn has_index_signature(t: TypeId, type_checker: &mut Checker) -> bool {
    type_checker.get_string_index_type(t).is_some()
        || type_checker.get_number_index_type(t).is_some()
}

/// `isRequireCallArgument` — matches `require("`/`require("`.
fn is_require_call_argument(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node].parent;
    let Some(parent) = parent else {
        return false;
    };
    ast::is_call_expression(&nodes[parent])
        && nodes[parent]
            .arguments()
            .is_some_and(|args| !args.is_empty() && args[0] == node)
        && nodes[parent]
            .expression()
            .is_some_and(|e| ast::is_identifier(&nodes[e]) && nodes[e].text(&nodes) == "require")
}

/// `kindModifiersFromExtension`.
fn kind_modifiers_from_extension(extension: &str) -> ScriptElementKindModifier {
    match extension {
        tspath::EXTENSION_DTS => ScriptElementKindModifier::DTS,
        tspath::EXTENSION_JS => ScriptElementKindModifier::JS,
        tspath::EXTENSION_JSON => ScriptElementKindModifier::JSON,
        tspath::EXTENSION_JSX => ScriptElementKindModifier::JSX,
        tspath::EXTENSION_TS => ScriptElementKindModifier::TS,
        tspath::EXTENSION_TSX => ScriptElementKindModifier::TSX,
        tspath::EXTENSION_DMTS => ScriptElementKindModifier::DMTS,
        tspath::EXTENSION_MJS => ScriptElementKindModifier::MJS,
        tspath::EXTENSION_MTS => ScriptElementKindModifier::MTS,
        tspath::EXTENSION_DCTS => ScriptElementKindModifier::DCTS,
        tspath::EXTENSION_CJS => ScriptElementKindModifier::CJS,
        tspath::EXTENSION_CTS => ScriptElementKindModifier::CTS,
        tspath::EXTENSION_TS_BUILD_INFO => {
            panic!(
                "Extension {} is unsupported.",
                tspath::EXTENSION_TS_BUILD_INFO
            )
        }
        _ => ScriptElementKindModifier::NONE,
    }
}

/// `isAnyDirectorySeparator`.
fn is_any_directory_separator(r: char) -> bool {
    r == '/' || r == '\\'
}

/// `getDirectoryFragmentRange` — replace everything after the last directory
/// separator that appears.
fn get_directory_fragment_range(text: &str, text_start: TextPos) -> Option<TextRange> {
    let offset = match text.rfind(|c| is_any_directory_separator(c)) {
        Some(index) => index + 1,
        None => 0,
    };
    let length = text.len() - offset;
    if length == 0 {
        return None;
    }
    Some(TextRange::new(
        text_start + offset as i32,
        text_start + (offset + length) as i32,
    ))
}

/// `getFragmentDirectory`.
fn get_fragment_directory(fragment: &str) -> String {
    if !contains_slash(fragment) {
        return String::new();
    }
    if tspath::has_trailing_directory_separator(fragment) {
        return fragment.to_string();
    }
    tspath::get_directory_path(fragment).into_owned()
}

/// `containsSlash`.
fn contains_slash(fragment: &str) -> bool {
    fragment.contains(tspath::DIRECTORY_SEPARATOR)
}

/// `withoutStartAndEnd`.
fn without_start_and_end(s: &str, start: &str, end: &str) -> Option<String> {
    if s.starts_with(start) && s.ends_with(end) && s.len() >= start.len() + end.len() {
        return Some(s[start.len()..s.len() - end.len()].to_string());
    }
    None
}

/// `removeLeadingDirectorySeparator`.
fn remove_leading_directory_separator(path: &str) -> &str {
    path.trim_start_matches(tspath::DIRECTORY_SEPARATOR)
}

/// `isPathRelativeToScript` — returns true if the path is explicitly relative
/// (i.e. relative to `.` or `..`).
fn is_path_relative_to_script(path: &str) -> bool {
    path.starts_with("./") || path.starts_with("../")
}

/// `moduleResolutionUsesNodeModules`.
fn module_resolution_uses_node_modules(
    module_resolution: tsc_core::options_generated::ModuleResolutionKind,
) -> bool {
    (tsc_core::options_generated::ModuleResolutionKind::Node16 <= module_resolution
        && module_resolution <= tsc_core::options_generated::ModuleResolutionKind::NodeNext)
        || module_resolution == tsc_core::options_generated::ModuleResolutionKind::Bundler
}

/// `moduletToScriptElementKind`.
fn module_to_script_element_kind(kind: ModuleCompletionKind) -> ScriptElementKind {
    match kind {
        ModuleCompletionKind::Directory => ScriptElementKind::Directory,
        ModuleCompletionKind::File => ScriptElementKind::ScriptElement,
        ModuleCompletionKind::ExternalModuleName => ScriptElementKind::ExternalModuleName,
    }
}

/// `toPathCompletions`.
fn to_path_completions(names: Vec<ModuleCompletionNameAndKind>) -> Vec<PathCompletion> {
    names
        .into_iter()
        .map(|name_and_kind| PathCompletion {
            name: name_and_kind.name,
            kind: module_to_script_element_kind(name_and_kind.kind),
            extension: name_and_kind.extension,
        })
        .collect()
}

/// `getFileExtension`.
fn get_file_extension(file_name: &str) -> String {
    let extension = tspath::try_get_extension_from_path(file_name);
    if !extension.is_empty() {
        return extension.to_string();
    }
    tspath::get_any_extension_from_path(file_name, &[], tspath::CaseSensitivity::CaseSensitive)
        .to_string()
}

/// `tryRemoveDirectoryPrefix`.
fn try_remove_directory_prefix(
    path: &str,
    prefix: &str,
    case_sensitivity: CaseSensitivity,
) -> Option<String> {
    let (without_prefix, ok) = case_sensitivity.trim_prefix(path, prefix);
    if !ok {
        return None;
    }
    let mut without_prefix = without_prefix;
    if without_prefix.starts_with('/') || without_prefix.starts_with('\\') {
        without_prefix = &without_prefix[1..];
    }
    Some(without_prefix.to_string())
}

/// `deduplicateDirectoryNames`.
fn deduplicate_directory_names(slice: Vec<RootedDirectoryPath>) -> Vec<RootedDirectoryPath> {
    if slice.len() <= 1 {
        return slice;
    }
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::new();
    for directory in slice {
        if seen.insert(directory.clone()) {
            result.push(directory);
        }
    }
    result
}

/// `deduplicateModuleCompletions`.
fn deduplicate_module_completions(
    completions: Vec<ModuleCompletionNameAndKind>,
) -> Vec<ModuleCompletionNameAndKind> {
    if completions.len() <= 1 {
        return completions;
    }
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::new();
    for c in completions {
        let key = (c.name.clone(), c.kind as u8, c.extension.clone());
        if seen.insert(key) {
            result.push(c);
        }
    }
    result
}

/// `getBaseDirectoriesFromRootDirs` — takes a script path and returns paths
/// for all potential folders that could be merged with its containing folder
/// via the `rootDirs` compiler option.
fn get_base_directories_from_root_dirs(
    root_dirs: &[RootedDirectoryPath],
    script_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> Vec<RootedDirectoryPath> {
    // Determine the path to the directory containing the script relative to the
    // root directory it is contained within.
    let mut relative_directory: Option<RelativePath> = None;
    for root_directory in root_dirs {
        if let Some(relative) = case_sensitivity
            .relative_path_within_directory(root_directory, &script_directory.as_path())
        {
            relative_directory = Some(relative);
            break;
        }
    }

    // Now find a path for each potential directory that is to be merged with
    // the one containing the script.
    let mut directories = Vec::new();
    for root_directory in root_dirs {
        match &relative_directory {
            None => directories.push(root_directory.clone()),
            Some(relative_directory) if relative_directory.as_string().is_empty() => {
                directories.push(root_directory.clone());
            }
            Some(relative_directory) => {
                directories.push(root_directory.resolve_relative_directory(relative_directory));
            }
        }
    }
    directories.push(script_directory.clone());

    deduplicate_directory_names(directories)
}

/// `getPatternFromFirstMatchingCondition`.
fn get_pattern_from_first_matching_condition(
    target: &tsc_packagejson::ExportsOrImports,
    conditions: &[String],
) -> String {
    if target.type_ == tsc_packagejson::JSONValueType::String {
        return target.as_string().to_string();
    }
    if target.type_ == tsc_packagejson::JSONValueType::Object {
        let obj = target.as_object();
        for condition in obj.keys() {
            if condition == "default"
                || conditions.contains(condition)
                || (conditions.iter().any(|c| c == "types")
                    && tsc_module::util::is_applicable_versioned_types_key(condition))
            {
                if let Some(pattern) = obj.get(condition) {
                    return get_pattern_from_first_matching_condition(pattern, conditions);
                }
            }
        }
    }
    String::new()
}

/// `getAmbientModuleName`.
fn get_ambient_module_name(
    symbol: SymbolId,
    program: &Rc<dyn tsc_checker::checker_types::Program>,
) -> String {
    // `getNonAugmentationDeclaration` — each declaration's arena is fetched
    // from its own `file_index`.
    let declarations = program.symbols().borrow()[symbol.index()]
        .declarations
        .clone();
    for declaration in declarations {
        let nodes = program.nodes(declaration.file_index());
        if ast::is_external_module_augmentation(&nodes[declaration], &nodes)
            || ast::is_global_scope_augmentation(&nodes[declaration])
        {
            continue;
        }
        if ast::is_module_with_string_literal_name(&nodes[declaration], &nodes) {
            if let Some(name) = nodes[declaration].name() {
                return nodes[name].text(&nodes).into_owned();
            }
        }
        break;
    }
    let name = program.symbols().borrow()[symbol.index()].name.clone();
    String::from_utf8_lossy(tsc_stringutil::strip_quotes(name.as_bytes())).into_owned()
}

/// `getAmbientModuleCompletions`.
fn get_ambient_module_completions(
    fragment: &str,
    fragment_directory: &str,
    type_checker: &mut Checker,
) -> Vec<String> {
    let program = type_checker.program.clone().expect("program");
    let ambient_modules = type_checker.get_ambient_modules();
    let mut non_relative_module_names = Vec::new();
    for sym in ambient_modules {
        let module_name = get_ambient_module_name(sym, &program);
        if module_name.starts_with(fragment) && !module_name.contains('*') {
            non_relative_module_names.push(module_name);
        }
    }

    if !fragment_directory.is_empty() {
        let module_name_with_separator =
            tspath::ensure_trailing_directory_separator(fragment_directory);
        for module_name in non_relative_module_names.iter_mut() {
            *module_name = module_name
                .trim_start_matches(module_name_with_separator.as_ref())
                .to_string();
        }
    }
    non_relative_module_names
}

/// `getPossibleOriginalInputPathWithoutChangingExt`.
fn get_possible_original_input_path_without_changing_ext(
    file_path: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    output_dir: &RootedDirectoryPath,
    get_common_source_directory: impl Fn() -> RootedDirectoryPath,
) -> RootedDirectoryPath {
    if !output_dir.as_string().is_empty() {
        let Some(relative_path) =
            case_sensitivity.relative_path_from_path(output_dir, &file_path.as_path())
        else {
            return file_path.clone();
        };
        return get_common_source_directory().resolve_relative_directory(&relative_path);
    }
    file_path.clone()
}

impl LanguageService<'_> {
    /// `getStringLiteralCompletions`.
    pub(crate) fn get_string_literal_completions(
        &self,
        ctx: &Context,
        file: NodeId,
        position: TextPos,
        context_token: Option<NodeId>,
        checker: &Rc<RefCell<Checker>>,
        compiler_options: &Rc<CompilerOptions>,
        include_symbols: bool,
    ) -> Result<Option<CompletionList>, Error> {
        if self.is_in_reference_comment(file, position) {
            let completion = self.get_triple_slash_reference_completions(
                file,
                position,
                &mut checker.borrow_mut(),
            );
            return Ok(self.convert_path_completions(ctx, completion, file, position));
        }
        let is_in_string = {
            let program = self.get_program();
            let mut nodes = program.nodes_mut(file.file_index());
            utilities::is_in_string(&mut nodes, file, position, context_token)
        };
        if is_in_string {
            let Some(context_token) = context_token else {
                return Ok(None);
            };
            let is_string_literal_like = {
                let program = self.get_program();
                let nodes = program.nodes(file.file_index());
                ast::is_string_literal_like(&nodes[context_token])
            };
            if !is_string_literal_like {
                return Ok(None);
            }
            let entries = self.get_string_literal_completion_entries(
                ctx,
                file,
                context_token,
                position,
                &mut checker.borrow_mut(),
            );
            Ok(self.convert_string_literal_completions(
                ctx,
                entries,
                context_token,
                file,
                position,
                &mut checker.borrow_mut(),
                compiler_options,
                include_symbols,
            ))
        } else {
            Ok(None)
        }
    }

    /// `convertStringLiteralCompletions`.
    fn convert_string_literal_completions(
        &self,
        ctx: &Context,
        completion: Option<StringLiteralCompletions>,
        context_token: NodeId,
        file: NodeId,
        position: TextPos,
        type_checker: &mut Checker,
        options: &CompilerOptions,
        include_symbols: bool,
    ) -> Option<CompletionList> {
        let completion = completion?;

        let optional_replacement_range =
            self.create_range_from_string_literal_like_content(file, context_token, position);
        if let Some(from_paths) = completion.from_paths {
            return self.convert_path_completions(ctx, Some(from_paths), file, position);
        }
        if let Some(from_properties) = completion.from_properties {
            let data = completions::CompletionDataData {
                symbols: from_properties.symbols,
                auto_imports: Vec::new(),
                completion_kind: completions::CompletionKind::String,
                is_in_snippet_scope: false,
                property_access_to_convert: None,
                is_new_identifier_location: from_properties.has_index_signature,
                location: Some(file),
                keyword_filters: Default::default(),
                literals: Vec::new(),
                symbol_to_origin_info_map: HashMap::new(),
                symbol_to_sort_text_map: HashMap::new(),
                recommended_completion: None,
                previous_token: None,
                context_token: Some(context_token),
                jsx_initializer: Default::default(),
                inside_jsdoc_tag_type_expression: false,
                is_type_only_location: false,
                is_jsx_identifier_expected: false,
                is_right_of_open_tag: false,
                is_right_of_dot_or_question_dot: false,
                import_statement_completion: None,
                has_unresolved_auto_imports: false,
                default_commit_characters: Vec::new(),
            };
            let (_, mut items) = self
                .get_completion_entries_from_symbols(
                    ctx,
                    type_checker,
                    &data,
                    Some(context_token), /*replacementToken*/
                    position,
                    file,
                    options,
                    include_symbols,
                )
                .expect("get_completion_entries_from_symbols");
            let default_commit_characters =
                get_default_commit_characters(from_properties.has_index_signature);
            let item_defaults = self.set_item_defaults(
                ctx,
                position,
                file,
                &mut items,
                Some(&default_commit_characters),
                optional_replacement_range.as_ref(),
            );
            return Some(CompletionList {
                is_incomplete: false,
                item_defaults,
                apply_kind: Default::default(),
                items: items.into_iter().map(Some).collect(),
            });
        }
        if let Some(from_types) = completion.from_types {
            let quote_char = {
                let program = self.get_program();
                let nodes = program.nodes(file.file_index());
                if nodes[context_token].kind == Kind::NoSubstitutionTemplateLiteral {
                    tsc_printer::QuoteChar::Backtick
                } else if nodes[context_token].text(&nodes).starts_with('\'') {
                    tsc_printer::QuoteChar::SingleQuote
                } else {
                    tsc_printer::QuoteChar::DoubleQuote
                }
            };
            let mut items: Vec<CompletionItem> = Vec::with_capacity(from_types.types.len());
            let replacement_range =
                self.get_replacement_range_for_context_token(file, Some(context_token), position);
            for &t in &from_types.types {
                let value = match &type_checker.types.get(t).as_literal_type().value {
                    Some(tsc_evaluator::Value::String(s)) => s.clone(),
                    _ => continue,
                };
                let name = tsc_printer::escape_string(&value, quote_char);
                let lsp_item = self.create_lsp_completion_item(
                    ctx,
                    name,
                    "", /*insertText*/
                    "", /*filterText*/
                    completions::sort_text::LOCATION_PRIORITY.to_string(),
                    ScriptElementKind::String,
                    ScriptElementKindModifier::NONE,
                    replacement_range.as_ref(),
                    None, /*commitCharacters*/
                    None, /*labelDetails*/
                    file,
                    position,
                    false, /*isMemberCompletion*/
                    false, /*isSnippet*/
                    false, /*hasAction*/
                    false, /*preselect*/
                    "",    /*source*/
                    None,  /*autoImportEntryData*/
                    None,  /*additionalTextEdits*/
                    None,  /*detail*/
                );
                items.push(CompletionItem {
                    item: lsp_item,
                    symbol: None,
                });
            }
            let default_commit_characters =
                get_default_commit_characters(from_types.is_new_identifier);
            let item_defaults = self.set_item_defaults(
                ctx,
                position,
                file,
                &mut items,
                Some(&default_commit_characters),
                None, /*optionalReplacementSpan*/
            );
            return Some(CompletionList {
                is_incomplete: false,
                item_defaults,
                apply_kind: Default::default(),
                items: items.into_iter().map(Some).collect(),
            });
        }
        None
    }

    /// `convertPathCompletions`.
    fn convert_path_completions(
        &self,
        ctx: &Context,
        completion: Option<PathCompletions>,
        file: NodeId,
        position: TextPos,
    ) -> Option<CompletionList> {
        let completion = completion?;
        // The user may type in a path that doesn't yet exist, creating a "new
        // identifier" with respect to the collection of identifiers the server
        // is aware of.
        let is_new_identifier_location = true;
        let default_commit_characters = get_default_commit_characters(is_new_identifier_location);
        let mut items: Vec<CompletionItem> = Vec::with_capacity(completion.entries.len());
        for path_completion in &completion.entries {
            let mut detail = path_completion.name.clone();
            if !path_completion.name.ends_with(&path_completion.extension) {
                detail.push_str(&path_completion.extension);
            }
            let lsp_item = self.create_lsp_completion_item(
                ctx,
                path_completion.name.clone(),
                "", /*insertText*/
                "", /*filterText*/
                completions::sort_text::LOCATION_PRIORITY.to_string(),
                path_completion.kind,
                kind_modifiers_from_extension(&path_completion.extension),
                completion.replacement_span.as_ref(),
                None, /*commitCharacters*/
                None, /*labelDetails*/
                file,
                position,
                false, /*isMemberCompletion*/
                false, /*isSnippet*/
                false, /*hasAction*/
                false, /*preselect*/
                "",    /*source*/
                None,  /*autoImportEntryData*/
                None,  /*additionalTextEdits*/
                Some(detail),
            );
            items.push(CompletionItem {
                item: lsp_item,
                symbol: None,
            });
        }
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            None, /*optionalReplacementSpan*/
        );
        Some(CompletionList {
            is_incomplete: false,
            item_defaults,
            apply_kind: Default::default(),
            items: items.into_iter().map(Some).collect(),
        })
    }

    /// `getStringLiteralCompletionEntries` — `node` is an
    /// `*ast.StringLiteralLike`.
    fn get_string_literal_completion_entries(
        &self,
        _ctx: &Context,
        file: NodeId,
        node: NodeId,
        position: TextPos,
        type_checker: &mut Checker,
    ) -> Option<StringLiteralCompletions> {
        let program = self.get_program();
        let parent = {
            let nodes = program.nodes(node.file_index());
            walk_up_parentheses(nodes[node].parent.expect("string literal parent"), &nodes)
        };
        let parent_kind = program.nodes(parent.file_index())[parent].kind;
        match parent_kind {
            Kind::LiteralType => {
                let grandparent = {
                    let nodes = program.nodes(parent.file_index());
                    walk_up_parentheses(nodes[parent].parent.expect("grandparent"), &nodes)
                };
                if program.nodes(grandparent.file_index())[grandparent].kind == Kind::ImportType {
                    return self.get_string_literal_completions_from_module_names(
                        file,
                        node,
                        type_checker,
                    );
                }
                self.from_unionable_literal_type(grandparent, parent, position, type_checker)
            }
            Kind::PropertyAssignment => {
                let (parent_parent, parent_name) = {
                    let nodes = program.nodes(parent.file_index());
                    (nodes[parent].parent, nodes[parent].name())
                };
                let parent_parent = parent_parent?;
                if ast::is_object_literal_expression(
                    &program.nodes(parent_parent.file_index())[parent_parent],
                ) && parent_name == Some(node)
                {
                    // Get quoted name of properties of the object literal expression
                    // i.e. interface ConfigFiles {
                    //          'jspm:dev': string
                    //      }
                    //      let files: ConfigFiles = {
                    //          '/*completion position*/'
                    //      }
                    return Some(StringLiteralCompletions {
                        from_properties: string_literal_completions_for_object_literal(
                            &program,
                            type_checker,
                            parent_parent,
                        ),
                        ..Default::default()
                    });
                }
                let has_call_like_ancestor = {
                    let nodes = program.nodes(parent.file_index());
                    ast::find_ancestor(nodes[parent].parent, &nodes, &mut |n, nodes| {
                        ast::is_call_like_expression(n, nodes)
                    })
                    .is_some()
                };
                if has_call_like_ancestor {
                    let mut uniques = Set::default();
                    let contextual_type =
                        type_checker.get_contextual_type_api(node, ContextFlags::NONE);
                    let mut string_literal_types =
                        get_string_literal_types(contextual_type, Some(&mut uniques), type_checker);
                    let contextual_type_ignore = type_checker
                        .get_contextual_type_api(node, ContextFlags::IGNORE_NODE_INFERENCES);
                    string_literal_types.extend(get_string_literal_types(
                        contextual_type_ignore,
                        Some(&mut uniques),
                        type_checker,
                    ));
                    return to_string_literal_completions_from_types(string_literal_types);
                }
                Some(StringLiteralCompletions {
                    from_types: from_contextual_type(ContextFlags::NONE, node, type_checker),
                    ..Default::default()
                })
            }
            Kind::ElementAccessExpression => {
                let (expression, argument_expression) = {
                    let nodes = program.nodes(parent.file_index());
                    (
                        nodes[parent].expression(),
                        nodes[parent]
                            .as_element_access_expression()
                            .argument_expression,
                    )
                };
                let argument_is_node = argument_expression.is_some_and(|arg| {
                    ast::skip_parentheses(arg, &program.nodes(arg.file_index())) == node
                });
                if argument_is_node {
                    // Get all names of properties on the expression
                    // i.e. interface A {
                    //      'prop1': string
                    // }
                    // let a: A;
                    // a['/*completion position*/']
                    let t = type_checker.get_type_at_location(expression.expect("expression"));
                    return Some(StringLiteralCompletions {
                        from_properties: Some(string_literal_completions_from_properties(
                            t,
                            type_checker,
                        )),
                        ..Default::default()
                    });
                }
                None
            }
            Kind::CallExpression | Kind::NewExpression | Kind::JsxAttribute => {
                let (is_require, is_import_call) = {
                    let nodes = program.nodes(parent.file_index());
                    (
                        is_require_call_argument(node, &nodes),
                        ast::is_import_call(&nodes[parent], &nodes),
                    )
                };
                if !is_require && !is_import_call {
                    let argument_node = if parent_kind == Kind::JsxAttribute {
                        nodes_parent(&program, parent)?
                    } else {
                        node
                    };
                    let argument_info = {
                        let mut nodes = program.nodes_mut(file.file_index());
                        completions::get_argument_info_for_completions(
                            &mut nodes,
                            argument_node,
                            position,
                            file,
                            type_checker,
                        )
                    };
                    // Get string literal completions from specialized signatures
                    // of the target
                    // i.e. declare function f(a: 'A');
                    // f("/*completion position*/")
                    let argument_info = argument_info?;

                    let result = get_string_literal_completions_from_signature(
                        argument_info.invocation,
                        node,
                        &argument_info,
                        type_checker,
                    );
                    if result.is_some() {
                        return Some(StringLiteralCompletions {
                            from_types: result,
                            ..Default::default()
                        });
                    }
                    return Some(StringLiteralCompletions {
                        from_types: from_contextual_type(ContextFlags::NONE, node, type_checker),
                        ..Default::default()
                    });
                }
                // fallthrough — is `require("")` or `import("")`
                self.get_string_literal_completions_from_module_names(file, node, type_checker)
            }
            Kind::ImportDeclaration
            | Kind::ExportDeclaration
            | Kind::ExternalModuleReference
            | Kind::JSDocImportTag => {
                // Get all known external module names or complete a path to a module
                // i.e. import * as ns from "/*completion position*/";
                //      var y = import("/*completion position*/");
                //      import x = require("/*completion position*/");
                //      var y = require("/*completion position*/");
                //      export * from "/*completion position*/";
                self.get_string_literal_completions_from_module_names(file, node, type_checker)
            }
            Kind::CaseClause => {
                let clauses = {
                    let nodes = program.nodes(parent.file_index());
                    nodes[nodes[parent].parent.expect("case block")]
                        .as_case_block()
                        .clauses
                        .as_ref()
                        .map(|c| c.nodes.to_vec())
                        .unwrap_or_default()
                };
                let tracker = utilities::new_case_clause_tracker(type_checker, &clauses);
                let contextual_types =
                    from_contextual_type(ContextFlags::IGNORE_NODE_INFERENCES, node, type_checker)?;
                let literals: Vec<TypeId> = contextual_types
                    .types
                    .into_iter()
                    .filter(|&t| {
                        let value_is_used = {
                            let t_ref = type_checker.types.get(t);
                            match &t_ref.as_literal_type().value {
                                Some(tsc_evaluator::Value::String(s)) => {
                                    tracker.has_value(utilities::TrackerHasValue::Str(s.clone()))
                                }
                                Some(tsc_evaluator::Value::Number(n)) => {
                                    tracker.has_value(utilities::TrackerHasValue::Number(n.clone()))
                                }
                                Some(tsc_evaluator::Value::PseudoBigInt(b)) => tracker
                                    .has_value(utilities::TrackerHasValue::PseudoBigInt(b.clone())),
                                _ => false,
                            }
                        };
                        !value_is_used
                    })
                    .collect();
                Some(StringLiteralCompletions {
                    from_types: Some(CompletionsFromTypes {
                        types: literals,
                        is_new_identifier: false,
                    }),
                    ..Default::default()
                })
            }
            Kind::ImportSpecifier | Kind::ExportSpecifier => {
                // Complete string aliases in `import { "|" } from` and
                // `export { "|" } from`
                let specifier = parent;
                let (property_name, specifier_parent) = {
                    let nodes = program.nodes(specifier.file_index());
                    (nodes[specifier].property_name(), nodes[specifier].parent)
                };
                if let Some(property_name) = property_name {
                    if node != property_name {
                        return None; // Don't complete in `export { "..." as "|" } from`
                    }
                }
                let named_imports_or_exports = specifier_parent?;
                let named_kind = program.nodes(named_imports_or_exports.file_index())
                    [named_imports_or_exports]
                    .kind;
                let module_specifier = {
                    let nodes = program.nodes(named_imports_or_exports.file_index());
                    if named_kind == Kind::NamedImports {
                        nodes[nodes[named_imports_or_exports]
                            .parent
                            .expect("import clause")]
                        .parent
                    } else {
                        nodes[named_imports_or_exports].parent
                    }
                };
                let module_specifier = module_specifier?;
                let module_specifier_symbol =
                    type_checker.get_symbol_at_location_api(module_specifier)?;
                let exports =
                    type_checker.get_exports_and_properties_of_module(module_specifier_symbol);
                let existing: Set<String> = {
                    let nodes = program.nodes(named_imports_or_exports.file_index());
                    let mut set = Set::default();
                    if let Some(elements) = nodes[named_imports_or_exports].elements() {
                        for &n in elements {
                            if let Some(name_node) = nodes[n].property_name_or_name() {
                                set.add(nodes[name_node].text(&nodes).into_owned());
                            }
                        }
                    }
                    set
                };
                let symbols = program.symbols.borrow();
                let uniques: Vec<SymbolId> = exports
                    .into_iter()
                    .filter(|&e| {
                        symbols[e.index()].name.as_str()
                            != ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
                            && !existing.has(&symbols[e.index()].name)
                    })
                    .collect();
                drop(symbols);
                Some(StringLiteralCompletions {
                    from_properties: Some(CompletionsFromProperties {
                        symbols: uniques,
                        has_index_signature: false,
                    }),
                    ..Default::default()
                })
            }
            Kind::BinaryExpression => {
                let (operator_kind, right) = {
                    let nodes = program.nodes(parent.file_index());
                    let bin = nodes[parent].as_binary_expression();
                    (bin.operator_token.map(|t| nodes[t].kind), bin.right)
                };
                if operator_kind == Some(Kind::InKeyword) {
                    let t = type_checker.get_type_at_location(right.expect("binary right"));
                    let properties = completions::get_properties_for_completion(t, type_checker);
                    let filtered: Vec<SymbolId> = properties
                        .into_iter()
                        .filter(|&s| {
                            let value_declaration =
                                program.symbols.borrow()[s.index()].value_declaration;
                            value_declaration.is_none_or(|d| {
                                let nodes = program.arena_of(d);
                                !ast::is_private_identifier_class_element_declaration(
                                    &nodes[d], &nodes,
                                )
                            })
                        })
                        .collect();
                    return Some(StringLiteralCompletions {
                        from_properties: Some(CompletionsFromProperties {
                            symbols: filtered,
                            has_index_signature: false,
                        }),
                        ..Default::default()
                    });
                }
                Some(StringLiteralCompletions {
                    from_types: from_contextual_type(ContextFlags::NONE, node, type_checker),
                    ..Default::default()
                })
            }
            _ => {
                let result =
                    from_contextual_type(ContextFlags::IGNORE_NODE_INFERENCES, node, type_checker);
                if result.is_some() {
                    return Some(StringLiteralCompletions {
                        from_types: result,
                        ..Default::default()
                    });
                }
                Some(StringLiteralCompletions {
                    from_types: from_contextual_type(ContextFlags::NONE, node, type_checker),
                    ..Default::default()
                })
            }
        }
    }

    /// `fromUnionableLiteralType`.
    fn from_unionable_literal_type(
        &self,
        grandparent: NodeId,
        parent: NodeId,
        position: TextPos,
        type_checker: &mut Checker,
    ) -> Option<StringLiteralCompletions> {
        let program = self.get_program();
        match program.nodes(grandparent.file_index())[grandparent].kind {
            Kind::CallExpression
            | Kind::ExpressionWithTypeArguments
            | Kind::JsxOpeningElement
            | Kind::JsxSelfClosingElement
            | Kind::NewExpression
            | Kind::TaggedTemplateExpression
            | Kind::TypeReference => {
                let type_argument = {
                    let nodes = program.nodes(parent.file_index());
                    ast::find_ancestor(Some(parent), &nodes, &mut |n, _| {
                        n.parent == Some(grandparent)
                    })
                };
                if let Some(type_argument) = type_argument {
                    let t = type_checker.get_type_argument_constraint_api(type_argument);
                    return Some(StringLiteralCompletions {
                        from_types: Some(CompletionsFromTypes {
                            types: get_string_literal_types(t, None, type_checker),
                            is_new_identifier: false,
                        }),
                        ..Default::default()
                    });
                }
                None
            }
            Kind::IndexedAccessType => {
                // Get all apparent property names
                // i.e. interface Foo {
                //          foo: string;
                //          bar: string;
                //      }
                //      let x: Foo["/*completion position*/"]
                let (index_type, object_type) = {
                    let nodes = program.nodes(grandparent.file_index());
                    let iat = nodes[grandparent].as_indexed_access_type_node();
                    (iat.index_type, iat.object_type)
                };
                let index_type = index_type?;
                if !program.nodes(index_type.file_index())[index_type]
                    .loc
                    .contains_inclusive(position)
                {
                    return None;
                }
                let t = type_checker.get_type_from_type_node(object_type.expect("object type"));
                Some(StringLiteralCompletions {
                    from_properties: Some(string_literal_completions_from_properties(
                        t,
                        type_checker,
                    )),
                    ..Default::default()
                })
            }
            Kind::UnionType => {
                let grandparent_parent = {
                    let nodes = program.nodes(grandparent.file_index());
                    walk_up_parentheses(nodes[grandparent].parent.expect("union parent"), &nodes)
                };
                let result = self.from_unionable_literal_type(
                    grandparent_parent,
                    parent,
                    position,
                    type_checker,
                )?;
                let already_used_types = {
                    let nodes = program.nodes(grandparent.file_index());
                    get_already_used_types_in_string_literal_union(grandparent, parent, &nodes)
                };
                if let Some(from_properties) = result.from_properties {
                    let symbols = program.symbols.borrow();
                    return Some(StringLiteralCompletions {
                        from_properties: Some(CompletionsFromProperties {
                            symbols: from_properties
                                .symbols
                                .into_iter()
                                .filter(|s| !already_used_types.contains(&symbols[s.index()].name))
                                .collect(),
                            has_index_signature: from_properties.has_index_signature,
                        }),
                        ..Default::default()
                    });
                }
                if let Some(from_types) = result.from_types {
                    let mut literals = Vec::new();
                    for t in from_types.types {
                        let value = {
                            let t_ref = type_checker.types.get(t);
                            match &t_ref.as_literal_type().value {
                                Some(tsc_evaluator::Value::String(s)) => s.clone(),
                                _ => continue,
                            }
                        };
                        if !already_used_types.contains(&value) {
                            literals.push(t);
                        }
                    }
                    return Some(StringLiteralCompletions {
                        from_types: Some(CompletionsFromTypes {
                            types: literals,
                            is_new_identifier: false,
                        }),
                        ..Default::default()
                    });
                }
                None
            }
            Kind::PropertySignature => Some(StringLiteralCompletions {
                from_types: Some(CompletionsFromTypes {
                    types: get_string_literal_types(
                        completions::get_constraint_of_type_argument_property(
                            &program,
                            Some(grandparent),
                            type_checker,
                        ),
                        None,
                        type_checker,
                    ),
                    is_new_identifier: false,
                }),
                ..Default::default()
            }),
            _ => None,
        }
    }

    /// `getStringLiteralCompletionsFromModuleNames`.
    fn get_string_literal_completions_from_module_names(
        &self,
        file: NodeId,
        node: NodeId,
        type_checker: &mut Checker,
    ) -> Option<StringLiteralCompletions> {
        let program = self.get_program();
        let (text_start, node_text) = {
            let mut nodes = program.nodes_mut(file.file_index());
            let start = tsc_astnav::tokens::get_start_of_node(&mut nodes, file, node, false) + 1;
            (start, nodes[node].text(&nodes).into_owned())
        };
        let replacement_span = self.path_completion_replacement_span(
            file,
            get_directory_fragment_range(&node_text, text_start),
        )?;

        let name_and_kinds = self.get_string_literal_completions_from_module_names_worker(
            file,
            node,
            &node_text,
            type_checker,
        );
        Some(StringLiteralCompletions {
            from_paths: Some(PathCompletions {
                entries: to_path_completions(name_and_kinds),
                replacement_span,
            }),
            ..Default::default()
        })
    }

    /// `pathCompletionReplacementSpan` — returns `Ok(Some(range))` for Go's
    /// `(range, true)`, `Ok(None)` for `(nil, true)` and `None` for `(_, false)`.
    fn path_completion_replacement_span(
        &self,
        file: NodeId,
        text_range: Option<TextRange>,
    ) -> Option<Option<lsproto::Range>> {
        let text_range = text_range?;
        let (lsp_range, fidelity) =
            self.create_lsp_range_from_bounds(text_range.pos(), text_range.end(), file);
        if !fidelity.is_exact() {
            return None;
        }
        Some(Some(lsp_range))
    }

    /// `getStringLiteralCompletionsFromModuleNamesWorker` — `literal_value`
    /// is `tspath.NormalizeSlashes(node.Text())`.
    fn get_string_literal_completions_from_module_names_worker(
        &self,
        file: NodeId,
        node: NodeId,
        node_text: &str,
        checker: &mut Checker,
    ) -> Vec<ModuleCompletionNameAndKind> {
        let program = self.get_program();
        let literal_value = tspath::normalize_slashes(node_text).into_owned();
        let mut mode = tsc_core::compileroptions::RESOLUTION_MODE_NONE;
        let is_string_literal_like = {
            let nodes = program.nodes(node.file_index());
            ast::is_string_literal_like(&nodes[node])
        };
        if is_string_literal_like {
            mode = program.get_mode_for_usage_location(&program.file_has_file_name(file), node);
        }

        let (script_path, script_directory) = {
            let nodes = program.nodes(file.file_index());
            let source_file = nodes[file].as_source_file();
            (
                source_file.path_key().clone(),
                source_file.file_name().directory(),
            )
        };
        let options = program.options();
        let extension_options = self.get_extension_options(
            &options,
            ReferenceKind::ModuleSpecifier,
            file,
            mode,
            Some(&mut *checker),
        );

        if is_path_relative_to_script(&literal_value)
            || (options.paths.as_ref().is_none_or(|p| p.size() == 0)
                && (tspath::is_rooted_disk_path(&literal_value) || tspath::is_url(&literal_value)))
        {
            self.get_completion_entries_for_relative_modules(
                &literal_value,
                &script_directory,
                &script_path,
                &extension_options,
            )
        } else {
            self.get_completion_entries_for_non_relative_modules(
                &literal_value,
                &script_directory,
                mode,
                checker,
                &extension_options,
            )
        }
    }

    /// `getCompletionEntriesForNonRelativeModules`.
    ///
    /// Check all of the declared modules and those in node modules. Possible
    /// sources of modules:
    ///   - Modules that are found by the type checker
    ///   - Modules found via patterns from "paths" compiler option
    ///   - Modules from node_modules (i.e. those listed in package.json)
    ///     This includes all files that are found in node_modules/moduleName/
    ///     with acceptable file extensions
    fn get_completion_entries_for_non_relative_modules(
        &self,
        fragment: &str,
        script_directory: &RootedDirectoryPath,
        mode: tsc_core::compileroptions::ResolutionMode,
        type_checker: &mut Checker,
        extension_options: &ExtensionOptions,
    ) -> Vec<ModuleCompletionNameAndKind> {
        let program = self.get_program();
        let compiler_options = program.options();
        let paths = compiler_options.paths.clone();

        let mut result = ModuleCompletionNameAndKindSet::default();
        let module_resolution = compiler_options.get_module_resolution_kind();

        if let Some(paths) = &paths {
            if paths.size() > 0 {
                let absolute = compiler_options.get_paths_base_path(&program.base_directory());
                self.add_completion_entries_from_paths(
                    &mut result,
                    fragment,
                    &absolute,
                    extension_options,
                    paths,
                );
            }
        }

        let fragment_directory = get_fragment_directory(fragment);
        for ambient_name in
            get_ambient_module_completions(fragment, &fragment_directory, type_checker)
        {
            result.add(ModuleCompletionNameAndKind {
                name: ambient_name,
                kind: ModuleCompletionKind::ExternalModuleName,
                extension: String::new(),
            });
        }

        self.get_completion_entries_from_typings(
            script_directory,
            &fragment_directory,
            extension_options,
            &mut result,
        );

        if module_resolution_uses_node_modules(module_resolution) {
            // If looking for a global package name, don't just include
            // everything in `node_modules` because that includes dependencies'
            // own dependencies.
            // (But do if we didn't find anything, e.g. 'package.json' missing.)
            let mut found_global = false;
            if fragment_directory.is_empty() {
                for module_name in self.enumerate_node_modules_visible_to_script(script_directory) {
                    let module_result = ModuleCompletionNameAndKind {
                        name: module_name,
                        kind: ModuleCompletionKind::ExternalModuleName,
                        extension: String::new(),
                    };
                    if result.names.get(&module_result.name).is_none() {
                        found_global = true;
                        result.add(module_result);
                    }
                }
            }
            if !found_global {
                let resolve_package_json_exports =
                    compiler_options.get_resolve_package_json_exports();
                let resolve_package_json_imports =
                    compiler_options.get_resolve_package_json_imports();
                let mut seen_package_scope = false;
                let conditions = tsc_module::resolver::get_conditions(&compiler_options, mode);

                // Returns true if the search should stop.
                let exports_or_imports_lookup =
                    |result: &mut ModuleCompletionNameAndKindSet,
                     lookup_table: &tsc_packagejson::ExportsOrImports,
                     fragment: &str,
                     base_directory: &RootedDirectoryPath,
                     is_exports: bool,
                     is_imports: bool|
                     -> bool {
                        if lookup_table.type_ != tsc_packagejson::JSONValueType::Object {
                            return lookup_table.type_
                                != tsc_packagejson::JSONValueType::NotPresent;
                        }
                        let keys: Vec<String> = lookup_table.as_object().keys().cloned().collect();
                        self.add_completion_entries_from_paths_or_exports_or_imports(
                            result,
                            is_exports,
                            is_imports,
                            fragment,
                            base_directory,
                            extension_options,
                            keys,
                            &|key: &str| {
                                let Some(key_value) = lookup_table.as_object().get(key) else {
                                    return Vec::new();
                                };
                                let pattern = get_pattern_from_first_matching_condition(
                                    key_value,
                                    &conditions,
                                );
                                if pattern.is_empty() {
                                    return Vec::new();
                                }
                                if key.ends_with('/') && pattern.ends_with('/') {
                                    return vec![format!("{pattern}*")];
                                }
                                vec![pattern]
                            },
                            &compare_pattern_keys_comparison,
                        )
                    };

                // `importsLookup(directory)` and `ancestorLookup(ancestor)` —
                // closures over `seen_package_scope` need `FnMut` borrows, so
                // implement them inline.
                let ancestor_lookup =
                    |result: &mut ModuleCompletionNameAndKindSet,
                     ancestor: &RootedDirectoryPath,
                     seen_package_scope: &mut bool| {
                        let node_modules = ancestor.resolve_directory("node_modules");
                        if self.directory_exists(&node_modules) {
                            self.get_completion_entries_for_directory_fragment(
                                fragment,
                                &node_modules,
                                extension_options,
                                false, /* moduleSpecifierIsRelative */
                                None,  /* exclude */
                                result,
                            );
                        }
                        if resolve_package_json_imports && !*seen_package_scope {
                            let package_json_info = program
                                .get_package_json_info(&ancestor.resolve_file("package.json"));
                            if package_json_info.as_ref().is_some_and(|info| info.exists()) {
                                *seen_package_scope = true;
                                if let Some(info) = &package_json_info {
                                    if let Some(contents) = &info.contents {
                                        exports_or_imports_lookup(
                                            result,
                                            &contents.imports,
                                            fragment,
                                            ancestor,
                                            false, /*isExports*/
                                            true,  /*isImports*/
                                        );
                                    }
                                }
                            }
                        }
                    };

                let global_cache_location = program.get_global_typings_cache_location();
                let mut ancestor_lookup_fn =
                    |result: &mut ModuleCompletionNameAndKindSet,
                     ancestor: &RootedDirectoryPath,
                     seen_package_scope: &mut bool| {
                        if !fragment_directory.is_empty() && resolve_package_json_exports {
                            let components = tspath::get_path_components(fragment);
                            let mut components = &components[1..]; // shift off empty root
                            if components.is_empty() {
                                ancestor_lookup(result, ancestor, seen_package_scope);
                                return;
                            }
                            let mut package_path = components[0].clone();
                            components = &components[1..];
                            if package_path.starts_with('@') {
                                if components.is_empty() {
                                    ancestor_lookup(result, ancestor, seen_package_scope);
                                    return;
                                }
                                let sub_name = components[0].clone();
                                components = &components[1..];
                                package_path = tspath::combine_paths(&package_path, &[&sub_name]);
                            }
                            if resolve_package_json_imports && package_path.starts_with('#') {
                                if !*seen_package_scope {
                                    let package_json_info = program.get_package_json_info(
                                        &ancestor.resolve_file("package.json"),
                                    );
                                    if package_json_info.as_ref().is_some_and(|info| info.exists())
                                    {
                                        *seen_package_scope = true;
                                        if let Some(info) = &package_json_info {
                                            if let Some(contents) = &info.contents {
                                                exports_or_imports_lookup(
                                                    result,
                                                    &contents.imports,
                                                    fragment,
                                                    ancestor,
                                                    false, /*isExports*/
                                                    true,  /*isImports*/
                                                );
                                            }
                                        }
                                    }
                                }
                                return;
                            }
                            let package_directory = ancestor.resolve_directory(
                                &tspath::combine_paths("node_modules", &[&package_path]),
                            );
                            let package_json_info = program.get_package_json_info(
                                &package_directory.resolve_file("package.json"),
                            );
                            if package_json_info.as_ref().is_some_and(|info| info.exists()) {
                                let mut fragment_subpath = components.join("/");
                                if !components.is_empty()
                                    && tspath::has_trailing_directory_separator(fragment)
                                {
                                    fragment_subpath.push('/');
                                }
                                if let Some(info) = &package_json_info {
                                    if let Some(contents) = &info.contents {
                                        if exports_or_imports_lookup(
                                            result,
                                            &contents.exports,
                                            &fragment_subpath,
                                            &package_directory,
                                            true,  /*isExports*/
                                            false, /*isImports*/
                                        ) {
                                            return;
                                        }
                                    }
                                }
                            }
                        }
                        ancestor_lookup(result, ancestor, seen_package_scope);
                    };

                tspath::for_each_ancestor_directory_path_stopping_at_global_cache(
                    &global_cache_location,
                    script_directory,
                    |directory| {
                        ancestor_lookup_fn(&mut result, directory, &mut seen_package_scope);
                        ((), false)
                    },
                );
            }
        }

        result.into_values()
    }

    /// `getCompletionEntriesFromTypings`.
    fn get_completion_entries_from_typings(
        &self,
        script_directory: &RootedDirectoryPath,
        fragment_directory: &str,
        extension_options: &ExtensionOptions,
        result: &mut ModuleCompletionNameAndKindSet,
    ) {
        let program = self.get_program();
        let options = program.options();
        let mut seen = std::collections::HashMap::new();

        let (type_roots, _) = options.get_effective_type_roots(&program.base_directory());

        for root in type_roots.unwrap_or_default() {
            self.get_completion_entries_from_typings_directories(
                &root,
                &options,
                fragment_directory,
                extension_options,
                &mut seen,
                result,
            );
        }

        let global_cache_location = program.get_global_typings_cache_location();
        tspath::for_each_ancestor_directory_path_stopping_at_global_cache(
            &global_cache_location,
            script_directory,
            |directory| {
                let types_dir = directory.resolve_directory("node_modules/@types");
                self.get_completion_entries_from_typings_directories(
                    &types_dir,
                    &options,
                    fragment_directory,
                    extension_options,
                    &mut seen,
                    result,
                );
                ((), false)
            },
        );
    }

    /// `getCompletionEntriesFromTypingsDirectories`.
    fn get_completion_entries_from_typings_directories(
        &self,
        directory: &RootedDirectoryPath,
        options: &CompilerOptions,
        fragment_directory: &str,
        extension_options: &ExtensionOptions,
        seen: &mut std::collections::HashMap<String, bool>,
        result: &mut ModuleCompletionNameAndKindSet,
    ) {
        let program = self.get_program();
        if !self.directory_exists(directory) {
            return;
        }

        for type_directory_name in self.get_directories(directory) {
            let package_name = tsc_module::util::unmangle_scoped_package_name(&type_directory_name);
            if let Some(types) = &options.types {
                if !types.is_empty() && !types.contains(&package_name) {
                    continue;
                }
            }

            if fragment_directory.is_empty() {
                if !seen.get(&package_name).copied().unwrap_or(false) {
                    result.add(ModuleCompletionNameAndKind {
                        name: package_name.clone(),
                        kind: ModuleCompletionKind::ExternalModuleName,
                        extension: String::new(),
                    });
                    seen.insert(package_name, true);
                }
            } else {
                let base_directory = directory.resolve_directory(&type_directory_name);
                let remaining_fragment = try_remove_directory_prefix(
                    fragment_directory,
                    &package_name,
                    program.case_sensitivity(),
                );
                if let Some(remaining_fragment) = remaining_fragment {
                    self.get_completion_entries_for_directory_fragment(
                        &remaining_fragment,
                        &base_directory,
                        extension_options,
                        false,
                        None,
                        result,
                    );
                }
            }
        }
    }

    /// `enumerateNodeModulesVisibleToScript`.
    fn enumerate_node_modules_visible_to_script(
        &self,
        script_directory: &RootedDirectoryPath,
    ) -> Vec<String> {
        let program = self.get_program();
        let mut result = Vec::new();
        let global_cache_location = program.get_global_typings_cache_location();

        tspath::for_each_ancestor_directory_path_stopping_at_global_cache(
            &global_cache_location,
            script_directory,
            |directory| {
                let package_json_path = directory.resolve_file("package.json");
                let package_json_info = program.get_package_json_info(&package_json_path);
                if let Some(info) = package_json_info {
                    if info.exists() {
                        if let Some(contents) = &info.contents {
                            contents.range_dependencies(|name, _version, _field| {
                                if !name.starts_with("@types/") {
                                    result.push(name.to_string());
                                }
                                true
                            });
                        }
                    }
                }
                ((), false)
            },
        );

        result
    }

    /// `getExtensionOptions`.
    fn get_extension_options(
        &self,
        options: &CompilerOptions,
        reference_kind: ReferenceKind,
        file: NodeId,
        mode: tsc_core::compileroptions::ResolutionMode,
        checker: Option<&mut Checker>,
    ) -> ExtensionOptions {
        let program = self.get_program();
        let extensions_to_search = get_supported_extensions_for_module_resolution(
            options,
            program.command_line().content_mapper_extensions(),
            checker,
        );

        ExtensionOptions {
            extensions_to_search,
            reference_kind,
            importing_source_file: file,
            ending_preference: self.user_preferences().import_module_specifier_ending,
            resolution_mode: mode,
        }
    }

    /// `getCompletionEntriesForRelativeModules`.
    fn get_completion_entries_for_relative_modules(
        &self,
        literal_value: &str,
        script_directory: &RootedDirectoryPath,
        script_path: &PathKey,
        extension_options: &ExtensionOptions,
    ) -> Vec<ModuleCompletionNameAndKind> {
        let program = self.get_program();
        let options = program.options();
        if options.root_dirs.as_ref().is_some_and(|r| !r.is_empty()) {
            self.get_completion_entries_for_directory_fragment_with_root_dirs(
                literal_value,
                script_directory,
                script_path,
                extension_options,
            )
        } else {
            let mut result = ModuleCompletionNameAndKindSet::default();
            self.get_completion_entries_for_directory_fragment(
                literal_value,
                script_directory,
                extension_options,
                true, /*moduleSpecifierIsRelative*/
                Some(script_path),
                &mut result,
            );
            result.into_values()
        }
    }

    /// `getCompletionEntriesForDirectoryFragmentWithRootDirs`.
    fn get_completion_entries_for_directory_fragment_with_root_dirs(
        &self,
        fragment: &str,
        script_directory: &RootedDirectoryPath,
        exclude: &PathKey,
        extension_options: &ExtensionOptions,
    ) -> Vec<ModuleCompletionNameAndKind> {
        let program = self.get_program();
        let options = program.options();
        let base_directories = get_base_directories_from_root_dirs(
            &options.get_effective_root_dirs().unwrap_or_default(),
            script_directory,
            program.case_sensitivity(),
        );

        let mut all_completions = Vec::new();
        for base_directory in &base_directories {
            let mut result = ModuleCompletionNameAndKindSet::default();
            self.get_completion_entries_for_directory_fragment(
                fragment,
                base_directory,
                extension_options,
                true, /*moduleSpecifierIsRelative*/
                Some(exclude),
                &mut result,
            );
            all_completions.extend(result.into_values());
        }

        // Deduplicate based on name, kind, and extension
        deduplicate_module_completions(all_completions)
    }

    /// `getCompletionEntriesForDirectoryFragment` — given a path ending at a
    /// directory, gets the completions for the path.
    fn get_completion_entries_for_directory_fragment(
        &self,
        fragment: &str,
        script_directory: &RootedDirectoryPath,
        extension_options: &ExtensionOptions,
        module_specifier_is_relative: bool,
        exclude: Option<&PathKey>,
        result: &mut ModuleCompletionNameAndKindSet,
    ) {
        let program = self.get_program();
        let mut fragment = tspath::normalize_slashes(fragment).into_owned();

        // Remove the basename from the path.
        // We don't use the basename to filter completions: the client is
        // responsible for that filtering.
        if !tspath::has_trailing_directory_separator(&fragment) {
            fragment = tspath::get_directory_path(&fragment).into_owned();
        }

        if fragment.is_empty() {
            fragment = ".".to_string();
        }

        fragment = tspath::ensure_trailing_directory_separator(&fragment).into_owned();

        let base_directory = script_directory.resolve_directory(&fragment);
        if !module_specifier_is_relative {
            // Check for a version redirect.
            let package_json_directory =
                program.get_nearest_ancestor_directory_with_package_json(&base_directory);
            if !package_json_directory.as_string().is_empty() {
                let package_json_path = package_json_directory.resolve_file("package.json");
                let package_json_info = program.get_package_json_info(&package_json_path);
                if let Some(info) = package_json_info {
                    if let Some(contents) = &info.contents {
                        if contents.types_versions.type_ == tsc_packagejson::JSONValueType::Object {
                            let mut version_paths = contents.get_version_paths(None);
                            if let Some(paths) = version_paths.get_paths() {
                                if paths.size() > 0 {
                                    let Some(path_in_package) = base_directory
                                        .as_path()
                                        .relative_to(&package_json_directory)
                                    else {
                                        panic!(
                                            "package json directory must be an ancestor of the completion directory"
                                        );
                                    };
                                    let path_in_package = if path_in_package.as_string().is_empty()
                                    {
                                        path_in_package
                                    } else {
                                        path_in_package.with_trailing_directory_separator()
                                    };
                                    if self.add_completion_entries_from_relative_path_patterns(
                                        result,
                                        &path_in_package,
                                        &package_json_directory,
                                        extension_options,
                                        paths,
                                    ) {
                                        // One of the `versionPaths` was matched, which will
                                        // block relative resolution to files and folders from
                                        // here.
                                        // All reachable paths given the pattern match are
                                        // already added.
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        if !self.directory_exists(&base_directory) {
            return;
        }

        // Enumerate all available files.
        let extensions: Vec<&str> = extension_options
            .extensions_to_search
            .iter()
            .map(|s| s.as_str())
            .collect();
        let files = self.read_directory(&base_directory, &extensions, &["./*"]);

        for file_path in files {
            if exclude == Some(&program.path_key_for_file_name(&file_path)) {
                continue; // Avoid self-imports
            }

            let (name, extension) = self.get_filename_with_extension_option(
                file_path.base_name(),
                extension_options,
                false, /*isExportsOrImportsWildcard*/
            );
            result.add(ModuleCompletionNameAndKind {
                name,
                kind: ModuleCompletionKind::File,
                extension,
            });
        }

        // Get folder completion as well.
        let directories = self.get_directories(&base_directory);

        for directory in directories {
            let directory_name = tspath::get_base_file_name(&directory);
            if directory_name != "@types" {
                result.add(ModuleCompletionNameAndKind {
                    name: directory_name.into_owned(),
                    kind: ModuleCompletionKind::Directory,
                    extension: String::new(),
                });
            }
        }
    }

    /// `addCompletionEntriesFromRelativePathPatterns` — returns true if
    /// `fragment` was a match for any `paths` (which should indicate whether
    /// any other path completions should be offered).
    fn add_completion_entries_from_relative_path_patterns(
        &self,
        result: &mut ModuleCompletionNameAndKindSet,
        fragment: &RelativePath,
        base_directory: &RootedDirectoryPath,
        extension_options: &ExtensionOptions,
        paths: &OrderedMap<String, Vec<String>>,
    ) -> bool {
        self.add_completion_entries_from_paths_or_exports_or_imports(
            result,
            false, /*isExports*/
            false, /*isImports*/
            fragment.as_string(),
            base_directory,
            extension_options,
            paths.keys().cloned().collect(),
            &|key: &str| paths.get_or_zero(key),
            &compare_paths_default,
        )
    }

    /// `addCompletionEntriesFromPaths` — returns true if `fragment` was a
    /// match for any `paths`.
    fn add_completion_entries_from_paths(
        &self,
        result: &mut ModuleCompletionNameAndKindSet,
        fragment: &str,
        base_directory: &RootedDirectoryPath,
        extension_options: &ExtensionOptions,
        paths: &OrderedMap<String, Option<Vec<String>>>,
    ) -> bool {
        self.add_completion_entries_from_paths_or_exports_or_imports(
            result,
            false, /*isExports*/
            false, /*isImports*/
            fragment,
            base_directory,
            extension_options,
            paths.keys().cloned().collect(),
            &|key: &str| paths.get_or_zero(key).unwrap_or_default(),
            &compare_paths_default,
        )
    }

    /// `addCompletionEntriesFromPathsOrExportsOrImports` — returns true if
    /// `fragment` was a match for any `paths`.
    fn add_completion_entries_from_paths_or_exports_or_imports(
        &self,
        result: &mut ModuleCompletionNameAndKindSet,
        is_exports: bool,
        is_imports: bool,
        fragment: &str,
        base_directory: &RootedDirectoryPath,
        extension_options: &ExtensionOptions,
        keys: Vec<String>,
        get_patterns_for_key: &dyn Fn(&str) -> Vec<String>,
        compare_paths: &dyn Fn(&str, &str) -> tsc_stringutil::Comparison,
    ) -> bool {
        struct PathResult {
            results: Vec<ModuleCompletionNameAndKind>,
            matched: bool,
        }
        let mut path_results: Vec<PathResult> = Vec::new();
        let mut matched_path: Option<String> = None;
        for key in keys {
            if key == "." {
                continue;
            }
            let mut normalized_key = key.trim_start_matches("./").to_string(); // Remove leading "./"
            if (is_exports || is_imports) && key.ends_with('/') {
                // Normalize trailing "/" to "/*"
                normalized_key.push('*');
            }
            let patterns = get_patterns_for_key(&key);
            if !patterns.is_empty() {
                let path_pattern = tsc_core::pattern::try_parse_pattern(&normalized_key);
                if !path_pattern.is_valid() {
                    continue;
                }
                let is_match = path_pattern.matches(fragment);
                let mut is_longest_match = false;
                if is_match {
                    if matched_path.is_none() {
                        is_longest_match = true;
                    } else {
                        is_longest_match =
                            compare_paths(&normalized_key, matched_path.as_ref().unwrap())
                                == tsc_stringutil::COMPARISON_LESS_THAN;
                    }
                }
                if is_longest_match {
                    // If this is a higher priority match than anything we've
                    // seen so far, previous results from matches are invalid.
                    matched_path = Some(normalized_key.clone());
                    path_results.retain(|pr| !pr.matched);
                }
                if path_pattern.star_index == -1
                    || matched_path.is_none()
                    || compare_paths(&normalized_key, matched_path.as_ref().unwrap())
                        != tsc_stringutil::COMPARISON_GREATER_THAN
                {
                    path_results.push(PathResult {
                        matched: is_match,
                        results: self.get_completions_for_path_mapping(
                            &normalized_key,
                            &patterns,
                            fragment,
                            base_directory,
                            is_exports,
                            is_imports,
                            extension_options,
                        ),
                    });
                }
            }
        }

        for pr in path_results {
            for res in pr.results {
                result.add(res);
            }
        }

        matched_path.is_some()
    }

    /// `getCompletionsForPathMapping`.
    fn get_completions_for_path_mapping(
        &self,
        path: &str,
        patterns: &[String],
        fragment: &str,
        package_directory: &RootedDirectoryPath,
        is_exports: bool,
        is_imports: bool,
        extension_options: &ExtensionOptions,
    ) -> Vec<ModuleCompletionNameAndKind> {
        let mut fragment_directory = get_fragment_directory(fragment);
        if !fragment_directory.is_empty() {
            fragment_directory =
                tspath::ensure_trailing_directory_separator(&fragment_directory).into_owned();
        }
        let just_path_mapping_name = |name: &str,
                                      kind: ModuleCompletionKind,
                                      extension: &str|
         -> Vec<ModuleCompletionNameAndKind> {
            if name.starts_with(fragment) {
                let name = tspath::remove_trailing_directory_separator(name);
                let name = if !fragment_directory.is_empty() {
                    name.trim_start_matches(&fragment_directory)
                } else {
                    name
                };
                return vec![ModuleCompletionNameAndKind {
                    name: name.to_string(),
                    kind,
                    extension: extension.to_string(),
                }];
            }
            Vec::new()
        };

        let parsed_path = tsc_core::pattern::try_parse_pattern(path);
        if !parsed_path.is_valid() {
            return Vec::new();
        }
        // No stars in the pattern.
        if parsed_path.star_index == -1 {
            // For a path mapping "foo": ["/x/y/z.ts"], add "foo" itself as a
            // completion.
            let extension = patterns
                .first()
                .map(|p| get_file_extension(p))
                .unwrap_or_default();
            return just_path_mapping_name(path, ModuleCompletionKind::File, &extension);
        }

        let star_index = parsed_path.star_index as usize;
        let path_prefix = &parsed_path.text[..star_index];
        let path_suffix = &parsed_path.text[star_index + 1..];
        if !fragment.starts_with(path_prefix) {
            // Fragment doesn't match the path mapping prefix at all:
            // we cannot extend it via this path.
            if !path_prefix.starts_with(fragment) {
                return Vec::new();
            }
            let star_is_full_path_component = path.ends_with("/*");
            if star_is_full_path_component {
                return just_path_mapping_name(path_prefix, ModuleCompletionKind::Directory, "");
            }
            // If path is e.g. `foo/bar/*`, and fragment is `foo/b`, then
            // remaining directory prefix is `bar/`,
            let remaining_directory_prefix = path_prefix[fragment_directory.len()..].to_string();
            let mut completions = Vec::new();
            for pattern in patterns {
                let mut modules = self.get_modules_for_paths_pattern(
                    "", /*fragment*/
                    package_directory,
                    pattern,
                    is_exports,
                    is_imports,
                    extension_options,
                );
                for m in modules.iter_mut() {
                    m.name = format!(
                        "{remaining_directory_prefix}{}{}",
                        m.name,
                        if m.kind == ModuleCompletionKind::File {
                            path_suffix
                        } else {
                            ""
                        }
                    );
                }
                completions.extend(modules);
            }
            return completions;
        }
        let remaining_fragment = fragment[path_prefix.len()..].to_string();
        let remaining_directory_fragment = if !fragment_directory.starts_with(path_prefix) {
            path_prefix[fragment_directory.len()..].to_string()
        } else {
            String::new()
        };
        let mut completions = Vec::new();
        for pattern in patterns {
            let mut modules = self.get_modules_for_paths_pattern(
                &remaining_fragment,
                package_directory,
                pattern,
                is_exports,
                is_imports,
                extension_options,
            );
            for m in modules.iter_mut() {
                m.name = format!(
                    "{remaining_directory_fragment}{}{}",
                    m.name,
                    if m.kind == ModuleCompletionKind::File {
                        path_suffix
                    } else {
                        ""
                    }
                );
            }
            completions.extend(modules);
        }
        completions
    }

    /// `getModulesForPathsPattern` — the input fragment is relative to the
    /// path pattern's prefix:
    /// e.g. if path = `"bar/_*/baz"`, and fragment = `"bar/_dir"`, then
    /// fragment is `"dir"`.
    /// The names are relative to the path pattern's prefix and fragment
    /// directory:
    /// e.g. if path = `"bar/_*/baz"`, and fragment = `"bar/_dir/a"`, and we
    /// find result `"abd"`, the result should be interpreted as
    /// `"bar/_dir/abd"`.
    fn get_modules_for_paths_pattern(
        &self,
        fragment: &str,
        package_directory: &RootedDirectoryPath,
        pattern: &str,
        is_exports: bool,
        is_imports: bool,
        extension_options: &ExtensionOptions,
    ) -> Vec<ModuleCompletionNameAndKind> {
        let program = self.get_program();
        let parsed = tsc_core::pattern::try_parse_pattern(pattern);
        if !parsed.is_valid() || parsed.star_index == -1 {
            return Vec::new();
        }

        let star_index = parsed.star_index as usize;
        let prefix = &parsed.text[..star_index];
        let suffix = &parsed.text[star_index + 1..];

        // The prefix has two effective parts: the directory path and the base
        // component after the filepath that is not a full directory component.
        // For example: directory/path/of/prefix/base*
        let normalized_prefix = tspath::resolve_path(prefix, &[]);
        let (normalized_prefix_directory, normalized_prefix_base) =
            if tspath::has_trailing_directory_separator(prefix) {
                (normalized_prefix.clone(), String::new())
            } else {
                (
                    tspath::get_directory_path(&normalized_prefix).into_owned(),
                    tspath::get_base_file_name(&normalized_prefix).into_owned(),
                )
            };

        let fragment_has_path = contains_slash(fragment);
        let fragment_directory = if fragment_has_path {
            if tspath::has_trailing_directory_separator(fragment) {
                fragment.to_string()
            } else {
                tspath::get_directory_path(fragment).into_owned()
            }
        } else {
            String::new()
        };

        let options = program.options();
        let case_sensitivity = program.case_sensitivity();
        let out_dir = options.out_dir.clone();
        let declaration_dir = options.declaration_dir.clone();

        // Try and expand the prefix to include any path from the fragment so
        // that we can limit the readDirectory call.
        let expanded_prefix_directory = if fragment_has_path {
            tspath::combine_paths(
                &normalized_prefix_directory,
                &[&format!("{normalized_prefix_base}{fragment_directory}")],
            )
        } else {
            normalized_prefix_directory.clone()
        };
        // Need to normalize after combining: If we combinePaths("a", "../b"),
        // we want "b" and not "a/../b".
        let base_directory = package_directory.resolve_directory(&expanded_prefix_directory);

        let possible_input_base_directory_for_out_dir =
            if is_imports && !out_dir.as_string().is_empty() {
                get_possible_original_input_path_without_changing_ext(
                    &base_directory,
                    case_sensitivity,
                    &out_dir,
                    || program.common_source_directory(),
                )
            } else {
                RootedDirectoryPath::default()
            };
        let possible_input_base_directory_for_declaration_dir =
            if is_imports && !declaration_dir.as_string().is_empty() {
                get_possible_original_input_path_without_changing_ext(
                    &base_directory,
                    case_sensitivity,
                    &declaration_dir,
                    || program.common_source_directory(),
                )
            } else {
                RootedDirectoryPath::default()
            };

        let normalized_suffix = tspath::normalize_path(suffix).into_owned();

        let mut input_extensions = Vec::new();
        let declaration_extension = if !normalized_suffix.is_empty() {
            let decl_ext =
                tspath::get_declaration_emit_extension_for_path(&format!("_{normalized_suffix}"))
                    .into_owned();
            input_extensions = tspath::get_possible_original_input_extension_for_extension(
                &format!("_{normalized_suffix}"),
            );
            decl_ext
        } else {
            String::new()
        };

        let mut matching_suffixes = Vec::new();
        if !declaration_extension.is_empty() {
            matching_suffixes.push(
                tspath::change_extension(&normalized_suffix, &declaration_extension).into_owned(),
            );
        }
        for ext in &input_extensions {
            matching_suffixes.push(tspath::change_extension(&normalized_suffix, ext).into_owned());
        }
        matching_suffixes.push(normalized_suffix.clone());

        // If we have a suffix, then we read the directory all the way down to
        // avoid returning completions for directories that don't contain files
        // that would match the suffix. See Go comment for why `?` in the
        // suffix is not a problem.
        let include_globs: Vec<String> = if !normalized_suffix.is_empty() {
            matching_suffixes
                .iter()
                .map(|suffix| format!("**/*{suffix}"))
                .collect()
        } else {
            vec!["./*".to_string()]
        };

        let is_exports_or_imports_wildcard = (is_exports || is_imports) && pattern.ends_with("/*");

        let trim_prefix_and_suffix = |path: &str, prefix_str: &str| -> String {
            for suffix in &matching_suffixes {
                if let Some(inner) =
                    without_start_and_end(&tspath::normalize_path(path), prefix_str, suffix)
                {
                    return remove_leading_directory_separator(&inner).to_string();
                }
            }
            String::new()
        };

        let get_matches_with_prefix =
            |directory: &RootedDirectoryPath| -> Vec<ModuleCompletionNameAndKind> {
                let complete_prefix = if fragment_has_path {
                    directory.as_string().to_string()
                } else {
                    format!(
                        "{}{}",
                        tspath::ensure_trailing_directory_separator(directory.as_string()),
                        normalized_prefix_base
                    )
                };

                let extensions: Vec<&str> = extension_options
                    .extensions_to_search
                    .iter()
                    .map(|s| s.as_str())
                    .collect();
                let include_glob_strs: Vec<&str> =
                    include_globs.iter().map(|s| s.as_str()).collect();
                let matches = self.read_directory(directory, &extensions, &include_glob_strs);

                let mut result = Vec::new();
                for m in matches {
                    let trimmed_with_pattern =
                        trim_prefix_and_suffix(m.as_string(), &complete_prefix);
                    if !trimmed_with_pattern.is_empty() {
                        if contains_slash(&trimmed_with_pattern) {
                            let path_components = tspath::get_path_components(
                                remove_leading_directory_separator(&trimmed_with_pattern),
                            );
                            if path_components.len() > 1 {
                                result.push(ModuleCompletionNameAndKind {
                                    name: path_components[1].clone(),
                                    kind: ModuleCompletionKind::Directory,
                                    extension: String::new(),
                                });
                            }
                        } else {
                            let (name, mut extension) = self.get_filename_with_extension_option(
                                &trimmed_with_pattern,
                                extension_options,
                                is_exports_or_imports_wildcard,
                            );
                            if extension.is_empty() {
                                extension = get_file_extension(m.as_string());
                            }
                            result.push(ModuleCompletionNameAndKind {
                                name,
                                kind: ModuleCompletionKind::File,
                                extension,
                            });
                        }
                    }
                }
                result
            };

        let get_directory_matches =
            |directory_name: &RootedDirectoryPath| -> Vec<ModuleCompletionNameAndKind> {
                let directories = self.get_directories(directory_name);
                let mut result = Vec::new();
                for dir in directories {
                    if dir != "node_modules" {
                        result.push(ModuleCompletionNameAndKind {
                            name: dir,
                            kind: ModuleCompletionKind::Directory,
                            extension: String::new(),
                        });
                    }
                }
                result
            };

        let mut matches = get_matches_with_prefix(&base_directory);
        if !possible_input_base_directory_for_out_dir
            .as_string()
            .is_empty()
        {
            matches.extend(get_matches_with_prefix(
                &possible_input_base_directory_for_out_dir,
            ));
        }
        if !possible_input_base_directory_for_declaration_dir
            .as_string()
            .is_empty()
        {
            matches.extend(get_matches_with_prefix(
                &possible_input_base_directory_for_declaration_dir,
            ));
        }

        // If we had a suffix, we already recursively searched for all possible
        // files that could match it and returned the directories leading to
        // those files. Otherwise, assume any directory could have something
        // valid to import.
        if normalized_suffix.is_empty() {
            matches.extend(get_directory_matches(&base_directory));
            if !possible_input_base_directory_for_out_dir
                .as_string()
                .is_empty()
            {
                matches.extend(get_directory_matches(
                    &possible_input_base_directory_for_out_dir,
                ));
            }
            if !possible_input_base_directory_for_declaration_dir
                .as_string()
                .is_empty()
            {
                matches.extend(get_directory_matches(
                    &possible_input_base_directory_for_declaration_dir,
                ));
            }
        }

        matches
    }

    /// `getFilenameWithExtensionOption` — returns `(name, extension)`.
    fn get_filename_with_extension_option(
        &self,
        name: &str,
        extension_options: &ExtensionOptions,
        is_exports_or_imports_wildcard: bool,
    ) -> (String, String) {
        let program = self.get_program();
        let non_js_result =
            tsc_modulespecifiers::util::try_get_real_file_name_for_non_js_declaration_file_name(
                name,
            );
        if !non_js_result.is_empty() {
            return (
                non_js_result.clone(),
                tspath::try_get_extension_from_path(&non_js_result).to_string(),
            );
        }
        if extension_options.reference_kind == ReferenceKind::FileName {
            return (
                name.to_string(),
                tspath::try_get_extension_from_path(name).to_string(),
            );
        }

        let mut allowed_endings = {
            let nodes = program.nodes(extension_options.importing_source_file.file_index());
            let mut prefs = tsc_modulespecifiers::UserPreferences::default();
            prefs.import_module_specifier_ending = extension_options.ending_preference;
            tsc_modulespecifiers::preferences::get_allowed_endings_in_preferred_order(
                &prefs,
                &*program,
                &program.options(),
                nodes[extension_options.importing_source_file].as_source_file(),
                "", /*oldImportSpecifier*/
                extension_options.resolution_mode,
                &nodes,
                &|_| None,
            )
        };

        if is_exports_or_imports_wildcard {
            // If we're completing `import {} from "foo/|"` and subpaths are
            // available via `"exports": { "./*": "./src/*" }`, the completion
            // must be a (potentially extension-swapped) file name. Dropping
            // extensions and index files is not allowed.
            allowed_endings.retain(|e| {
                *e != tsc_modulespecifiers::ModuleSpecifierEnding::Minimal
                    && *e != tsc_modulespecifiers::ModuleSpecifierEnding::Index
            });
        }

        if !allowed_endings.is_empty()
            && allowed_endings[0] == tsc_modulespecifiers::ModuleSpecifierEnding::TsExtension
        {
            if tspath::file_extension_is_one_of(
                name,
                tspath::SUPPORTED_TS_IMPLEMENTATION_EXTENSIONS,
            ) {
                return (
                    name.to_string(),
                    tspath::try_get_extension_from_path(name).to_string(),
                );
            }
            let output_extension =
                tsc_module::util::try_get_js_extension_for_file(name, &program.options());
            if !output_extension.is_empty() {
                return (
                    tspath::change_extension(name, output_extension).into_owned(),
                    output_extension.to_string(),
                );
            }
            return (
                name.to_string(),
                tspath::try_get_extension_from_path(name).to_string(),
            );
        }

        if !is_exports_or_imports_wildcard
            && !allowed_endings.is_empty()
            && (allowed_endings[0] == tsc_modulespecifiers::ModuleSpecifierEnding::Minimal
                || allowed_endings[0] == tsc_modulespecifiers::ModuleSpecifierEnding::Index)
            && tspath::file_extension_is_one_of(
                name,
                &[
                    tspath::EXTENSION_JS,
                    tspath::EXTENSION_JSX,
                    tspath::EXTENSION_TS,
                    tspath::EXTENSION_TSX,
                    tspath::EXTENSION_DTS,
                ],
            )
        {
            return (
                tspath::remove_file_extension(name).to_string(),
                tspath::try_get_extension_from_path(name).to_string(),
            );
        }

        let output_extension =
            tsc_module::util::try_get_js_extension_for_file(name, &program.options());
        if !output_extension.is_empty() {
            return (
                tspath::change_extension(name, output_extension).into_owned(),
                output_extension.to_string(),
            );
        }
        (
            name.to_string(),
            tspath::try_get_extension_from_path(name).to_string(),
        )
    }

    /// `isInReferenceComment`.
    fn is_in_reference_comment(&self, file: NodeId, position: TextPos) -> bool {
        let program = self.get_program();
        let mut nodes = program.nodes_mut(file.file_index());
        let token_at_position =
            tsc_astnav::tokens::get_token_at_position(&mut nodes, file, position);
        let Some(comment_range) =
            utilities::is_in_comment(&mut nodes, file, position, token_at_position)
        else {
            return false;
        };
        let comment_text = &nodes[file].as_source_file().text
            [comment_range.text_range.pos() as usize..comment_range.text_range.end() as usize];
        has_triple_slash_prefix(comment_text)
    }

    /// `getTripleSlashReferenceCompletions`.
    fn get_triple_slash_reference_completions(
        &self,
        file: NodeId,
        position: TextPos,
        checker: &mut Checker,
    ) -> Option<PathCompletions> {
        let program = self.get_program();
        let compiler_options = program.options();
        let (token, text) = {
            let mut nodes = program.nodes_mut(file.file_index());
            let token = tsc_astnav::tokens::get_token_at_position(&mut nodes, file, position);
            (token, nodes[file].as_source_file().text.clone())
        };
        let token = token?;
        let token_pos = program.arena_of(token)[token].pos();
        let comment_ranges = tsc_scanner::scanner::get_leading_comment_ranges(
            &NodeFactory::<'static>::new(NodeFactoryHooks::default()),
            &text,
            token_pos,
        );

        let mut found_range = None;
        for comment_range in &comment_ranges {
            if position >= comment_range.text_range.pos()
                && position <= comment_range.text_range.end()
            {
                found_range = Some(*comment_range);
                break;
            }
        }
        let found_range = found_range?;

        let comment_text = &text[found_range.text_range.pos() as usize..position.max(0) as usize];
        let (prefix, kind, to_complete) = parse_triple_slash_directive_fragment(comment_text)?;
        let replacement_span = self.path_completion_replacement_span(
            file,
            get_directory_fragment_range(
                &to_complete,
                found_range.text_range.pos() + prefix.len() as i32,
            ),
        )?;

        let script_directory = {
            let nodes = program.nodes(file.file_index());
            nodes[file].as_source_file().file_name().directory()
        };

        let names = match kind.as_str() {
            "path" => {
                let extension_options = self.get_extension_options(
                    &compiler_options,
                    ReferenceKind::FileName,
                    file,
                    tsc_core::compileroptions::RESOLUTION_MODE_NONE,
                    None,
                );
                let script_path = {
                    let nodes = program.nodes(file.file_index());
                    nodes[file].as_source_file().path_key().clone()
                };
                let mut result = ModuleCompletionNameAndKindSet::default();
                self.get_completion_entries_for_directory_fragment(
                    &to_complete,
                    &script_directory,
                    &extension_options,
                    true, /*moduleSpecifierIsRelative*/
                    Some(&script_path),
                    &mut result,
                );
                result.into_values()
            }
            "types" => {
                let extension_options = self.get_extension_options(
                    &compiler_options,
                    ReferenceKind::ModuleSpecifier,
                    file,
                    tsc_core::compileroptions::RESOLUTION_MODE_NONE,
                    None,
                );
                let mut result = ModuleCompletionNameAndKindSet::default();
                self.get_completion_entries_from_typings(
                    &script_directory,
                    &get_fragment_directory(&to_complete),
                    &extension_options,
                    &mut result,
                );
                result.into_values()
            }
            _ => Vec::new(),
        };
        let _ = checker;

        Some(PathCompletions {
            entries: to_path_completions(names),
            replacement_span,
        })
    }
}

/// `hasTripleSlashPrefix`.
fn has_triple_slash_prefix(comment_text: &str) -> bool {
    comment_text.starts_with("///") && comment_text[3..].trim_start().starts_with('<')
}

/// `parseTripleSlashDirectiveFragment` — matches a triple slash reference
/// directive with an incomplete string literal for its path. Returns
/// `(prefix, kind, to_complete)` where `prefix` is everything up to and
/// including the opening quote, `kind` is either `"path"` or `"types"`, and
/// `to_complete` is the fragment after the opening quote.
fn parse_triple_slash_directive_fragment(text: &str) -> Option<(String, String, String)> {
    let mut rest = text;
    if !rest.starts_with("///") {
        return None;
    }

    rest = &rest["///".len()..];
    rest = rest.trim_start_matches(|c: char| tsc_stringutil::is_white_space_like(c));

    // <reference
    if !rest.starts_with("<reference") {
        return None;
    }
    rest = &rest["<reference".len()..];

    if rest.is_empty() || !tsc_stringutil::is_white_space_like(rest.chars().next().unwrap()) {
        return None;
    }
    rest = rest.trim_start_matches(|c: char| tsc_stringutil::is_white_space_like(c));

    // path or types
    let kind;
    if rest.starts_with("path") {
        kind = "path";
        rest = &rest["path".len()..];
    } else if rest.starts_with("types") {
        kind = "types";
        rest = &rest["types".len()..];
    } else {
        return None;
    }

    // Skip optional whitespace, then must have "="
    rest = rest.trim_start_matches(|c: char| tsc_stringutil::is_white_space_like(c));
    if !rest.starts_with('=') {
        return None;
    }
    rest = &rest[1..];

    // Skip optional whitespace, then must have opening quote (' or ")
    rest = rest.trim_start_matches(|c: char| tsc_stringutil::is_white_space_like(c));
    if rest.is_empty() || (rest.as_bytes()[0] != b'\'' && rest.as_bytes()[0] != b'"') {
        return None;
    }
    rest = &rest[1..];

    // The toComplete part is everything after the opening quote
    if rest.contains('\'') || rest.contains('"') {
        return None;
    }
    let to_complete = rest;
    let prefix = &text[..text.len() - to_complete.len()];
    Some((
        prefix.to_string(),
        kind.to_string(),
        to_complete.to_string(),
    ))
}

/// `stringLiteralCompletionsForObjectLiteral` — `object_literal_expression`
/// is an `*ast.ObjectLiteralExpressionNode`.
fn string_literal_completions_for_object_literal(
    program: &Program,
    type_checker: &mut Checker,
    object_literal_expression: NodeId,
) -> Option<CompletionsFromProperties> {
    let contextual_type =
        type_checker.get_contextual_type_api(object_literal_expression, ContextFlags::NONE)?;

    let completions_type = type_checker.get_contextual_type_api(
        object_literal_expression,
        ContextFlags::IGNORE_NODE_INFERENCES,
    );
    let symbols = completions::get_properties_for_object_expression(
        &program,
        contextual_type,
        completions_type,
        object_literal_expression,
        type_checker,
    );

    Some(CompletionsFromProperties {
        symbols,
        has_index_signature: has_index_signature(contextual_type, type_checker),
    })
}

/// `stringLiteralCompletionsFromProperties`.
fn string_literal_completions_from_properties(
    t: TypeId,
    type_checker: &mut Checker,
) -> CompletionsFromProperties {
    let program = type_checker.program.clone().expect("program");
    let symbols = type_checker
        .get_apparent_properties(t)
        .into_iter()
        .filter(|&s| {
            let value_declaration = program.symbols().borrow()[s.index()].value_declaration;
            value_declaration.is_none_or(|d| {
                let nodes = program.nodes(d.file_index());
                !ast::is_private_identifier_class_element_declaration(&nodes[d], &nodes)
            })
        })
        .collect();
    CompletionsFromProperties {
        symbols,
        has_index_signature: has_index_signature(t, type_checker),
    }
}

/// `getStringLiteralCompletionsFromSignature`.
fn get_string_literal_completions_from_signature(
    call: NodeId,
    arg: NodeId,
    argument_info: &completions::ArgumentInfoForCompletions,
    type_checker: &mut Checker,
) -> Option<CompletionsFromTypes> {
    let program = type_checker.program.clone().expect("program");
    let mut is_new_identifier = false;
    let mut uniques = Set::default();
    let is_jsx_opening_like = {
        let nodes = program.nodes(call.file_index());
        ast::is_jsx_opening_like_element(&nodes[call])
    };
    let editing_argument = if is_jsx_opening_like {
        let nodes = program.nodes(arg.file_index());
        ast::find_ancestor(nodes[arg].parent, &nodes, &mut |n, _| {
            ast::is_jsx_attribute(n)
        })
        .expect("Expected jsx opening-like element to have a jsx attribute as ancestor.")
    } else {
        arg
    };
    let candidates = type_checker
        .get_candidate_signatures_for_string_literal_completions(call, editing_argument);
    let mut types = Vec::new();
    for candidate in candidates {
        let (has_rest_parameter, parameters_len) = {
            let signature = type_checker.signature_arena.get(candidate);
            (signature.has_rest_parameter(), signature.parameters().len())
        };
        if !has_rest_parameter && argument_info.argument_count > parameters_len {
            continue;
        }
        let mut t =
            type_checker.get_type_parameter_at_position(candidate, argument_info.argument_index);
        if is_jsx_opening_like {
            let attr_name = {
                let nodes = program.nodes(editing_argument.file_index());
                nodes[editing_argument]
                    .as_jsx_attribute()
                    .name
                    .map(|n| nodes[n].text(&nodes).into_owned())
            };
            if let Some(attr_name) = attr_name {
                if let Some(prop_type) = type_checker.get_type_of_property_of_type(t, &attr_name) {
                    t = prop_type;
                }
            }
        }
        is_new_identifier = is_new_identifier || type_checker.types.get(t).is_string();
        types.extend(get_string_literal_types(
            Some(t),
            Some(&mut uniques),
            type_checker,
        ));
    }
    if !types.is_empty() {
        return Some(CompletionsFromTypes {
            types,
            is_new_identifier,
        });
    }
    None
}

/// `getSupportedExtensionsForModuleResolution`.
fn get_supported_extensions_for_module_resolution(
    options: &CompilerOptions,
    extra_extensions: &[String],
    checker: Option<&mut Checker>,
) -> Vec<String> {
    // file extensions from ambient modules declarations e.g. *.css
    let mut extensions = Vec::new();
    if let Some(checker) = checker {
        let program = checker.program.clone().expect("program");
        let ambient_modules = checker.get_ambient_modules();
        for module in ambient_modules {
            let name = get_ambient_module_name(module, &program);
            if !name.starts_with("*.") || name.contains('/') {
                continue;
            }
            extensions.push(name[1..].to_string());
        }
    }
    let supported_extensions =
        tsc_tsoptions::tsconfigparsing::get_supported_extensions(options, extra_extensions);
    for ext in &supported_extensions {
        extensions.extend(ext.iter().cloned());
    }
    let module_resolution = options.get_module_resolution_kind();
    if module_resolution_uses_node_modules(module_resolution) {
        return tsc_core::core::flatten(
            &tsc_tsoptions::tsconfigparsing::get_supported_extensions_with_json_if_resolve_json_module(
                Some(options),
                &[extensions],
            ),
        );
    }
    extensions
}

/// `comparePaths` — the default ordering for `paths` keys used by
/// `addCompletionEntriesFromPaths` (longer matched prefix first).
fn compare_paths_default(a: &str, b: &str) -> tsc_stringutil::Comparison {
    let pattern_a = tsc_core::pattern::try_parse_pattern(a);
    let pattern_b = tsc_core::pattern::try_parse_pattern(b);
    let length_a = if pattern_a.star_index != -1 {
        pattern_a.star_index
    } else {
        a.len() as i32
    };
    let length_b = if pattern_b.star_index != -1 {
        pattern_b.star_index
    } else {
        b.len() as i32
    };
    length_b.cmp(&length_a) as tsc_stringutil::Comparison
}

/// Helper: parent of `node` (`Option<NodeId>`).
fn nodes_parent(program: &Program, node: NodeId) -> Option<NodeId> {
    program.nodes(node.file_index())[node].parent
}

/// `module.ComparePatternKeys` adapted to `stringutil.Comparison`.
fn compare_pattern_keys_comparison(a: &str, b: &str) -> tsc_stringutil::Comparison {
    match tsc_module::util::compare_pattern_keys(a, b) {
        std::cmp::Ordering::Less => tsc_stringutil::COMPARISON_LESS_THAN,
        std::cmp::Ordering::Equal => tsc_stringutil::COMPARISON_EQUAL,
        std::cmp::Ordering::Greater => tsc_stringutil::COMPARISON_GREATER_THAN,
    }
}

impl LanguageService<'_> {
    /// `getStringLiteralCompletionDetails` — used by `getCompletionItemDetails`
    /// (the `completionItem/resolve` path, `ResolveCompletionItem` — itself
    /// not yet ported).
    pub(crate) fn get_string_literal_completion_details(
        &self,
        ctx: &Context,
        checker: &mut Checker,
        item: lsproto::CompletionItem,
        name: &str,
        file: NodeId,
        position: TextPos,
        context_token: Option<NodeId>,
        doc_format: lsproto::MarkupKind,
    ) -> lsproto::CompletionItem {
        let Some(context_token) = context_token else {
            return item;
        };
        let is_string_literal_like = {
            let program = self.get_program();
            let nodes = program.nodes(context_token.file_index());
            ast::is_string_literal_like(&nodes[context_token])
        };
        if !is_string_literal_like {
            return item;
        }
        let Some(completions) =
            self.get_string_literal_completion_entries(ctx, file, context_token, position, checker)
        else {
            return item;
        };
        self.string_literal_completion_details(
            item,
            name,
            context_token,
            position,
            &completions,
            file,
            checker,
            doc_format,
        )
    }

    /// `stringLiteralCompletionDetails`.
    fn string_literal_completion_details(
        &self,
        item: lsproto::CompletionItem,
        name: &str,
        location: NodeId,
        position: TextPos,
        completion: &StringLiteralCompletions,
        file: NodeId,
        checker: &mut Checker,
        doc_format: lsproto::MarkupKind,
    ) -> lsproto::CompletionItem {
        let program = self.get_program();
        if completion.from_paths.is_some() {
            // Path completions have eagerly-resolved details so the client can
            // show an accurate icon for items of file kind based on the file
            // extension provided in the item detail.
            return item;
        }
        if let Some(properties) = &completion.from_properties {
            for &symbol in &properties.symbols {
                let symbol_name = program.symbols.borrow()[symbol.index()].name.clone();
                if symbol_name == name {
                    return self.create_completion_details_for_symbol(
                        item, symbol, checker, location, position, doc_format,
                    );
                }
            }
        }
        if let Some(types) = &completion.from_types {
            for &t in &types.types {
                let matches = {
                    let t_ref = checker.types.get(t);
                    matches!(&t_ref.as_literal_type().value, Some(tsc_evaluator::Value::String(v)) if v == name)
                };
                if matches {
                    return create_completion_details(item, name, "", doc_format);
                }
            }
        }
        let _ = file;
        item
    }

    /// `createCompletionDetailsForSymbol`.
    ///
    /// PORT(deferred): `getQuickInfoAndDocumentationForSymbol` lives in
    /// hover.go (sibling-owned and still a skeleton), so the symbol's quick
    /// info/documentation detail is not populated yet.
    fn create_completion_details_for_symbol(
        &self,
        item: lsproto::CompletionItem,
        symbol: SymbolId,
        checker: &mut Checker,
        location: NodeId,
        position: TextPos,
        doc_format: lsproto::MarkupKind,
    ) -> lsproto::CompletionItem {
        // PORT(deferred): quickInfo/documentation come from
        // `l.getQuickInfoAndDocumentationForSymbol(checker, symbol, location,
        // docFormat, nil, false /*vsCapability*/)`.
        let _ = (symbol, checker, location, position);
        create_completion_details(item, "", "", doc_format)
    }
}

/// `createCompletionDetails`.
///
/// PORT(ownership): Go mutates `*item` and returns it; the Rust version takes
/// and returns the value.
fn create_completion_details(
    mut item: lsproto::CompletionItem,
    detail: &str,
    documentation: &str,
    doc_format: lsproto::MarkupKind,
) -> lsproto::CompletionItem {
    // !!! fill in additionalTextEdits from code actions
    if item.detail.is_none() && !detail.is_empty() {
        item.detail = Some(detail.to_string());
    }
    if !documentation.is_empty() {
        item.documentation = Some(lsproto::StringOrMarkupContent {
            markup_content: Some(lsproto::MarkupContent {
                kind: doc_format,
                value: documentation.to_string(),
            }),
            ..Default::default()
        });
    }
    item
}
