// Ported from tsc/internal/ls/completions.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// PORT(partial): the port is in progress — top-level structures, the entry
// points and small helpers are complete; `getCompletionData` and the symbol
// entry builders are still being ported.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::{Kind, ModifierFlags, Node, NodeFlags, NodeId, SymbolFlags, SymbolId, self as ast};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{ContextFlags, TypeId};
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::{TextPos, TextRange};
use tsc_debug as debug;
use tsc_lsproto::{self as lsproto, CompletionItem as LspCompletionItem};
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::languageservice::LanguageService;

/// `ErrNeedsAutoImports` — `errors.New("completion list needs auto imports")`.
///
/// Go's sentinel is an `error` value; the port mirrors it as a constant of
/// the language-service `Error` enum.
pub(crate) const ERR_NEEDS_AUTO_IMPORTS: Error = Error::NeedsAutoImports;

/// `getSwitchedType` — `caseClause` is a `*ast.CaseOrDefaultClauseNode`.
pub(crate) fn get_switched_type(case_clause: NodeId, type_checker: &mut Checker) -> TypeId {
    let expression = {
        let program = type_checker.program.clone().expect("program");
        let nodes = program.nodes(case_clause.file_index());
        nodes[nodes[case_clause].parent.expect("CaseClause parent")]
            .parent
            .and_then(|p| nodes[p].expression())
            .expect("switch expression")
    };
    type_checker.get_type_at_location(expression)
}

/// `isEqualityOperatorKind`.
pub(crate) fn is_equality_operator_kind(kind: Kind) -> bool {
    match kind {
        Kind::EqualsEqualsEqualsToken
        | Kind::EqualsEqualsToken
        | Kind::ExclamationEqualsEqualsToken
        | Kind::ExclamationEqualsToken => true,
        _ => false,
    }
}

impl LanguageService<'_> {
    /// `ProvideCompletion`.
    pub fn provide_completion(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
        lsp_position: lsproto::Position,
        context: Option<&lsproto::CompletionContext>,
    ) -> Result<lsproto::CompletionItemsOrListOrNull, Error> {
        let (program, file) = self.get_program_and_file(&document_uri);
        let trigger_character = context.and_then(|c| c.trigger_character.clone());
        let ctx = tsc_format::with_format_code_settings(
            ctx,
            self.format_options(),
            &self.format_options().editor_settings.new_line_character,
        );
        let nodes = program.nodes(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            lsp_position,
            Feature::Completion,
        );
        if positions.is_empty() || !positions[0].fidelity.is_exact() {
            // In a content-mapped file the cursor is outside a verbatim span, so any completion committed here
            // could not be applied to the original text. Offer nothing rather than edits at a bogus location.
            return Ok(lsproto::CompletionItemsOrListOrNull::default());
        }
        let file = positions[0].script.file;
        let position = positions[0].position;
        drop(positions);
        drop(nodes);
        let completion_list_internal = self.get_completions_at_position(
            &ctx,
            file,
            position,
            trigger_character.as_deref(),
            false, /*includeSymbols*/
        )?;
        let mut completion_list = ensure_item_data(
            &program,
            file,
            position,
            completion_list_internal
                .as_ref()
                .map(CompletionList::to_lsp),
        );
        let has_span_map = {
            let nodes = program.nodes(file.file_index());
            nodes[file].as_source_file().span_map().is_some()
        };
        if has_span_map {
            if let Some(completion_list) = &mut completion_list {
                self.filter_content_mapped_auto_imports(&ctx, &program, file, completion_list);
            }
        }
        Ok(lsproto::CompletionItemsOrListOrNull {
            list: completion_list,
            ..Default::default()
        })
    }

    /// `filterContentMappedAutoImports` eagerly resolves auto-import edits for a content-mapped file and drops any
    /// completion whose import edit cannot be placed entirely within verbatim spans (it would otherwise insert
    /// an import into synthesized virtual code with no counterpart in the original file). Surviving auto-imports carry
    /// their additional edits directly so the client applies correct original-text positions on commit.
    fn filter_content_mapped_auto_imports(
        &self,
        ctx: &Context,
        program: &Program,
        file: NodeId,
        list: &mut lsproto::CompletionList,
    ) {
        let Some(items) = list.items.take() else {
            return;
        };
        let mut filtered: Vec<lsproto::CompletionItem> = Vec::new();
        for mut item in items {
            let Some(data) = &item.data else {
                filtered.push(item);
                continue;
            };
            let Some(auto_import) = &data.auto_import else {
                filtered.push(item);
                continue;
            };
            // PORT(deferred): `autoimport::Fix` is sibling-owned.
            let nodes = program.nodes_handle(file.file_index());
            let (edits, description, ok) = crate::autoimport::Fix {
                auto_import_fix: auto_import.clone(),
                ..Default::default()
            }
            .edits(
                ctx,
                &nodes,
                file,
                &program.options(),
                self.format_options(),
                &self.converters,
                self.user_preferences(),
            );
            if !ok {
                continue;
            }
            item.additional_text_edits = Some(edits);
            item.detail = Some(description);
            filtered.push(item);
        }
        list.items = Some(filtered);
    }

    /// `GetCompletionsAtPosition`.
    pub fn get_completions_at_position(
        &self,
        ctx: &Context,
        file: NodeId,
        position: TextPos,
        trigger_character: Option<&str>,
        include_symbols: bool,
    ) -> Result<Option<CompletionList>, Error> {
        self.get_completions_at_position_impl(
            ctx,
            file,
            position,
            trigger_character,
            include_symbols,
        )
    }
}

/// `type CompletionItem struct` — `*lsproto.CompletionItem` plus the resolved
/// symbol (`Symbol` is non-nil for symbol completions when `includeSymbols` is set).
#[derive(Clone)]
pub struct CompletionItem {
    /// `*lsproto.CompletionItem`.
    pub item: LspCompletionItem,
    /// `Symbol *ast.Symbol`.
    pub symbol: Option<SymbolId>,
}

/// `type CompletionList struct`.
#[derive(Default)]
pub struct CompletionList {
    /// `IsIncomplete`.
    pub is_incomplete: bool,
    /// `ItemDefaults`.
    pub item_defaults: Option<lsproto::CompletionItemDefaults>,
    /// `ApplyKind`.
    pub apply_kind: Option<lsproto::CompletionItemApplyKinds>,
    /// `Items` — `None` entries mirror Go's nil `*CompletionItem` elements.
    pub items: Vec<Option<CompletionItem>>,
}

/// `ensureItemData`.
fn ensure_item_data(
    program: &Program,
    file: NodeId,
    pos: i32,
    list: Option<lsproto::CompletionList>,
) -> Option<lsproto::CompletionList> {
    let mut list = list?;
    let (original_file_name, supplemental_file_index) = {
        let nodes = program.nodes(file.file_index());
        (
            nodes[file]
                .as_source_file()
                .original_file_name(&nodes)
                .as_string()
                .to_string(),
            supplemental_file_index(&nodes, file),
        )
    };
    if let Some(items) = list.items.as_mut() {
        for item in items.iter_mut() {
            if item.data.is_none() {
                item.data = Some(lsproto::CompletionItemData {
                    file_name: original_file_name.clone(),
                    position: pos,
                    supplemental_file_index,
                    name: item.label.clone(),
                    ..Default::default()
                });
            }
        }
    }
    Some(list)
}

/// `supplementalFileIndex`.
fn supplemental_file_index(nodes: &[Node], file: NodeId) -> Option<i32> {
    let sf = nodes[file].as_source_file();
    let Some(canonical) = sf.canonical_source_file() else {
        return None;
    };
    for (i, supplemental) in nodes[canonical]
        .as_source_file()
        .supplemental_source_files()
        .iter()
        .enumerate()
    {
        if *supplemental == file {
            return Some(i as i32);
        }
    }
    panic!("supplemental source file is not linked from its canonical source file")
}

/// `sourceFileForSupplementalFileIndex`.
fn source_file_for_supplemental_file_index(
    nodes: &[Node],
    file: NodeId,
    index: Option<i32>,
) -> Option<NodeId> {
    let Some(index) = index else {
        return Some(file);
    };
    let supplemental = nodes[file].as_source_file().supplemental_source_files();
    if index >= 0 && (index as usize) < supplemental.len() {
        return Some(supplemental[index as usize]);
    }
    None
}

/// `completionData` — Go's `any` field holding `*completionDataData |
/// *completionDataKeyword | *completionDataJSDocTagName |
/// *completionDataJSDocTag | *completionDataJSDocParameterName`.
pub(crate) enum CompletionData {
    /// `*completionDataData`.
    Data(Box<CompletionDataData>),
    /// `*completionDataKeyword`.
    Keyword(CompletionDataKeyword),
    /// `*completionDataJSDocTagName`.
    JSDocTagName,
    /// `*completionDataJSDocTag`.
    JSDocTag,
    /// `*completionDataJSDocParameterName`.
    JSDocParameterName {
        /// `tag *ast.JSDocParameterOrPropertyTag`.
        tag: NodeId,
    },
}

/// `type completionDataData struct`.
pub(crate) struct CompletionDataData {
    /// `symbols`.
    pub(crate) symbols: Vec<SymbolId>,
    /// `autoImports`.
    pub(crate) auto_imports: Vec<crate::autoimport::FixAndExport>,
    /// `completionKind`.
    pub(crate) completion_kind: CompletionKind,
    /// `isInSnippetScope`.
    pub(crate) is_in_snippet_scope: bool,
    /// `propertyAccessToConvert *ast.PropertyAccessExpressionNode` — note that
    /// the presence of this alone doesn't mean that we need a conversion. Only
    /// do that if the completion is not an ordinary identifier.
    pub(crate) property_access_to_convert: Option<NodeId>,
    /// `isNewIdentifierLocation`.
    pub(crate) is_new_identifier_location: bool,
    /// `location`.
    pub(crate) location: Option<NodeId>,
    /// `keywordFilters`.
    pub(crate) keyword_filters: KeywordCompletionFilters,
    /// `literals`.
    pub(crate) literals: Vec<LiteralValue>,
    /// `symbolToOriginInfoMap` — Go keys on the symbol's index into `symbols`.
    pub(crate) symbol_to_origin_info_map: HashMap<i32, SymbolOriginInfo>,
    /// `symbolToSortTextMap`.
    pub(crate) symbol_to_sort_text_map: HashMap<SymbolId, SortText>,
    /// `recommendedCompletion`.
    pub(crate) recommended_completion: Option<SymbolId>,
    /// `previousToken`.
    pub(crate) previous_token: Option<NodeId>,
    /// `contextToken`.
    pub(crate) context_token: Option<NodeId>,
    /// `jsxInitializer`.
    pub(crate) jsx_initializer: JsxInitializer,
    /// `insideJSDocTagTypeExpression`.
    pub(crate) inside_jsdoc_tag_type_expression: bool,
    /// `isTypeOnlyLocation`.
    pub(crate) is_type_only_location: bool,
    /// `isJsxIdentifierExpected` — in JSX tag name and attribute names,
    /// identifiers like "my-tag" or "aria-name" are valid identifiers.
    pub(crate) is_jsx_identifier_expected: bool,
    /// `isRightOfOpenTag`.
    pub(crate) is_right_of_open_tag: bool,
    /// `isRightOfDotOrQuestionDot`.
    pub(crate) is_right_of_dot_or_question_dot: bool,
    /// `importStatementCompletion`.
    pub(crate) import_statement_completion: Option<ImportStatementCompletionInfo>,
    /// `hasUnresolvedAutoImports`.
    pub(crate) has_unresolved_auto_imports: bool,
    /// `defaultCommitCharacters`.
    pub(crate) default_commit_characters: Vec<String>,
}

/// `type completionDataKeyword struct`.
pub(crate) struct CompletionDataKeyword {
    /// `keywordCompletions`.
    pub(crate) keyword_completions: Vec<CompletionItem>,
    /// `isNewIdentifierLocation`.
    pub(crate) is_new_identifier_location: bool,
}

/// `type importStatementCompletionInfo struct`.
#[derive(Clone, Default)]
pub(crate) struct ImportStatementCompletionInfo {
    /// `isKeywordOnlyCompletion`.
    pub(crate) is_keyword_only_completion: bool,
    /// `keywordCompletion` — `ast.Kind` (`TokenKind`).
    pub(crate) keyword_completion: Kind,
    /// `isNewIdentifierLocation`.
    pub(crate) is_new_identifier_location: bool,
    /// `isTopLevelTypeOnly`.
    pub(crate) is_top_level_type_only: bool,
    /// `couldBeTypeOnlyImportSpecifier`.
    pub(crate) could_be_type_only_import_specifier: bool,
    /// `replacementSpan`.
    pub(crate) replacement_span: Option<lsproto::Range>,
}

/// `type jsxInitializer struct` — if we're after the `=` sign but no
/// identifier has been typed yet, `isInitializer` is `true` and `initializer`
/// is `None`.
#[derive(Clone, Copy, Default)]
pub(crate) struct JsxInitializer {
    /// `isInitializer`.
    pub(crate) is_initializer: bool,
    /// `initializer *ast.IdentifierNode`.
    pub(crate) initializer: Option<NodeId>,
}

/// `type KeywordCompletionFilters int`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub(crate) struct KeywordCompletionFilters(pub i32);

impl KeywordCompletionFilters {
    /// `KeywordCompletionFiltersNone` — no keywords.
    pub(crate) const NONE: Self = Self(0);
    /// `KeywordCompletionFiltersAll` — every possible keyword.
    pub(crate) const ALL: Self = Self(1);
    /// `KeywordCompletionFiltersClassElementKeywords` — keywords inside class body.
    pub(crate) const CLASS_ELEMENT_KEYWORDS: Self = Self(2);
    /// `KeywordCompletionFiltersInterfaceElementKeywords` — keywords inside interface body.
    pub(crate) const INTERFACE_ELEMENT_KEYWORDS: Self = Self(3);
    /// `KeywordCompletionFiltersConstructorParameterKeywords` — keywords at constructor parameter.
    pub(crate) const CONSTRUCTOR_PARAMETER_KEYWORDS: Self = Self(4);
    /// `KeywordCompletionFiltersFunctionLikeBodyKeywords` — keywords at function like body.
    pub(crate) const FUNCTION_LIKE_BODY_KEYWORDS: Self = Self(5);
    /// `KeywordCompletionFiltersTypeAssertionKeywords`.
    pub(crate) const TYPE_ASSERTION_KEYWORDS: Self = Self(6);
    /// `KeywordCompletionFiltersTypeKeywords`.
    pub(crate) const TYPE_KEYWORDS: Self = Self(7);
    /// `KeywordCompletionFiltersTypeKeyword` — literally just `type`.
    pub(crate) const TYPE_KEYWORD: Self = Self(8);
    /// `KeywordCompletionFiltersLast`.
    #[allow(dead_code)]
    pub(crate) const LAST: Self = Self::TYPE_KEYWORD;
}

/// `keywordFiltersFromSyntaxKind`.
fn keyword_filters_from_syntax_kind(keyword_completion: Kind) -> KeywordCompletionFilters {
    match keyword_completion {
        Kind::TypeKeyword => KeywordCompletionFilters::TYPE_KEYWORD,
        _ => panic!(
            "Unknown mapping from ast.Kind `{}` to KeywordCompletionFilters",
            keyword_completion.kind_string()
        ),
    }
}

/// `type CompletionKind int`.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum CompletionKind {
    /// `CompletionKindNone`.
    #[default]
    None,
    /// `CompletionKindObjectPropertyDeclaration`.
    ObjectPropertyDeclaration,
    /// `CompletionKindGlobal`.
    Global,
    /// `CompletionKindPropertyAccess`.
    PropertyAccess,
    /// `CompletionKindMemberLike`.
    MemberLike,
    /// `CompletionKindString`.
    String,
}

/// `CompletionTriggerCharacters`.
pub(crate) fn completion_trigger_characters() -> &'static [&'static str] {
    &[".", "\"", "'", "`", "/", "@", "<", "#", " ", "*"]
}

/// `allCommitCharacters` — all commit characters, valid when
/// `isNewIdentifierLocation` is false.
fn all_commit_characters() -> &'static [&'static str] {
    &[".", ",", ";"]
}

/// `noCommaCommitCharacters` — commit characters valid at expression
/// positions where we could be inside a parameter list.
fn no_comma_commit_characters() -> &'static [&'static str] {
    &[".", ";"]
}

/// `emptyCommitCharacters`.
fn empty_commit_characters() -> &'static [&'static str] {
    &[]
}

/// `type SortText string` — sort texts are built dynamically
/// (`ObjectLiteralPropertySortText` etc.), so this is an owned string.
pub(crate) type SortText = String;

pub(crate) mod sort_text {
    /// `SortTextLocalDeclarationPriority`.
    pub(crate) const LOCAL_DECLARATION_PRIORITY: &str = "10";
    /// `SortTextLocationPriority`.
    pub(crate) const LOCATION_PRIORITY: &str = "11";
    /// `SortTextOptionalMember`.
    pub(crate) const OPTIONAL_MEMBER: &str = "12";
    /// `SortTextMemberDeclaredBySpreadAssignment`.
    pub(crate) const MEMBER_DECLARED_BY_SPREAD_ASSIGNMENT: &str = "13";
    /// `SortTextSuggestedClassMembers`.
    pub(crate) const SUGGESTED_CLASS_MEMBERS: &str = "14";
    /// `SortTextGlobalsOrKeywords`.
    pub(crate) const GLOBALS_OR_KEYWORDS: &str = "15";
    /// `SortTextAutoImportSuggestions`.
    pub(crate) const AUTO_IMPORT_SUGGESTIONS: &str = "16";
    /// `SortTextClassMemberSnippets`.
    pub(crate) const CLASS_MEMBER_SNIPPETS: &str = "17";
    /// `SortTextJavascriptIdentifiers`.
    pub(crate) const JAVASCRIPT_IDENTIFIERS: &str = "18";
}

/// `DeprecateSortText`.
pub(crate) fn deprecate_sort_text(original: &str) -> String {
    format!("z{original}")
}

/// `ObjectLiteralPropertySortText`.
pub(crate) fn object_literal_property_sort_text(
    preset_sort_text: &str,
    symbol_display_name: &str,
) -> String {
    format!("{preset_sort_text}\x00{symbol_display_name}\x00")
}

/// `SortBelow`.
pub(crate) fn sort_below(original: &str) -> String {
    format!("{original}1")
}

/// `type symbolOriginInfoKind int` — a bitmask.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct SymbolOriginInfoKind(pub i32);

impl SymbolOriginInfoKind {
    /// `symbolOriginInfoKindThisType`.
    pub(crate) const THIS_TYPE: Self = Self(1 << 0);
    /// `symbolOriginInfoKindSymbolMember`.
    pub(crate) const SYMBOL_MEMBER: Self = Self(1 << 1);
    /// `symbolOriginInfoKindPromise`.
    pub(crate) const PROMISE: Self = Self(1 << 2);
    /// `symbolOriginInfoKindNullable`.
    pub(crate) const NULLABLE: Self = Self(1 << 3);
    /// `symbolOriginInfoKindTypeOnlyAlias`.
    pub(crate) const TYPE_ONLY_ALIAS: Self = Self(1 << 4);
    /// `symbolOriginInfoKindObjectLiteralMethod`.
    pub(crate) const OBJECT_LITERAL_METHOD: Self = Self(1 << 5);
    /// `symbolOriginInfoKindIgnore`.
    pub(crate) const IGNORE: Self = Self(1 << 6);
    /// `symbolOriginInfoKindComputedPropertyName`.
    pub(crate) const COMPUTED_PROPERTY_NAME: Self = Self(1 << 7);

    /// `kind & other`.
    pub(crate) fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl std::ops::BitOr for SymbolOriginInfoKind {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

/// `type symbolOriginInfo struct`.
pub(crate) struct SymbolOriginInfo {
    /// `kind`.
    pub(crate) kind: SymbolOriginInfoKind,
    /// `isDefaultExport`.
    pub(crate) is_default_export: bool,
    /// `isFromPackageJson`.
    pub(crate) is_from_package_json: bool,
    /// `data` — `*symbolOriginInfoTypeOnlyAlias |
    /// *symbolOriginInfoComputedPropertyName |
    /// *symbolOriginInfoObjectLiteralMethod`.
    pub(crate) data: Option<SymbolOriginInfoData>,
}

/// `symbolOriginInfo.data` — the Go `any` payload.
pub(crate) enum SymbolOriginInfoData {
    /// `*symbolOriginInfoObjectLiteralMethod`.
    ObjectLiteralMethod(Box<SymbolOriginInfoObjectLiteralMethod>),
    /// `*symbolOriginInfoTypeOnlyAlias`.
    TypeOnlyAlias {
        /// `declaration *ast.TypeOnlyImportDeclaration`.
        declaration: NodeId,
    },
    /// `*symbolOriginInfoComputedPropertyName`.
    ComputedPropertyName {
        /// `symbolName`.
        symbol_name: String,
    },
}

impl SymbolOriginInfo {
    /// `(*symbolOriginInfo).symbolName`.
    pub(crate) fn symbol_name(&self) -> &str {
        match &self.data {
            Some(SymbolOriginInfoData::ComputedPropertyName { symbol_name }) => symbol_name,
            _ => panic!("symbolOriginInfo: unknown data type for symbolName()"),
        }
    }

    /// `(*symbolOriginInfo).asObjectLiteralMethod`.
    pub(crate) fn as_object_literal_method(&self) -> &SymbolOriginInfoObjectLiteralMethod {
        match &self.data {
            Some(SymbolOriginInfoData::ObjectLiteralMethod(m)) => m,
            _ => panic!("symbolOriginInfo: not an object literal method"),
        }
    }
}

/// `type symbolOriginInfoObjectLiteralMethod struct`.
pub(crate) struct SymbolOriginInfoObjectLiteralMethod {
    /// `insertText`.
    pub(crate) insert_text: String,
    /// `labelDetails`.
    pub(crate) label_details: Option<lsproto::CompletionItemLabelDetails>,
    /// `isSnippet`.
    pub(crate) is_snippet: bool,
}

/// `type completionSource string` — special values for `CompletionInfo['source']`
/// used to disambiguate completion items with the same `name`. (Each completion
/// item must have a unique name/source combination, because those two fields
/// comprise `CompletionEntryIdentifier` in `getCompletionEntryDetails`.)
///
/// When the completion item is an auto-import suggestion, the source is the
/// module specifier of the suggestion. To avoid collisions, the values here
/// should not be a module specifier we would ever generate for an auto-import.
pub(crate) type CompletionSource = &'static str;

/// `completionSource*` constants.
pub(crate) mod completion_source {
    /// `completionSourceThisProperty` — completions that require `this.` insertion text.
    pub(crate) const THIS_PROPERTY: &str = "ThisProperty/";
    /// `completionSourceClassMemberSnippet` — auto-import that comes attached to a class member snippet.
    pub(crate) const CLASS_MEMBER_SNIPPET: &str = "ClassMemberSnippet/";
    /// `completionSourceTypeOnlyAlias` — a type-only import that needs to be promoted
    /// in order to be used at the completion location.
    pub(crate) const TYPE_ONLY_ALIAS: &str = "TypeOnlyAlias/";
    /// `completionSourceObjectLiteralMethodSnippet` — auto-import that comes
    /// attached to an object literal method snippet.
    pub(crate) const OBJECT_LITERAL_METHOD_SNIPPET: &str = "ObjectLiteralMethodSnippet/";
    /// `completionSourceSwitchCases` — case completions for switch statements.
    pub(crate) const SWITCH_CASES: &str = "SwitchCases/";
    /// `completionSourceObjectLiteralMemberWithComma` — completions for an object literal expression.
    pub(crate) const OBJECT_LITERAL_MEMBER_WITH_COMMA: &str = "ObjectLiteralMemberWithComma/";
}

/// `type uniqueNamesMap` — value is false for global variables or completions
/// from external module exports, true otherwise.
pub(crate) type UniqueNamesMap = HashMap<String, bool>;

/// `type literalValue any` — `string | jsnum.Number | PseudoBigInt`.
#[derive(Clone)]
pub(crate) enum LiteralValue {
    /// `string`.
    Str(String),
    /// `jsnum.Number`.
    Number(tsc_jsnum::Number),
    /// `jsnum.PseudoBigInt`.
    PseudoBigInt(tsc_jsnum::PseudoBigInt),
}

/// `type globalsSearch int`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum GlobalsSearch {
    /// `globalsSearchContinue`.
    Continue,
    /// `globalsSearchSuccess`.
    Success,
    /// `globalsSearchFail`.
    Fail,
}

impl CompletionList {
    /// `(l *CompletionList) toLSP` — Go's nil `*CompletionList` receiver maps
    /// to `None` on `Option<CompletionList>`; callers do
    /// `list.as_ref().map(CompletionList::to_lsp)`.
    pub(crate) fn to_lsp(&self) -> lsproto::CompletionList {
        let items: Vec<lsproto::CompletionItem> = self
            .items
            .iter()
            .filter_map(|entry| entry.as_ref().map(|e| e.item.clone()))
            .collect();
        lsproto::CompletionList {
            is_incomplete: self.is_incomplete,
            item_defaults: self.item_defaults.clone(),
            apply_kind: self.apply_kind.clone(),
            items: Some(items),
        }
    }
}

impl LanguageService<'_> {
    /// `getCompletionsAtPosition`.
    fn get_completions_at_position_impl(
        &self,
        ctx: &Context,
        file: NodeId,
        position: TextPos,
        trigger_character: Option<&str>,
        include_symbols: bool,
    ) -> Result<Option<CompletionList>, Error> {
        let program = self.get_program();
        let previous_token = {
            let mut nodes = program.nodes_mut(file.file_index());
            get_relevant_tokens(&mut nodes, position, file).1
        };
        if let Some(trigger_character) = trigger_character {
            let (in_string, valid_trigger) = {
                let mut nodes = program.nodes_mut(file.file_index());
                (
                    crate::utilities::is_in_string(&mut nodes, file, position, previous_token),
                    is_valid_trigger(
                        &mut nodes,
                        file,
                        trigger_character,
                        previous_token,
                        position,
                    ),
                )
            };
            if !in_string && !valid_trigger {
                return Ok(None);
            }
        }

        if trigger_character == Some(" ") {
            // `isValidTrigger` ensures we are at `import |`
            if self
                .user_preferences()
                .completion_preferences
                .include_completions_for_import_statements
                .is_true()
            {
                return Ok(Some(CompletionList {
                    is_incomplete: true,
                    ..Default::default()
                }));
            }
            return Ok(None);
        }

        // PORT(deferred): `getJSDocSnippetCompletion` is sibling-owned
        // (`jsdoc_snippet.rs`).
        if let Some(js_doc_snippet_completion) =
            self.get_js_doc_snippet_completion(ctx, file, position)
        {
            return Ok(Some(js_doc_snippet_completion));
        }

        let compiler_options = program.options();

        // !!! see if incomplete completion list and continue or clean

        let (checker, done) = program.get_type_checker_for_file(ctx.clone(), file);

        let string_completions = self.get_string_literal_completions(
            ctx,
            file,
            position,
            previous_token,
            &checker,
            &compiler_options,
            include_symbols,
        )?;
        if let Some(string_completions) = string_completions {
            drop(checker);
            done();
            return Ok(Some(string_completions));
        }

        let label_completions = {
            let nodes = program.nodes(file.file_index());
            previous_token.is_some_and(|previous_token| {
                matches!(
                    nodes[previous_token].kind,
                    Kind::BreakKeyword | Kind::ContinueKeyword | Kind::Identifier
                ) && nodes[previous_token]
                    .parent
                    .is_some_and(|p| ast::is_break_or_continue_statement(&nodes[p]))
            })
        };
        if label_completions {
            let parent = {
                let nodes = program.nodes(file.file_index());
                nodes[previous_token.unwrap()].parent.unwrap()
            };
            let optional_replacement_span =
                self.get_optional_replacement_span(previous_token, file);
            drop(checker);
            done();
            return Ok(Some(self.get_label_completions_at_position(
                ctx,
                parent,
                file,
                position,
                optional_replacement_span,
            )));
        }

        let preferences = self.user_preferences();
        let data = {
            self.get_completion_data(
                ctx,
                &checker,
                file,
                position,
                preferences,
                false, /*forItemResolve*/
            )
        };
        let data = match data {
            Ok(data) => data,
            Err(err) => {
                drop(checker);
                done();
                return Err(err);
            }
        };
        let Some(data) = data else {
            drop(checker);
            done();
            return Ok(None);
        };

        match data {
            CompletionData::Data(mut data) => {
                let optional_replacement_span =
                    self.get_optional_replacement_span(data.location, file);
                let response = {
                    let mut c = checker.borrow_mut();
                    self.completion_info_from_data(
                        ctx,
                        &mut c,
                        file,
                        &compiler_options,
                        &mut data,
                        position,
                        optional_replacement_span,
                        include_symbols,
                    )
                };
                drop(checker);
                done();
                response
            }
            CompletionData::Keyword(data) => {
                let optional_replacement_span =
                    self.get_optional_replacement_span(previous_token, file);
                drop(checker);
                done();
                Ok(Some(self.specific_keyword_completion_info(
                    ctx,
                    position,
                    file,
                    data.keyword_completions,
                    data.is_new_identifier_location,
                    optional_replacement_span,
                )))
            }
            CompletionData::JSDocTagName => {
                // If the current position is a jsDoc tag name, only tag names should be provided for completion
                let mut items = get_js_doc_tag_name_completions();
                items.extend(get_js_doc_parameter_completions(
                    ctx,
                    file,
                    position,
                    &mut checker.borrow_mut(),
                    &compiler_options,
                    preferences,
                    true, /*tagNameOnly*/
                    &program,
                ));
                drop(checker);
                done();
                Ok(Some(
                    self.js_doc_completion_info(ctx, position, file, items),
                ))
            }
            CompletionData::JSDocTag => {
                // If the current position is a jsDoc tag, only tags should be provided for completion
                let mut items = get_js_doc_tag_completions();
                items.extend(get_js_doc_parameter_completions(
                    ctx,
                    file,
                    position,
                    &mut checker.borrow_mut(),
                    &compiler_options,
                    preferences,
                    false, /*tagNameOnly*/
                    &program,
                ));
                drop(checker);
                done();
                Ok(Some(
                    self.js_doc_completion_info(ctx, position, file, items),
                ))
            }
            CompletionData::JSDocParameterName { tag } => {
                let items = get_js_doc_parameter_name_completions(&program.arena_of(tag), tag);
                drop(checker);
                done();
                Ok(Some(
                    self.js_doc_completion_info(ctx, position, file, items),
                ))
            }
        }
    }

    /// `getCompletionData`. Go models most of the per-site analysis as
    /// closures mutating captured state; the port gathers that state on
    /// `CompletionDataBuilder` and turns each closure into a method.
    fn get_completion_data(
        &self,
        ctx: &Context,
        type_checker: &Rc<RefCell<Checker>>,
        file: NodeId,
        position: TextPos,
        preferences: &UserPreferences,
        for_item_resolve: bool,
    ) -> Result<Option<CompletionData>, Error> {
        let program = self.get_program();
        let in_checked_file = {
            let nodes = program.nodes(file.file_index());
            is_checked_file(&nodes, file, &program.options())
        };

        let mut current_token = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::get_token_at_position(&mut nodes, file, position)
        };

        let inside_comment = {
            let mut nodes = program.nodes_mut(file.file_index());
            crate::utilities::is_in_comment(&mut nodes, file, position, current_token)
        };

        let mut inside_jsdoc_tag_type_expression = false;
        let mut inside_jsdoc_import_tag = false;
        let mut is_in_snippet_scope = false;
        if inside_comment.is_some() {
            let text = {
                let nodes = program.nodes(file.file_index());
                nodes[file].as_source_file().text.clone()
            };
            let mut has_doc = {
                let mut nodes = program.nodes_mut(file.file_index());
                has_doc_comment(&mut nodes, file, position)
            };
            let _ = &mut has_doc;
            if has_doc {
                if position > 0 && text.as_bytes()[position as usize - 1] == b'@' {
                    // The current position is next to the '@' sign, when no tag name being provided yet.
                    // Provide a full list of tag names
                    return Ok(Some(CompletionData::JSDocTagName));
                } else {
                    // When completion is requested without "@", we will have check to make sure that
                    // there are no comments prefix the request position. We will only allow "*" and space.
                    // e.g
                    //   /** |c| /*
                    //
                    //   /**
                    //     |c|
                    //    */
                    //
                    //   /**
                    //    * |c|
                    //    */
                    //
                    //   /**
                    //    *         |c|
                    //    */
                    let line_start = {
                        let nodes = program.nodes(file.file_index());
                        tsc_format::get_line_start_position_for_position(position, file, &nodes)
                    };
                    let mut no_comment_prefix = true;
                    for r in text[line_start as usize..position as usize].chars() {
                        if !(tsc_stringutil::is_white_space_single_line(r)
                            || r == '*'
                            || r == '/'
                            || r == '('
                            || r == ')'
                            || r == '|')
                        {
                            no_comment_prefix = false;
                            break;
                        }
                    }
                    if no_comment_prefix {
                        return Ok(Some(CompletionData::JSDocTag));
                    }
                }
            }

            // Completion should work inside certain JSDoc tags. For example:
            //     /** @type {number | string} */
            // Completion should work in the brackets
            let tag = {
                let nodes = program.nodes(file.file_index());
                current_token.and_then(|t| get_js_doc_tag_at_position(&nodes, Some(t), position))
            };
            if let Some(tag) = tag {
                let tag_name = {
                    let nodes = program.nodes(file.file_index());
                    nodes[tag].tag_name()
                };
                {
                    let nodes = program.nodes(file.file_index());
                    if let Some(tag_name) = tag_name {
                        if nodes[tag_name].pos() <= position && position <= nodes[tag_name].end() {
                            return Ok(Some(CompletionData::JSDocTagName));
                        }
                    }
                }
                let is_jsdoc_import_tag = {
                    let nodes = program.nodes(file.file_index());
                    ast::is_js_doc_import_tag(&nodes[tag])
                };
                if is_jsdoc_import_tag {
                    inside_jsdoc_import_tag = true;
                } else {
                    let type_expression = {
                        let nodes = program.nodes(file.file_index());
                        try_get_type_expression_from_tag(&nodes, tag)
                    };
                    if let Some(type_expression) = type_expression {
                        current_token = {
                            let mut nodes = program.nodes_mut(file.file_index());
                            tsc_astnav::tokens::get_token_at_position(&mut nodes, file, position)
                        };
                        let use_as_type_location = {
                            let nodes = program.nodes(file.file_index());
                            current_token.is_none_or(|t| {
                                !ast::is_declaration_name(t, &nodes)
                                    && (nodes[t].parent.map(|p| nodes[p].kind)
                                        != Some(Kind::JSDocPropertyTag)
                                        || nodes[t].parent.and_then(|p| nodes[p].name()) != Some(t))
                            })
                        };
                        if use_as_type_location {
                            // Use as type location if inside tag's type expression
                            inside_jsdoc_tag_type_expression = {
                                let mut nodes = program.nodes_mut(file.file_index());
                                is_currently_editing_node(
                                    &mut nodes,
                                    type_expression,
                                    file,
                                    position,
                                )
                            };
                        }
                    }
                    let is_jsdoc_parameter_tag = {
                        let nodes = program.nodes(file.file_index());
                        ast::is_js_doc_parameter_tag(&nodes[tag])
                    };
                    if !inside_jsdoc_tag_type_expression && is_jsdoc_parameter_tag {
                        let name_is_missing_or_covers = {
                            let nodes = program.nodes(file.file_index());
                            let name = nodes[tag].name();
                            name.is_none_or(|name| {
                                ast::node_is_missing(Some(name), &nodes)
                                    || (nodes[name].pos() <= position
                                        && position <= nodes[name].end())
                            })
                        };
                        if name_is_missing_or_covers {
                            return Ok(Some(CompletionData::JSDocParameterName { tag }));
                        }
                    }
                }
            }

            if !inside_jsdoc_tag_type_expression && !inside_jsdoc_import_tag {
                // Proceed if the current position is in JSDoc tag expression; otherwise it is a normal
                // comment or the plain text part of a JSDoc comment, so no completion should be available
                return Ok(None);
            }
        }

        // The decision to provide completion depends on the contextToken, which is determined through the previousToken.
        // Note: 'previousToken' (and thus 'contextToken') can be undefined if we are the beginning of the file
        let is_js_only_location =
            !inside_jsdoc_tag_type_expression && !inside_jsdoc_import_tag && {
                let nodes = program.nodes(file.file_index());
                ast::is_source_file_js(nodes[file].as_source_file())
            };
        let (mut context_token, previous_token) = {
            let mut nodes = program.nodes_mut(file.file_index());
            get_relevant_tokens(&mut nodes, position, file)
        };

        // Find the node where completion is requested on.
        // Also determine whether we are trying to complete with members of that node
        // or attributes of a JSX tag.
        let mut node = current_token;
        let mut property_access_to_convert: Option<NodeId> = None;
        let mut is_right_of_dot = false;
        let mut is_right_of_question_dot = false;
        let mut is_right_of_open_tag = false;
        let mut is_starting_close_tag = false;
        let mut jsx_initializer = JsxInitializer::default();
        let mut is_jsx_identifier_expected = false;
        let mut import_statement_completion: Option<ImportStatementCompletionInfo> = None;
        let mut location = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::get_touching_property_name(&mut nodes, file, position)
        };
        let mut keyword_filters = KeywordCompletionFilters::NONE;
        let mut is_new_identifier_location = false;
        // !!! flags := CompletionInfoFlagsNone
        let mut default_commit_characters: Option<Vec<String>> = None;

        if let Some(ct) = context_token {
            let import_statement_completion_info =
                self.get_import_statement_completion_info(ct, file);
            if import_statement_completion_info.keyword_completion != Kind::Unknown {
                if import_statement_completion_info.is_keyword_only_completion {
                    return Ok(Some(CompletionData::Keyword(CompletionDataKeyword {
                        keyword_completions: vec![CompletionItem {
                            item: LspCompletionItem {
                                label: tsc_scanner::scanner::token_to_string(
                                    import_statement_completion_info.keyword_completion,
                                )
                                .to_string(),
                                kind: Some(lsproto::CompletionItemKind::Keyword),
                                sort_text: Some(sort_text::GLOBALS_OR_KEYWORDS.to_string()),
                                ..Default::default()
                            },
                            symbol: None,
                        }],
                        is_new_identifier_location: import_statement_completion_info
                            .is_new_identifier_location,
                    })));
                }
                keyword_filters = keyword_filters_from_syntax_kind(
                    import_statement_completion_info.keyword_completion,
                );
            }
            if import_statement_completion_info.replacement_span.is_some()
                && preferences
                    .completion_preferences
                    .include_completions_for_import_statements
                    .is_true()
            {
                // !!! flags |= CompletionInfoFlags::IsImportStatementCompletion
                is_new_identifier_location =
                    import_statement_completion_info.is_new_identifier_location;
                import_statement_completion = Some(import_statement_completion_info.clone());
            }
            // Bail out if this is a known invalid completion location.
            if import_statement_completion_info.replacement_span.is_none() {
                let blocker = is_completion_list_blocker(
                    ct,
                    previous_token,
                    location,
                    file,
                    position,
                    &mut type_checker.borrow_mut(),
                    &program,
                );
                if blocker {
                    if keyword_filters != KeywordCompletionFilters::NONE {
                        let is_new_identifier_location = {
                            let mut nodes = program.nodes_mut(file.file_index());
                            compute_commit_characters_and_is_new_identifier(
                                &mut nodes,
                                Some(ct),
                                file,
                                position,
                            )
                            .0
                        };
                        return Ok(Some(keyword_completion_data(
                            keyword_filters,
                            is_js_only_location,
                            is_new_identifier_location,
                        )));
                    }
                    return Ok(None);
                }
            }

            let parent = {
                let nodes = program.nodes(file.file_index());
                nodes[ct].parent
            };
            let (ct_kind, parent_kind) = {
                let nodes = program.nodes(file.file_index());
                (nodes[ct].kind, parent.map(|p| nodes[p].kind))
            };
            if ct_kind == Kind::DotToken || ct_kind == Kind::QuestionDotToken {
                is_right_of_dot = ct_kind == Kind::DotToken;
                is_right_of_question_dot = ct_kind == Kind::QuestionDotToken;
                match parent_kind {
                    Some(Kind::PropertyAccessExpression) => {
                        let parent = parent.expect("parent");
                        property_access_to_convert = Some(parent);
                        node = {
                            let nodes = program.nodes(file.file_index());
                            nodes[parent].expression()
                        };
                        let (left_most_missing, bail) = {
                            let mut nodes = program.nodes_mut(file.file_index());
                            let left_most_access_expression =
                                ast::get_leftmost_access_expression(parent, &nodes);
                            let node = node.expect("property access expression");
                            let missing =
                                ast::node_is_missing(Some(left_most_access_expression), &nodes);
                            let bail = !missing
                                && (ast::is_call_expression(&nodes[node])
                                    || ast::is_function_like(Some(node), &nodes))
                                && nodes[node].end() == nodes[ct].pos()
                                && tsc_lsutil::children::get_last_child(&mut nodes, node, file)
                                    .is_some_and(|last| nodes[last].kind != Kind::CloseParenToken);
                            (missing, bail)
                        };
                        let _ = left_most_missing;
                        if bail {
                            // This is likely dot from incorrectly parsed expression and user is starting to write spread
                            // eg: Math.min(./**/)
                            // const x = function (./**/) {}
                            // ({./**/})
                            return Ok(None);
                        }
                    }
                    Some(Kind::QualifiedName) => {
                        node = {
                            let nodes = program.nodes(file.file_index());
                            nodes[parent.expect("parent")].as_qualified_name().left
                        };
                    }
                    Some(Kind::ModuleDeclaration) => {
                        node = {
                            let nodes = program.nodes(file.file_index());
                            nodes[parent.expect("parent")].name()
                        };
                    }
                    Some(Kind::ImportType) => {
                        node = parent;
                    }
                    Some(Kind::MetaProperty) => {
                        let first_token = {
                            let mut nodes = program.nodes_mut(file.file_index());
                            tsc_lsutil::children::get_first_token(
                                &mut nodes,
                                parent.expect("parent"),
                                file,
                            )
                        };
                        let ft_kind = first_token.map(|t| {
                            let nodes = program.nodes(file.file_index());
                            nodes[t].kind
                        });
                        node = first_token;
                        if !matches!(ft_kind, Some(Kind::ImportKeyword) | Some(Kind::NewKeyword)) {
                            panic!("Unexpected token kind: {:?}", ft_kind);
                        }
                    }
                    _ => {
                        // There is nothing that precedes the dot, so this likely just a stray character
                        // or leading into a '...' token. Just bail out instead.
                        return Ok(None);
                    }
                }
            } else if import_statement_completion.is_none() {
                // <UI.Test /* completion position */ />
                // If the tagname is a property access expression, we will then walk up to the top most of property access expression.
                // Then, try to get a JSX container and its associated attributes type.
                let mut parent = parent;
                if let Some(p) = parent {
                    let nodes = program.nodes(file.file_index());
                    if nodes[p].kind == Kind::PropertyAccessExpression {
                        context_token = Some(p);
                        parent = nodes[p].parent;
                    }
                }

                // Fix location
                if let (Some(parent), Some(location_id)) = (parent, location) {
                    if parent == location_id {
                        let ct_kind = {
                            let nodes = program.nodes(file.file_index());
                            current_token.map(|t| nodes[t].kind)
                        };
                        let p_kind = {
                            let nodes = program.nodes(file.file_index());
                            nodes[parent].kind
                        };
                        match ct_kind {
                            Some(Kind::GreaterThanToken) => {
                                if p_kind == Kind::JsxElement || p_kind == Kind::JsxOpeningElement {
                                    location = current_token;
                                }
                            }
                            Some(Kind::LessThanSlashToken) => {
                                if p_kind == Kind::JsxSelfClosingElement {
                                    location = current_token;
                                }
                            }
                            _ => {}
                        }
                    }
                }

                match parent.map(|p| {
                    let nodes = program.nodes(file.file_index());
                    nodes[p].kind
                }) {
                    Some(Kind::JsxClosingElement) => {
                        let ct_is_less_than_slash = {
                            let nodes = program.nodes(file.file_index());
                            context_token.is_some_and(|t| nodes[t].kind == Kind::LessThanSlashToken)
                        };
                        if ct_is_less_than_slash {
                            is_starting_close_tag = true;
                            location = context_token;
                        }
                    }
                    Some(Kind::BinaryExpression)
                        if {
                            let nodes = program.nodes(file.file_index());
                            let parent = parent.unwrap();
                            binary_expression_may_be_open_tag(&nodes[parent], &nodes)
                        } =>
                    {
                        // fallthrough
                        let ct_is_less_than = {
                            let nodes = program.nodes(file.file_index());
                            context_token.is_some_and(|t| nodes[t].kind == Kind::LessThanToken)
                        };
                        is_jsx_identifier_expected = true;
                        if ct_is_less_than {
                            is_right_of_open_tag = true;
                            location = context_token;
                        }
                    }
                    Some(Kind::JsxSelfClosingElement)
                    | Some(Kind::JsxElement)
                    | Some(Kind::JsxOpeningElement) => {
                        let ct_is_less_than = {
                            let nodes = program.nodes(file.file_index());
                            context_token.is_some_and(|t| nodes[t].kind == Kind::LessThanToken)
                        };
                        is_jsx_identifier_expected = true;
                        if ct_is_less_than {
                            is_right_of_open_tag = true;
                            location = context_token;
                        }
                    }
                    Some(Kind::JsxExpression) | Some(Kind::JsxSpreadAttribute) => {
                        // First case is for `<div foo={true} [||] />` or `<div foo={true} [||] ></div>`,
                        // `parent` will be `{true}` and `previousToken` will be `}`.
                        // Second case is for `<div foo={true} t[||] ></div>`.
                        // Second case must not match for `<div foo={undefine[||]}></div>`.
                        let nodes = program.nodes(file.file_index());
                        if previous_token.is_some_and(|pt| {
                            nodes[pt].kind == Kind::CloseBraceToken
                                || (nodes[pt].kind == Kind::Identifier
                                    && nodes[pt].parent.map(|p| nodes[p].kind)
                                        == Some(Kind::JsxAttribute))
                        }) {
                            is_jsx_identifier_expected = true;
                        }
                    }
                    Some(Kind::JsxAttribute) => {
                        let parent = parent.unwrap();
                        let (initializer, prev_kind, prev_is_attr) = {
                            let nodes = program.nodes(file.file_index());
                            (
                                nodes[parent].initializer(),
                                previous_token.map(|pt| nodes[pt].kind),
                                previous_token.is_some_and(|pt| {
                                    nodes[pt].parent.map(|p| nodes[p].kind)
                                        == Some(Kind::JsxAttribute)
                                }),
                            )
                        };
                        // For `<div className="x" [||] ></div>`, `parent` will be JsxAttribute and `previousToken` will be its initializer.
                        if initializer == previous_token
                            && previous_token.is_some_and(|pt| {
                                let nodes = program.nodes(file.file_index());
                                nodes[pt].end() < position
                            })
                        {
                            is_jsx_identifier_expected = true;
                        } else {
                            match prev_kind {
                                Some(Kind::EqualsToken) => {
                                    jsx_initializer.is_initializer = true;
                                }
                                Some(Kind::Identifier) => {
                                    is_jsx_identifier_expected = true;
                                    // For `<div x=[|f/**/|]`, `parent` will be `x` and `previousToken.parent` will be `f` (which is its own JsxAttribute).
                                    // Note for `<div someBool f>` we don't want to treat this as a jsx inializer, instead it's the attribute name.
                                    let is_initializer_ident = {
                                        let mut nodes = program.nodes_mut(file.file_index());
                                        let prev = previous_token.unwrap();
                                        Some(parent) != nodes[prev].parent
                                            && nodes[parent].initializer().is_none()
                                            && tsc_astnav::tokens::find_child_of_kind(
                                                &mut nodes,
                                                file,
                                                parent,
                                                Kind::EqualsToken,
                                            )
                                            .is_some()
                                    };
                                    let _ = prev_is_attr;
                                    if is_initializer_ident {
                                        jsx_initializer.initializer = previous_token;
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let completion_kind = CompletionKind::None;
        let has_unresolved_auto_imports = false;

        let is_type_only_location = {
            let nodes = program.nodes(file.file_index());
            inside_jsdoc_tag_type_expression
                || inside_jsdoc_import_tag
                || (import_statement_completion.is_some()
                    && location
                        .and_then(|l| nodes[l].parent)
                        .is_some_and(|p| ast::is_type_only_import_or_export_declaration(p, &nodes)))
                || (!is_context_token_value_location(&nodes, context_token)
                    && (location.is_some_and(|l| ast::is_part_of_type_node(l, &nodes))
                        || is_context_token_type_location(&nodes, context_token)))
        };
        let mut builder = CompletionDataBuilder {
            l: self,
            ctx,
            checker: type_checker.clone(),
            program: program.clone(),
            file,
            position,
            preferences,
            for_item_resolve,
            in_checked_file,
            inside_jsdoc_tag_type_expression,
            inside_jsdoc_import_tag,
            is_in_snippet_scope,
            is_js_only_location,
            context_token,
            previous_token,
            node,
            property_access_to_convert,
            is_right_of_dot,
            is_right_of_question_dot,
            is_right_of_open_tag,
            is_starting_close_tag,
            jsx_initializer,
            is_jsx_identifier_expected,
            import_statement_completion,
            location,
            keyword_filters,
            is_new_identifier_location,
            default_commit_characters,
            completion_kind,
            has_unresolved_auto_imports,
            symbols: Vec::new(),
            auto_imports: Vec::new(),
            symbol_to_origin_info_map: HashMap::new(),
            symbol_to_sort_text_map: HashMap::new(),
            seen_property_symbols: Set::default(),
            is_type_only_location,
        };

        // `isPossiblyTypeArgumentPosition` needs the checker; run it outside
        // the struct literal (and outside any arena borrow).
        let is_context_token_value_location = {
            let nodes = program.nodes(file.file_index());
            is_context_token_value_location(&nodes, builder.context_token)
        };
        if !builder.is_type_only_location && !is_context_token_value_location {
            builder.is_type_only_location = is_possibly_type_argument_position(
                &program,
                builder.context_token,
                file,
                &mut type_checker.borrow_mut(),
            );
        }

        builder.finish()
    }
}

/// `getCompletionData`'s captured-state struct — see
/// [`LanguageService::get_completion_data`]. `checker` is an `Rc<RefCell>`
/// clone so that `&mut self` methods can take `checker.borrow_mut()` without
/// conflicting with the `self` borrow.
pub(crate) struct CompletionDataBuilder<'a, 'h> {
    /// `l *LanguageService`.
    pub(crate) l: &'a LanguageService<'h>,
    /// `ctx`.
    pub(crate) ctx: &'a Context,
    /// `typeChecker`.
    pub(crate) checker: Rc<RefCell<Checker>>,
    /// `l.GetProgram()`.
    pub(crate) program: Rc<Program>,
    /// `file`.
    pub(crate) file: NodeId,
    /// `position`.
    pub(crate) position: TextPos,
    /// `preferences`.
    pub(crate) preferences: &'a UserPreferences,
    /// `forItemResolve`.
    pub(crate) for_item_resolve: bool,
    /// `inCheckedFile`.
    pub(crate) in_checked_file: bool,
    /// `insideJSDocTagTypeExpression`.
    pub(crate) inside_jsdoc_tag_type_expression: bool,
    /// `insideJsDocImportTag`.
    pub(crate) inside_jsdoc_import_tag: bool,
    /// `isInSnippetScope`.
    pub(crate) is_in_snippet_scope: bool,
    /// `isJSOnlyLocation`.
    pub(crate) is_js_only_location: bool,
    /// `contextToken`.
    pub(crate) context_token: Option<NodeId>,
    /// `previousToken`.
    pub(crate) previous_token: Option<NodeId>,
    /// `node`.
    pub(crate) node: Option<NodeId>,
    /// `propertyAccessToConvert`.
    pub(crate) property_access_to_convert: Option<NodeId>,
    /// `isRightOfDot`.
    pub(crate) is_right_of_dot: bool,
    /// `isRightOfQuestionDot`.
    pub(crate) is_right_of_question_dot: bool,
    /// `isRightOfOpenTag`.
    pub(crate) is_right_of_open_tag: bool,
    /// `isStartingCloseTag`.
    pub(crate) is_starting_close_tag: bool,
    /// `jsxInitializer`.
    pub(crate) jsx_initializer: JsxInitializer,
    /// `isJsxIdentifierExpected`.
    pub(crate) is_jsx_identifier_expected: bool,
    /// `importStatementCompletion`.
    pub(crate) import_statement_completion: Option<ImportStatementCompletionInfo>,
    /// `location`.
    pub(crate) location: Option<NodeId>,
    /// `keywordFilters`.
    pub(crate) keyword_filters: KeywordCompletionFilters,
    /// `isNewIdentifierLocation`.
    pub(crate) is_new_identifier_location: bool,
    /// `defaultCommitCharacters` — `None` mirrors Go's nil slice (i.e. "not
    /// yet computed").
    pub(crate) default_commit_characters: Option<Vec<String>>,
    /// `completionKind`.
    pub(crate) completion_kind: CompletionKind,
    /// `hasUnresolvedAutoImports`.
    pub(crate) has_unresolved_auto_imports: bool,
    /// `symbols`.
    pub(crate) symbols: Vec<SymbolId>,
    /// `autoImports`.
    pub(crate) auto_imports: Vec<crate::autoimport::FixAndExport>,
    /// `symbolToOriginInfoMap` — keys are indexes into `symbols`.
    pub(crate) symbol_to_origin_info_map: HashMap<i32, SymbolOriginInfo>,
    /// `symbolToSortTextMap`.
    pub(crate) symbol_to_sort_text_map: HashMap<SymbolId, SortText>,
    /// `seenPropertySymbols`.
    pub(crate) seen_property_symbols: Set<SymbolId>,
    /// `isTypeOnlyLocation`.
    pub(crate) is_type_only_location: bool,
}

impl<'a, 'h> CompletionDataBuilder<'a, 'h> {
    /// Borrow the checker; helper for the `checker.borrow_mut()` dance.
    fn checker(&self) -> Rc<RefCell<Checker>> {
        self.checker.clone()
    }

    /// `checker.borrow_mut()` without cloning the `Rc` — the `RefMut`
    /// borrows through `self` so no temporary `Rc` is dropped early.
    fn checker_mut(&self) -> std::cell::RefMut<'_, Checker> {
        self.checker.borrow_mut()
    }

    /// `checker.borrow()` without cloning the `Rc`.
    fn checker_ref(&self) -> std::cell::Ref<'_, Checker> {
        self.checker.borrow()
    }

    /// Arena accessor for a node that may live in any file
    /// (`program.arena_of`).
    fn arena(&self, node: NodeId) -> std::rc::Rc<Vec<Node>> {
        self.program.arena_of(node)
    }

    fn nodes(&self) -> std::rc::Rc<Vec<Node>> {
        self.program.nodes(self.file.file_index())
    }

    fn nodes_mut(&self) -> tsc_ast::ArenaMut {
        self.program.nodes_mut(self.file.file_index())
    }

    /// `addSymbolOriginInfo`.
    fn add_symbol_origin_info(
        &mut self,
        symbol: SymbolId,
        insert_question_dot: bool,
        insert_await: bool,
    ) {
        let index = self.symbols.len() as i32 - 1;
        if insert_await && self.seen_property_symbols.add_if_absent(symbol) {
            self.symbol_to_origin_info_map.insert(
                index,
                SymbolOriginInfo::new(get_nullable_symbol_origin_info_kind(
                    SymbolOriginInfoKind::PROMISE,
                    insert_question_dot,
                )),
            );
        } else if insert_question_dot {
            self.symbol_to_origin_info_map
                .insert(index, SymbolOriginInfo::new(SymbolOriginInfoKind::NULLABLE));
        }
    }

    /// `addSymbolSortInfo`.
    fn add_symbol_sort_info(&mut self, symbol: SymbolId) {
        if is_static_property(&self.program, symbol) {
            self.symbol_to_sort_text_map
                .insert(symbol, sort_text::LOCAL_DECLARATION_PRIORITY.to_string());
        }
    }

    /// `addPropertySymbol`.
    fn add_property_symbol(
        &mut self,
        symbol: SymbolId,
        insert_await: bool,
        insert_question_dot: bool,
    ) {
        // For a computed property with an accessible name like `Symbol.iterator`,
        // we'll add a completion for the *name* `Symbol` instead of for the property.
        // If this is e.g. [Symbol.iterator], add a completion for `Symbol`.
        let declarations = self.program.symbols.get_ref(symbol)
            .declarations
            .clone();
        let computed_property_name = tsc_core::core::first_non_nil(&declarations, |decl| {
            let nodes = self.arena(*decl);
            ast::get_name_of_declaration(Some(*decl), &nodes)
                .filter(|name| nodes[*name].kind == Kind::ComputedPropertyName)
        });

        if let Some(computed_property_name) = computed_property_name {
            let expression = {
                let nodes = self.arena(computed_property_name);
                nodes[computed_property_name].expression()
            };
            let left_most_name = expression.and_then(|e| {
                let nodes = self.arena(e);
                get_left_most_name(&nodes, e)
            });
            // The completion is for `Symbol`, not `iterator`.
            let checker_rc = self.checker();
            let mut c = checker_rc.borrow_mut();
            let name_symbol = left_most_name.and_then(|name| c.get_symbol_at_location_api(name));
            // If this is nested like for `namespace N { export const sym = Symbol(); }`, we'll add the completion for `N`.
            let first_accessible_symbol = name_symbol.and_then(|name_symbol| {
                get_first_symbol_in_chain(&self.program, name_symbol, self.context_token, &mut c)
            });
            match first_accessible_symbol {
                Some(first_accessible_symbol)
                    if self
                        .seen_property_symbols
                        .add_if_absent(first_accessible_symbol) =>
                {
                    self.symbols.push(first_accessible_symbol);
                    self.symbol_to_sort_text_map.insert(
                        first_accessible_symbol,
                        sort_text::GLOBALS_OR_KEYWORDS.to_string(),
                    );
                    let (module_symbol, first_accessible_symbol_name) = {
                        let symbols = self.program.symbols.clone();
                        (
                            symbols[first_accessible_symbol.index()].parent,
                            symbols[first_accessible_symbol.index()].name.clone(),
                        )
                    };
                    let is_module_member = module_symbol.is_some_and(|module_symbol| {
                        tsc_checker::utilities::is_external_module_symbol(module_symbol, &c)
                            && c.try_get_member_in_module_exports_and_properties(
                                &first_accessible_symbol_name,
                                module_symbol,
                            ) == Some(first_accessible_symbol)
                    });
                    if !is_module_member {
                        let index = self.symbols.len() as i32 - 1;
                        self.symbol_to_origin_info_map.insert(
                            index,
                            SymbolOriginInfo::new(get_nullable_symbol_origin_info_kind(
                                SymbolOriginInfoKind::SYMBOL_MEMBER,
                                insert_question_dot,
                            )),
                        );
                    } else {
                        // !!! auto-import symbol
                    }
                }
                None => {
                    self.symbols.push(symbol);
                    self.add_symbol_origin_info(symbol, insert_question_dot, insert_await);
                    self.add_symbol_sort_info(symbol);
                }
                _ => {}
            }
        } else {
            self.symbols.push(symbol);
            self.add_symbol_origin_info(symbol, insert_question_dot, insert_await);
            self.add_symbol_sort_info(symbol);
        }
    }

    /// `addTypeProperties`.
    fn add_type_properties(&mut self, t: TypeId, insert_await: bool, insert_question_dot: bool) {
        let checker_rc = self.checker();
        {
            let mut c = checker_rc.borrow_mut();
            if c.get_string_index_type(t).is_some() {
                self.is_new_identifier_location = true;
                self.default_commit_characters = Some(Vec::new());
            }
            if self.is_right_of_question_dot && !c.get_call_signatures(t).is_empty() {
                self.is_new_identifier_location = true;
                if self.default_commit_characters.is_none() {
                    self.default_commit_characters = Some(
                        all_commit_characters()
                            .iter()
                            .map(|s| s.to_string())
                            .collect(),
                    ); // Only invalid commit character here would be `(`.
                }
            }
        }

        let node = self.node.expect("addTypeProperties: node");
        let property_access = {
            let nodes = self.nodes();
            if nodes[node].kind == Kind::ImportType {
                node
            } else {
                nodes[node].parent.expect("property access parent")
            }
        };

        let symbols_to_add: Vec<SymbolId> = {
            let mut c = checker_rc.borrow_mut();
            if self.in_checked_file {
                c.get_apparent_properties(t)
                    .into_iter()
                    .filter(|&symbol| {
                        c.is_valid_property_access_for_completions(property_access, t, symbol)
                    })
                    .collect()
            } else {
                // In javascript files, for union types, we don't just get the members that
                // the individual types have in common, we also include all the members that
                // each individual type has. This is because we're going to add all identifiers
                // anyways. So we might as well elevate the members that were at least part
                // of the individual types to a higher status since we know what they are.
                get_properties_for_completion(t, &mut c)
                    .into_iter()
                    .filter(|&symbol| {
                        c.is_valid_property_access_for_completions(property_access, t, symbol)
                    })
                    .collect()
            }
        };
        for symbol in symbols_to_add {
            if self.in_checked_file {
                self.add_property_symbol(symbol, false /*insertAwait*/, insert_question_dot);
            } else {
                self.symbols.push(symbol);
            }
        }

        if insert_await {
            let promise_symbols_to_add: Vec<SymbolId> = {
                let mut c = checker_rc.borrow_mut();
                match c.get_promised_type_of_promise(t) {
                    Some(promise_type) => c
                        .get_apparent_properties(promise_type)
                        .into_iter()
                        .filter(|&symbol| {
                            c.is_valid_property_access_for_completions(
                                property_access,
                                promise_type,
                                symbol,
                            )
                        })
                        .collect(),
                    None => Vec::new(),
                }
            };
            for symbol in promise_symbols_to_add {
                self.add_property_symbol(symbol, true /*insertAwait*/, insert_question_dot);
            }
        }
    }

    /// `getTypeScriptMemberSymbols` — right-of-dot member completion list.
    fn get_typescript_member_symbols(&mut self) {
        let checker_rc = self.checker();
        self.completion_kind = CompletionKind::PropertyAccess;

        let node = self.node.expect("getTypeScriptMemberSymbols: node");
        // Since this is qualified name check it's a type node location
        let (is_import_type, import_type_is_type_of, node_is_await_context) = {
            let nodes = self.nodes();
            (
                ast::is_literal_import_type_node(&nodes[node], &nodes),
                nodes[node].kind == Kind::ImportType
                    && nodes[node].as_import_type_node().is_type_of,
                nodes[node].flags.intersects(NodeFlags::AWAIT_CONTEXT),
            )
        };
        let is_type_location = (is_import_type && !import_type_is_type_of)
            || {
                let nodes = self.nodes();
                nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_part_of_type_node(p, &nodes))
            }
            || {
                let mut c = checker_rc.borrow_mut();
                is_possibly_type_argument_position(
                    &self.program,
                    self.context_token,
                    self.file,
                    &mut c,
                )
            };
        let is_rhs_of_import_declaration = {
            let nodes = self.nodes();
            crate::utilities::is_in_right_side_of_internal_import_equals_declaration(node, &nodes)
        };
        let (is_entity_name, is_property_access) = {
            let nodes = self.nodes();
            (
                ast::is_entity_name(&nodes[node]),
                ast::is_property_access_expression(&nodes[node]),
            )
        };
        if is_entity_name || is_import_type || is_property_access {
            let is_namespace_name = {
                let nodes = self.nodes();
                nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_module_declaration(&nodes[p]))
            };
            if is_namespace_name {
                self.is_new_identifier_location = true;
                self.default_commit_characters = Some(Vec::new());
            }
            let symbol = {
                let mut c = checker_rc.borrow_mut();
                c.get_symbol_at_location_api(node)
            };
            if let Some(symbol) = symbol {
                let symbol = checker_rc.borrow_mut().skip_alias(symbol);
                if let Some(symbol) = symbol {
                    let symbol_flags = self.program.symbols.get_ref(symbol).flags;
                    if symbol_flags.intersects(SymbolFlags::MODULE | SymbolFlags::ENUM) {
                        let value_access_node = if is_import_type {
                            node
                        } else {
                            let nodes = self.nodes();
                            nodes[node].parent.expect("value access node parent")
                        };
                        // Extract module or enum members
                        let exported_symbols = checker_rc
                            .borrow_mut()
                            .get_exports_of_module_as_array(symbol);
                        for exported_symbol in exported_symbols {
                            let is_valid_access = {
                                let mut c = checker_rc.borrow_mut();
                                let exported_flags =
                                    self.program.symbols.get_ref(exported_symbol).flags;
                                let exported_declarations = self.program.symbols.get_ref(exported_symbol)
                                .declarations
                                .clone();
                                if is_namespace_name {
                                    // At `namespace N.M/**/`, if this is the only declaration of `M`, don't include `M` as a completion.
                                    let nodes = self.nodes();
                                    exported_flags.intersects(SymbolFlags::NAMESPACE)
                                        && !tsc_core::core::every(
                                            &exported_declarations,
                                            |declaration| {
                                                nodes[*declaration].parent == nodes[node].parent
                                            },
                                        )
                                } else if is_rhs_of_import_declaration {
                                    // Any kind is allowed when dotting off namespace in internal import equals declaration
                                    symbol_can_be_referenced_at_type_location(
                                        exported_symbol,
                                        &mut c,
                                        &mut Set::default(),
                                        &self.program,
                                    ) || c.is_valid_property_access(
                                        value_access_node,
                                        &self.program.symbols.get_ref(exported_symbol)
                                            .name,
                                    )
                                } else if is_type_location || self.inside_jsdoc_tag_type_expression
                                {
                                    symbol_can_be_referenced_at_type_location(
                                        exported_symbol,
                                        &mut c,
                                        &mut Set::default(),
                                        &self.program,
                                    )
                                } else {
                                    c.is_valid_property_access(
                                        value_access_node,
                                        &self.program.symbols.get_ref(exported_symbol)
                                            .name,
                                    )
                                }
                            };
                            if is_valid_access {
                                self.symbols.push(exported_symbol);
                            }
                        }

                        // If the module is merged with a value, we must get the type of the class and add its properties (for inherited static methods).
                        let has_non_module_decl = {
                            let nodes = self.nodes();
                            let declarations = self.program.symbols.get_ref(symbol)
                                .declarations
                                .clone();
                            tsc_core::core::some(&declarations, |decl| {
                                let dnodes = self.arena(*decl);
                                !matches!(
                                    dnodes[*decl].kind,
                                    Kind::SourceFile
                                        | Kind::ModuleDeclaration
                                        | Kind::EnumDeclaration
                                )
                            })
                        };
                        if !is_type_location
                            && !self.inside_jsdoc_tag_type_expression
                            && has_non_module_decl
                        {
                            let (t, insert_question_dot) = {
                                let mut c = checker_rc.borrow_mut();
                                let sym_type = c.get_type_of_symbol_at_location(symbol, Some(node));
                                let t = c.get_non_optional_type(sym_type);
                                let mut t = t;
                                let mut insert_question_dot = false;
                                if c.is_nullable_type(t) {
                                    let can_correct_to_question_dot = self.is_right_of_dot
                                        && !self.is_right_of_question_dot
                                        && !self
                                            .preferences
                                            .completion_preferences
                                            .include_automatic_optional_chain_completions
                                            .is_false();
                                    if can_correct_to_question_dot || self.is_right_of_question_dot
                                    {
                                        t = c.get_non_nullable_type(t);
                                        if can_correct_to_question_dot {
                                            insert_question_dot = true;
                                        }
                                    }
                                }
                                (t, insert_question_dot)
                            };
                            self.add_type_properties(t, node_is_await_context, insert_question_dot);
                        }

                        return;
                    }
                }
            }
        }

        if !is_type_location || {
            let nodes = self.nodes();
            tsc_checker::utilities::is_in_type_query(node, &nodes)
        } {
            // microsoft/TypeScript#39946. Pulling on the type of a node inside of a function with a contextual `this` parameter can result in a circularity
            // if the `node` is part of the exprssion of a `yield` or `return`. This circularity doesn't exist at compile time because
            // we will check (and cache) the type of `this` *before* checking the type of the node.
            let mut c = checker_rc.borrow_mut();
            c.try_get_this_type_at_ex_exported(node, false /*includeGlobalThis*/, None);
            let node_type = c.get_type_at_location(node);
            let mut t = c.get_non_optional_type(node_type);

            if !is_type_location {
                let mut insert_question_dot = false;
                if c.is_nullable_type(t) {
                    let can_correct_to_question_dot = self.is_right_of_dot
                        && !self.is_right_of_question_dot
                        && !self
                            .preferences
                            .completion_preferences
                            .include_automatic_optional_chain_completions
                            .is_false();

                    if can_correct_to_question_dot || self.is_right_of_question_dot {
                        t = c.get_non_nullable_type(t);
                        if can_correct_to_question_dot {
                            insert_question_dot = true;
                        }
                    }
                }
                drop(c);
                self.add_type_properties(t, node_is_await_context, insert_question_dot);
            } else {
                let t = c.get_non_nullable_type(t);
                drop(c);
                self.add_type_properties(
                    t, false, /*insertAwait*/
                    false, /*insertQuestionDot*/
                );
            }
        }
    }

    /// `tryGetObjectTypeLiteralInTypeArgumentCompletionSymbols` — aggregates
    /// relevant symbols for completion in object literals in type argument
    /// positions.
    fn try_get_object_type_literal_in_type_argument_completion_symbols(&mut self) -> GlobalsSearch {
        let type_literal_node = {
            let nodes = self.nodes();
            self.context_token
                .and_then(|ct| try_get_type_literal_node(&nodes, ct))
        };
        let Some(type_literal_node) = type_literal_node else {
            return GlobalsSearch::Continue;
        };

        let (intersection_type_node, container_type_node) = {
            let nodes = self.nodes();
            let parent = nodes[type_literal_node].parent;
            let intersection = parent.filter(|p| ast::is_intersection_type_node(&nodes[*p]));
            let container = intersection.unwrap_or(type_literal_node);
            (intersection, container)
        };
        let _ = intersection_type_node;

        let container_expected_type = {
            let mut c = self.checker_mut();
            get_constraint_of_type_argument_property(
                &self.program,
                Some(container_type_node),
                &mut c,
            )
        };
        let Some(container_expected_type) = container_expected_type else {
            return GlobalsSearch::Continue;
        };

        let container_actual_type = {
            let mut c = self.checker_mut();
            c.get_type_from_type_node(container_type_node)
        };

        let (members, existing_members) = {
            let mut c = self.checker_mut();
            (
                get_properties_for_completion(container_expected_type, &mut c),
                get_properties_for_completion(container_actual_type, &mut c),
            )
        };

        let mut existing_member_names: Set<String> = Set::default();
        for member in &existing_members {
            existing_member_names.add(self.program.symbols.get_ref(*member).name.to_string());
        }

        let new_members: Vec<SymbolId> = members
            .into_iter()
            .filter(|member| {
                !existing_member_names.has(self.program.symbols.get_ref(*member).name.as_ref())
            })
            .collect();
        self.symbols.extend(new_members);

        self.completion_kind = CompletionKind::ObjectPropertyDeclaration;
        self.is_new_identifier_location = true;

        GlobalsSearch::Success
    }

    /// `tryGetObjectLikeCompletionSymbols` — aggregates relevant symbols for
    /// completion in object literals and object binding patterns. Relevant
    /// symbols are stored in `symbols`.
    fn try_get_object_like_completion_symbols(&mut self) -> GlobalsSearch {
        if self.context_token.is_some_and(|ct| {
            let nodes = self.nodes();
            nodes[ct].kind == Kind::DotDotDotToken
        }) {
            return GlobalsSearch::Continue;
        }
        let object_like_container = {
            let mut nodes = self.nodes_mut();
            self.context_token.and_then(|ct| {
                try_get_object_like_completion_container(&mut nodes, ct, self.position, self.file)
            })
        };
        let Some(object_like_container) = object_like_container else {
            return GlobalsSearch::Continue;
        };

        // We're looking up possible property names from contextual/inferred/declared type.
        self.completion_kind = CompletionKind::ObjectPropertyDeclaration;

        let mut type_members: Vec<SymbolId> = Vec::new();
        let mut existing_members: Vec<NodeId> = Vec::new();

        let container_kind = {
            let nodes = self.nodes();
            nodes[object_like_container].kind
        };
        if container_kind == Kind::ObjectLiteralExpression {
            let instantiated_type = {
                let mut c = self.checker_mut();
                try_get_object_literal_contextual_type(&self.program, object_like_container, &mut c)
            };

            // Check completions for Object property value shorthand
            let Some(instantiated_type) = instantiated_type else {
                let in_with = {
                    let nodes = self.nodes();
                    nodes[object_like_container]
                        .flags
                        .intersects(NodeFlags::IN_WITH_STATEMENT)
                };
                if in_with {
                    return GlobalsSearch::Fail;
                }
                return GlobalsSearch::Continue;
            };
            let (completions_type, is_new_identifier_location) = {
                let mut c = self.checker_mut();
                let completions_type = c.get_contextual_type_api(
                    object_like_container,
                    ContextFlags::IGNORE_NODE_INFERENCES,
                );
                let t = completions_type.unwrap_or(instantiated_type);
                let is_new_identifier_location =
                    c.get_string_index_type(t).is_some() || c.get_number_index_type(t).is_some();
                (completions_type, is_new_identifier_location)
            };
            self.is_new_identifier_location = is_new_identifier_location;
            {
                let mut c = self.checker_mut();
                type_members = get_properties_for_object_expression(
                    &self.program,
                    instantiated_type,
                    completions_type,
                    object_like_container,
                    &mut c,
                );
            }
            existing_members = {
                let nodes = self.nodes();
                nodes[object_like_container]
                    .properties()
                    .map(|p| p.to_vec())
                    .unwrap_or_default()
            };

            if type_members.is_empty() {
                // Edge case: If NumberIndexType exists
                let number_index_type = {
                    let mut c = self.checker_mut();
                    let t = completions_type.unwrap_or(instantiated_type);
                    c.get_number_index_type(t)
                };
                if number_index_type.is_none() {
                    return GlobalsSearch::Continue;
                }
            }
        } else {
            debug::assert_!(
                container_kind == Kind::ObjectBindingPattern,
                "Expected 'objectLikeContainer' to be an object binding pattern."
            );
            // We are *only* completing on properties from the type being destructured.
            self.is_new_identifier_location = false;
            let root_declaration = {
                let nodes = self.nodes();
                let parent = nodes[object_like_container].parent.expect("binding parent");
                ast::get_root_declaration(parent, &nodes)
            };
            {
                let nodes = self.nodes();
                debug::assert_!(
                    ast::is_variable_like(&nodes[root_declaration]),
                    "Root declaration is not variable-like."
                );
            }

            // We don't want to complete using the type acquired by the shape
            // of the binding pattern; we are only interested in types acquired
            // through type declaration or inference.
            // Also proceed if rootDeclaration is a parameter and if its containing function expression/arrow function is contextually typed -
            // type of parameter will flow in from the contextual type of the function.
            let mut can_get_type = {
                let nodes = self.nodes();
                let rd_parent = nodes[root_declaration].parent;
                let rd_grandparent = rd_parent.and_then(|p| nodes[p].parent);
                ast::has_initializer(&nodes[root_declaration])
                    || ast::get_type_annotation_node(&nodes[root_declaration]).is_some()
                    || rd_grandparent.map(|p| nodes[p].kind) == Some(Kind::ForOfStatement)
            };
            let root_kind = {
                let nodes = self.nodes();
                nodes[root_declaration].kind
            };
            if !can_get_type && root_kind == Kind::Parameter {
                let (rd_parent, rd_grandparent) = {
                    let nodes = self.nodes();
                    let rd_parent = nodes[root_declaration].parent;
                    (rd_parent, rd_parent.and_then(|p| nodes[p].parent))
                };
                let parent_is_expression = {
                    let nodes = self.nodes();
                    rd_parent.is_some_and(|p| ast::is_expression(&nodes[p], &nodes))
                };
                if parent_is_expression {
                    can_get_type = {
                        let mut c = self.checker_mut();
                        c.get_contextual_type_api(
                            rd_parent.expect("parameter parent"),
                            ContextFlags::NONE,
                        )
                        .is_some()
                    };
                } else {
                    let rd_parent_kind = {
                        let nodes = self.nodes();
                        rd_parent.map(|p| nodes[p].kind)
                    };
                    if matches!(
                        rd_parent_kind,
                        Some(Kind::MethodDeclaration) | Some(Kind::SetAccessor)
                    ) {
                        let grandparent_is_expression = {
                            let nodes = self.nodes();
                            rd_grandparent.is_some_and(|p| ast::is_expression(&nodes[p], &nodes))
                        };
                        if grandparent_is_expression {
                            can_get_type = {
                                let mut c = self.checker_mut();
                                c.get_contextual_type_api(
                                    rd_grandparent.expect("parameter grandparent"),
                                    ContextFlags::NONE,
                                )
                                .is_some()
                            };
                        }
                    }
                }
            }
            if can_get_type {
                let type_for_object = {
                    let mut c = self.checker_mut();
                    c.get_type_at_location(object_like_container)
                };
                // PORT: Rust's `getTypeAtLocation` never yields nil like Go's
                // can — `errorType` is the closest equivalent; treat it as
                // "no usable type" would be wrong, so keep the type.
                let filtered = {
                    let mut c = self.checker_mut();
                    let props = c.get_properties_of_type(type_for_object);
                    props
                        .into_iter()
                        .filter(|&property_symbol| {
                            c.is_property_accessible(
                                object_like_container,
                                false, /*isSuper*/
                                false, /*isWrite*/
                                type_for_object,
                                property_symbol,
                            )
                        })
                        .collect()
                };
                type_members = filtered;
                existing_members = {
                    let nodes = self.nodes();
                    nodes[object_like_container]
                        .elements()
                        .map(|e| e.to_vec())
                        .unwrap_or_default()
                };
            }
        }

        if !type_members.is_empty() {
            // Add filtered items to the completion list.
            let (filtered_members, spread_member_names) = {
                let checker_rc = self.checker();
                let mut c = checker_rc.borrow_mut();
                filter_object_members_list(
                    &self.program,
                    &type_members,
                    &existing_members,
                    self.file,
                    self.position,
                    &mut c,
                )
            };
            let filtered_members: Vec<SymbolId> = filtered_members;
            self.symbols.extend(filtered_members.iter().copied());

            // Set sort texts.
            for member in &filtered_members {
                let member = *member;
                let (member_name, member_is_optional) = {
                    let symbols = self.program.symbols.clone();
                    let m = &symbols[member.index()];
                    (m.name.clone(), m.flags.intersects(SymbolFlags::OPTIONAL))
                };
                if spread_member_names.has(member_name.as_ref()) {
                    self.symbol_to_sort_text_map.insert(
                        member,
                        sort_text::MEMBER_DECLARED_BY_SPREAD_ASSIGNMENT.to_string(),
                    );
                }
                if member_is_optional {
                    self.symbol_to_sort_text_map
                        .entry(member)
                        .or_insert_with(|| sort_text::OPTIONAL_MEMBER.to_string());
                }
                if container_kind == Kind::ObjectLiteralExpression
                    && self
                        .preferences
                        .completion_preferences
                        .include_completions_with_object_literal_method_snippets
                        .is_true()
                {
                    let (display_name, _) = {
                        let mut nodes = self.nodes_mut();
                        get_completion_entry_display_name_for_symbol(
                            &mut nodes,
                            self.file,
                            self.preferences,
                            member,
                            None, /*origin*/
                            CompletionKind::ObjectPropertyDeclaration,
                            false, /*isJsxIdentifierExpected*/
                            &self.checker.borrow(),
                            &self.program,
                        )
                    };
                    {
                        let display_name = display_name;
                        if !display_name.is_empty() {
                            let original_sort_text = self
                                .symbol_to_sort_text_map
                                .get(&member)
                                .cloned()
                                .unwrap_or_else(|| sort_text::LOCATION_PRIORITY.to_string());
                            self.symbol_to_sort_text_map.insert(
                                member,
                                object_literal_property_sort_text(
                                    &original_sort_text,
                                    &display_name,
                                ),
                            );
                        }
                    }
                }
            }

            if container_kind == Kind::ObjectLiteralExpression
                && self
                    .preferences
                    .completion_preferences
                    .include_completions_with_object_literal_method_snippets
                    .is_true()
            {
                for entry in self.collect_object_literal_method_symbols(
                    &filtered_members,
                    Some(object_like_container),
                ) {
                    self.symbol_to_origin_info_map
                        .insert(self.symbols.len() as i32, entry.origin);
                    self.symbols.push(entry.symbol);
                }
            }
        }

        GlobalsSearch::Success
    }

    /// `shouldOfferImportCompletions`.
    fn should_offer_import_completions(&self) -> bool {
        let file_name_is_dynamic = {
            let nodes = self.nodes();
            nodes[self.file].as_source_file().file_name().is_dynamic()
        };
        if file_name_is_dynamic {
            return false;
        }
        // If already typing an import statement, provide completions for it.
        if self.import_statement_completion.is_some() {
            return true;
        }
        // If not already a module, must have modules enabled.
        if self
            .preferences
            .completion_preferences
            .include_completions_for_module_exports
            .is_false()
        {
            return false;
        }
        // Always using ES modules in 6.0+
        true
    }

    /// `collectAutoImports` — mutates `auto_imports`.
    fn collect_auto_imports(&mut self) -> Result<(), Error> {
        // `completionItem/resolve` for auto-import completions should be resolved via the completion item data,
        // so we don't need to collect auto-import entries again.
        if self.for_item_resolve {
            return Ok(());
        }
        if !self.should_offer_import_completions() {
            return Ok(());
        }

        // import { type | -> token text should be blank
        let mut lower_case_token_text = String::new();
        let (usage_position, fidelity) = self.l.create_lsp_position(self.position, self.file);
        if !fidelity.is_exact() {
            return Ok(());
        }
        let mut usage_position = usage_position;
        if let Some(previous_token) = self.previous_token {
            let is_identifier = {
                let nodes = self.nodes();
                ast::is_identifier(&nodes[previous_token])
            };
            if is_identifier {
                let token_pos = {
                    let nodes = self.nodes();
                    tsc_scanner::scanner::get_token_pos_of_node(
                        previous_token,
                        nodes[self.file].as_source_file(),
                        false, /*includeJSDoc*/
                        &nodes,
                    )
                };
                let (pos, fidelity) = self.l.create_lsp_position(token_pos, self.file);
                if !fidelity.is_exact() {
                    return Ok(());
                }
                usage_position = pos;
                let is_context_token_and_import_completion = Some(previous_token)
                    == self.context_token
                    && self.import_statement_completion.is_some();
                if !is_context_token_and_import_completion {
                    let nodes = self.nodes();
                    lower_case_token_text = nodes[previous_token].text(&nodes).to_lowercase();
                }
            }
        }

        let view = self
            .l
            .get_prepared_auto_import_view(self.file, &self.checker)?;
        // PORT(deferred): `View::get_completions` is sibling-owned.
        self.auto_imports = view.get_completions(
            &lower_case_token_text,
            &usage_position,
            self.is_right_of_open_tag,
            self.is_type_only_location,
        );
        Ok(())
    }

    /// `tryGetImportCompletionSymbols`.
    fn try_get_import_completion_symbols(&mut self) -> Result<GlobalsSearch, Error> {
        if self.import_statement_completion.is_none() {
            return Ok(GlobalsSearch::Continue);
        }
        self.is_new_identifier_location = true;
        self.collect_auto_imports()?;
        Ok(GlobalsSearch::Success)
    }

    /// `tryGetImportOrExportClauseCompletionSymbols` — aggregates relevant
    /// symbols for completion in import clauses and export clauses whose
    /// declarations have a module specifier; for instance, symbols will be
    /// aggregated for
    ///
    /// ```text
    /// import { | } from "moduleName";
    /// export { a as foo, | } from "moduleName";
    /// ```
    ///
    /// but not for
    ///
    /// ```text
    /// export { | };
    /// ```
    /// Relevant symbols are stored in `symbols`.
    fn try_get_import_or_export_clause_completion_symbols(&mut self) -> GlobalsSearch {
        let Some(context_token) = self.context_token else {
            return GlobalsSearch::Continue;
        };

        // `import { |` or `import { a as 0, | }` or `import { type | }`
        let named_imports_or_exports = {
            let nodes = self.nodes();
            let ct_kind = nodes[context_token].kind;
            let ct_parent = nodes[context_token].parent;
            let ct_grandparent = ct_parent.and_then(|p| nodes[p].parent);
            if ct_kind == Kind::OpenBraceToken || ct_kind == Kind::CommaToken {
                ct_parent.filter(|p| is_named_imports_or_exports(&nodes[*p]))
            } else if is_type_keyword_token_or_identifier(&nodes[context_token], &nodes) {
                ct_grandparent.filter(|p| is_named_imports_or_exports(&nodes[*p]))
            } else {
                None
            }
        };
        let Some(named_imports_or_exports) = named_imports_or_exports else {
            return GlobalsSearch::Continue;
        };

        let needs_type_keyword = {
            let nodes = self.nodes();
            // We can at least offer `type` at `import { |`
            !is_type_keyword_token_or_identifier(&nodes[context_token], &nodes)
        };
        if needs_type_keyword {
            self.keyword_filters = KeywordCompletionFilters::TYPE_KEYWORD;
        }

        // try to show exported member for imported/re-exported module
        let module_specifier = {
            let nodes = self.nodes();
            let container = if nodes[named_imports_or_exports].kind == Kind::NamedImports {
                nodes[named_imports_or_exports]
                    .parent
                    .and_then(|p| nodes[p].parent)
            } else {
                nodes[named_imports_or_exports].parent
            };
            container.and_then(|c| nodes[c].module_specifier())
        };
        let Some(module_specifier) = module_specifier else {
            self.is_new_identifier_location = true;
            let nodes = self.nodes();
            if nodes[named_imports_or_exports].kind == Kind::NamedImports {
                return GlobalsSearch::Fail;
            }
            return GlobalsSearch::Continue;
        };

        let module_specifier_symbol = {
            let mut c = self.checker_mut();
            c.get_symbol_at_location_api(module_specifier)
        };
        if module_specifier_symbol.is_none() {
            self.is_new_identifier_location = true;
            return GlobalsSearch::Fail;
        }
        let module_specifier_symbol = module_specifier_symbol.unwrap();

        self.completion_kind = CompletionKind::MemberLike;
        self.is_new_identifier_location = false;
        let exports = {
            let mut c = self.checker_mut();
            c.get_exports_and_properties_of_module(module_specifier_symbol)
        };

        let mut existing: Set<String> = Set::default();
        {
            let nodes = self.nodes();
            for element in nodes[named_imports_or_exports]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default()
            {
                if is_currently_editing_node(
                    &mut self.nodes_mut(),
                    element,
                    self.file,
                    self.position,
                ) {
                    continue;
                }
                existing.add(
                    nodes[element]
                        .property_name_or_name()
                        .map(|n| nodes[n].text(&nodes).to_string())
                        .unwrap_or_default(),
                );
            }
        }
        let uniques: Vec<SymbolId> = exports
            .into_iter()
            .filter(|&symbol| {
                let symbols = self.program.symbols.clone();
                let name = ast::symbol_name(&symbols[symbol.index()], &self.nodes()).to_string();
                name != ast::INTERNAL_SYMBOL_NAME_DEFAULT && !existing.has(&name)
            })
            .collect();
        let uniques_len = uniques.len();
        self.symbols.extend(uniques);
        if uniques_len == 0 {
            // If there's nothing else to import, don't offer `type` either.
            self.keyword_filters = KeywordCompletionFilters::NONE;
        }
        GlobalsSearch::Success
    }

    /// `tryGetImportAttributesCompletionSymbols` —
    /// `import { x } from "foo" with { | }`.
    fn try_get_import_attributes_completion_symbols(&mut self) -> GlobalsSearch {
        let Some(context_token) = self.context_token else {
            return GlobalsSearch::Continue;
        };

        let import_attributes = {
            let nodes = self.nodes();
            let parent = nodes[context_token].parent;
            match nodes[context_token].kind {
                Kind::OpenBraceToken | Kind::CommaToken => parent,
                Kind::ColonToken => parent.and_then(|p| nodes[p].parent),
                _ => None,
            }
        };
        let Some(import_attributes) = import_attributes else {
            return GlobalsSearch::Continue;
        };
        {
            let nodes = self.nodes();
            if !ast::is_import_attributes(&nodes[import_attributes]) {
                return GlobalsSearch::Continue;
            }
        }

        let elements = {
            let nodes = self.nodes();
            nodes[import_attributes]
                .as_import_attributes()
                .attributes
                .as_ref()
                .map(|a| a.nodes.to_vec())
                .unwrap_or_default()
        };
        let mut existing: Set<String> = Set::default();
        {
            let nodes = self.nodes();
            for el in &elements {
                if let Some(name) = nodes[*el].as_import_attribute().name {
                    existing.add(nodes[name].text(&nodes).to_string());
                }
            }
        }
        let uniques: Vec<SymbolId> = {
            let mut c = self.checker_mut();
            let t = c.get_type_at_location(import_attributes);
            c.get_apparent_properties(t)
                .into_iter()
                .filter(|&symbol| {
                    let symbols = self.program.symbols.clone();
                    let name =
                        ast::symbol_name(&symbols[symbol.index()], &self.nodes()).to_string();
                    !existing.has(&name)
                })
                .collect()
        };
        self.symbols.extend(uniques);
        GlobalsSearch::Success
    }

    /// `tryGetLocalNamedExportCompletionSymbols` — adds local declarations for
    /// completions in named exports:
    ///   export { | };
    /// Does not check for the absence of a module specifier (`export {} from "./other"`)
    /// because `tryGetImportOrExportClauseCompletionSymbols` runs first and handles that,
    /// preventing this function from running.
    fn try_get_local_named_export_completion_symbols(&mut self) -> GlobalsSearch {
        let Some(context_token) = self.context_token else {
            return GlobalsSearch::Continue;
        };
        let named_exports = {
            let nodes = self.nodes();
            let ct_kind = nodes[context_token].kind;
            if ct_kind == Kind::OpenBraceToken || ct_kind == Kind::CommaToken {
                nodes[context_token]
                    .parent
                    .filter(|p| ast::is_named_exports(&nodes[*p]))
            } else {
                None
            }
        };
        let Some(named_exports) = named_exports else {
            return GlobalsSearch::Continue;
        };

        let locals_container = {
            let nodes = self.nodes();
            ast::find_ancestor(Some(named_exports), &nodes, &mut |n, _| {
                ast::is_source_file(n) || ast::is_module_declaration(n)
            })
        };
        let Some(locals_container) = locals_container else {
            return GlobalsSearch::Continue;
        };
        self.completion_kind = CompletionKind::None;
        self.is_new_identifier_location = false;
        let local_symbol = {
            let nodes = self.nodes();
            nodes[locals_container].symbol()
        };
        let local_exports: Vec<String> = local_symbol
            .map(|ls| {
                self.program.symbols.get_ref(ls)
                    .exports
                    .keys()
                    .map(|k| k.to_string())
                    .collect()
            })
            .unwrap_or_default();
        let locals: Vec<(String, SymbolId)> = {
            let nodes = self.nodes();
            nodes[locals_container]
                .locals()
                .map(|locals| {
                    locals
                        .entries()
                        .map(|(name, symbol)| (name.to_string(), *symbol))
                        .collect()
                })
                .unwrap_or_default()
        };
        for (name, symbol) in locals {
            self.symbols.push(symbol);
            if local_exports.iter().any(|n| *n == name) {
                self.symbol_to_sort_text_map
                    .insert(symbol, sort_text::OPTIONAL_MEMBER.to_string());
            }
        }

        GlobalsSearch::Success
    }

    /// `tryGetConstructorCompletion`.
    fn try_get_constructor_completion(&mut self) -> GlobalsSearch {
        if {
            let nodes = self.nodes();
            self.context_token
                .and_then(|ct| try_get_constructor_like_completion_container(&nodes, ct))
                .is_none()
        } {
            return GlobalsSearch::Continue;
        }

        // no members, only keywords
        self.completion_kind = CompletionKind::None;
        // Declaring new property/method/accessor
        self.is_new_identifier_location = true;
        // Has keywords for constructor parameter
        self.keyword_filters = KeywordCompletionFilters::CONSTRUCTOR_PARAMETER_KEYWORDS;
        GlobalsSearch::Success
    }

    /// `tryGetClassLikeCompletionSymbols` — aggregates relevant symbols for
    /// completion in class declaration; stored in `symbols`.
    fn try_get_class_like_completion_symbols(&mut self) -> GlobalsSearch {
        let decl = {
            let mut nodes = self.nodes_mut();
            try_get_object_type_declaration_completion_container(
                &mut nodes,
                self.file,
                self.context_token,
                self.location,
                self.position,
            )
        };
        let Some(decl) = decl else {
            return GlobalsSearch::Continue;
        };

        // We're looking up possible property names from parent type.
        self.completion_kind = CompletionKind::MemberLike;
        // Declaring new property/method/accessor
        self.is_new_identifier_location = true;
        let (ct_kind, decl_is_class_like) = {
            let nodes = self.nodes();
            (
                self.context_token.map(|ct| nodes[ct].kind),
                ast::is_class_like(Some(decl), &nodes),
            )
        };
        if ct_kind == Some(Kind::AsteriskToken) {
            self.keyword_filters = KeywordCompletionFilters::NONE;
        } else if decl_is_class_like {
            self.keyword_filters = KeywordCompletionFilters::CLASS_ELEMENT_KEYWORDS;
        } else {
            self.keyword_filters = KeywordCompletionFilters::INTERFACE_ELEMENT_KEYWORDS;
        }

        // If you're in an interface you don't want to repeat things from super-interface. So just stop here.
        if !decl_is_class_like {
            return GlobalsSearch::Success;
        }

        let class_element = {
            let nodes = self.nodes();
            let ct = self.context_token.expect("class context token");
            if nodes[ct].kind == Kind::SemicolonToken {
                nodes[ct].parent.and_then(|p| nodes[p].parent)
            } else {
                nodes[ct].parent
            }
        };
        let mut class_element_modifier_flags = ModifierFlags::NONE;
        {
            let nodes = self.nodes();
            if let Some(class_element) = class_element {
                if ast::is_class_element(&nodes[class_element]) {
                    class_element_modifier_flags = nodes[class_element].modifier_flags();
                }
            }
        }
        // If this is context token is not something we are editing now, consider if this would lead to be modifier.
        {
            let ct = self.context_token.expect("class context token");
            let ct_is_identifier = {
                let nodes = self.nodes();
                nodes[ct].kind == Kind::Identifier
            };
            if ct_is_identifier {
                let editing = {
                    let mut nodes = self.nodes_mut();
                    is_currently_editing_node(&mut nodes, ct, self.file, self.position)
                };
                if !editing {
                    let nodes = self.nodes();
                    match nodes[ct].text(&nodes).as_ref() {
                        "private" => class_element_modifier_flags |= ModifierFlags::PRIVATE,
                        "static" => class_element_modifier_flags |= ModifierFlags::STATIC,
                        "override" => class_element_modifier_flags |= ModifierFlags::OVERRIDE,
                        _ => {}
                    }
                }
            }
            let nodes = self.nodes();
            if let Some(class_element) = class_element {
                if ast::is_class_static_block_declaration(&nodes[class_element]) {
                    class_element_modifier_flags |= ModifierFlags::STATIC;
                }
            }
        }

        // No member list for private methods
        if !class_element_modifier_flags.intersects(ModifierFlags::PRIVATE) {
            // List of property symbols of base type that are not private and already implemented
            let base_type_nodes: Vec<NodeId> = {
                let nodes = self.nodes();
                if decl_is_class_like
                    && class_element_modifier_flags.intersects(ModifierFlags::OVERRIDE)
                {
                    tsc_core::core::single_element_slice(ast::get_class_extends_heritage_element(
                        &nodes[decl],
                        &nodes,
                    ))
                } else {
                    crate::utilities::get_all_super_type_nodes(&nodes[decl], &nodes)
                }
            };
            let mut base_symbols: Vec<SymbolId> = Vec::new();
            for base_type_node in base_type_nodes {
                let mut c = self.checker_mut();
                let t = c.get_type_at_location(base_type_node);
                if class_element_modifier_flags.intersects(ModifierFlags::STATIC) {
                    let t_symbol = c.types.get(t).symbol;
                    if let Some(t_symbol) = t_symbol {
                        let st = c.get_type_of_symbol_at_location(t_symbol, Some(decl));
                        base_symbols.extend(c.get_properties_of_type(st));
                    }
                } else {
                    // PORT: Go checks `t != nil` — TypeId is never nil here;
                    // the error type is the closest analogue and is simply
                    // carried through.
                    base_symbols.extend(c.get_properties_of_type(t));
                }
            }

            let members: Vec<NodeId> = {
                let nodes = self.nodes();
                nodes[decl]
                    .members()
                    .map(|m| m.to_vec())
                    .unwrap_or_default()
            };
            let filtered = {
                let checker = self.checker();
                let checker = checker.borrow();
                filter_class_members_list(
                    &self.program,
                    &base_symbols,
                    &members,
                    class_element_modifier_flags,
                    self.file,
                    self.position,
                    &checker,
                )
            };
            let start = self.symbols.len();
            self.symbols.extend(filtered);
            for index in start..self.symbols.len() {
                let symbol = self.symbols[index];
                let declaration = {
                    let symbols = self.program.symbols.clone();
                    symbols[symbol.index()].value_declaration
                };
                if let Some(declaration) = declaration {
                    let is_computed = {
                        let nodes = self.arena(declaration);
                        ast::is_class_element(&nodes[declaration])
                            && nodes[declaration]
                                .name()
                                .is_some_and(|name| ast::is_computed_property_name(&nodes[name]))
                    };
                    if is_computed {
                        let symbol_name = {
                            let mut c = self.checker_mut();
                            c.symbol_to_string(symbol)
                        };
                        let origin = SymbolOriginInfo {
                            kind: SymbolOriginInfoKind::COMPUTED_PROPERTY_NAME,
                            is_default_export: false,
                            is_from_package_json: false,
                            data: Some(SymbolOriginInfoData::ComputedPropertyName { symbol_name }),
                        };
                        self.symbol_to_origin_info_map.insert(index as i32, origin);
                    }
                }
            }
        }

        GlobalsSearch::Success
    }

    /// `tryGetJsxCompletionSymbols`.
    fn try_get_jsx_completion_symbols(&mut self) -> GlobalsSearch {
        let jsx_container = {
            let mut nodes = self.nodes_mut();
            self.context_token
                .and_then(|ct| try_get_containing_jsx_element(&mut nodes, ct, self.file))
        };
        let Some(jsx_container) = jsx_container else {
            return GlobalsSearch::Continue;
        };
        let attributes = {
            let nodes = self.nodes();
            nodes[jsx_container].attributes().expect("jsx attributes")
        };
        // Cursor is inside a JSX self-closing element or opening element.
        let attrs_type = {
            let mut c = self.checker_mut();
            c.get_contextual_type_api(attributes, ContextFlags::NONE)
        };
        let Some(attrs_type) = attrs_type else {
            return GlobalsSearch::Continue;
        };
        let completions_type = {
            let mut c = self.checker_mut();
            c.get_contextual_type_api(attributes, ContextFlags::IGNORE_NODE_INFERENCES)
        };
        let (filtered_symbols, spread_member_names) = {
            let mut c = self.checker_mut();
            let props = get_properties_for_object_expression(
                &self.program,
                attrs_type,
                completions_type,
                attributes,
                &mut c,
            );
            let attribute_properties = {
                let nodes = self.nodes();
                nodes[attributes]
                    .properties()
                    .map(|p| p.to_vec())
                    .unwrap_or_default()
            };
            filter_jsx_attributes(
                &self.program,
                &props,
                &attribute_properties,
                self.file,
                self.position,
                &mut c,
            )
        };

        self.symbols.extend(filtered_symbols.iter().copied());
        // Set sort texts.
        for &symbol in &filtered_symbols {
            let (symbol_name, symbol_is_optional) = {
                let symbols = self.program.symbols.clone();
                let s = &symbols[symbol.index()];
                (
                    ast::symbol_name(s, &self.nodes()).to_string(),
                    s.flags.intersects(SymbolFlags::OPTIONAL),
                )
            };
            if spread_member_names.has(&symbol_name) {
                self.symbol_to_sort_text_map.insert(
                    symbol,
                    sort_text::MEMBER_DECLARED_BY_SPREAD_ASSIGNMENT.to_string(),
                );
            }
            if symbol_is_optional {
                self.symbol_to_sort_text_map
                    .entry(symbol)
                    .or_insert_with(|| sort_text::OPTIONAL_MEMBER.to_string());
            }
        }

        self.completion_kind = CompletionKind::MemberLike;
        self.is_new_identifier_location = false;
        GlobalsSearch::Success
    }

    /// `getGlobalCompletions` — get all entities in the current scope.
    fn get_global_completions(&mut self) -> Result<GlobalsSearch, Error> {
        if {
            let nodes = self.nodes();
            self.context_token
                .and_then(|ct| try_get_function_like_body_completion_container(&nodes, Some(ct)))
                .is_some()
        } {
            self.keyword_filters = KeywordCompletionFilters::FUNCTION_LIKE_BODY_KEYWORDS;
        } else {
            self.keyword_filters = KeywordCompletionFilters::ALL;
        }
        // Get all entities in the current scope.
        self.completion_kind = CompletionKind::Global;
        let (is_new_identifier_location, default_commit_characters) = {
            let mut nodes = self.nodes_mut();
            compute_commit_characters_and_is_new_identifier(
                &mut nodes,
                self.context_token,
                self.file,
                self.position,
            )
        };
        self.is_new_identifier_location = is_new_identifier_location;
        self.default_commit_characters = Some(default_commit_characters);

        if self.previous_token != self.context_token && self.previous_token.is_none() {
            panic!("Expected 'contextToken' to be defined when different from 'previousToken'.")
        }

        // We need to find the node that will give us an appropriate scope to begin
        // aggregating completion candidates. This is achieved in 'getScopeNode'
        // by finding the first node that encompasses a position, accounting for whether a node
        // is "complete" to decide whether a position belongs to the node.
        //
        // However, at the end of an identifier, we are interested in the scope of the identifier
        // itself, but fall outside of the identifier. For instance:
        //
        //      xyz => x$
        //
        // the cursor is outside of both the 'x' and the arrow function 'xyz => x',
        // so 'xyz' is not returned in our results.
        //
        // We define 'adjustedPosition' so that we may appropriately account for
        // being at the end of an identifier. The intention is that if requesting completion
        // at the end of an identifier, it should be effectively equivalent to requesting completion
        // anywhere inside/at the beginning of the identifier. So in the previous case, the
        // 'adjustedPosition' will work as if requesting completion in the following:
        //
        //      xyz => $x
        //
        // If previousToken !== contextToken, then
        //   - 'contextToken' was adjusted to the token prior to 'previousToken'
        //      because we were at the end of an identifier.
        //   - 'previousToken' is defined.
        let adjusted_position = if self.previous_token != self.context_token {
            let mut nodes = self.nodes_mut();
            tsc_astnav::tokens::get_start_of_node(
                &mut nodes,
                self.file,
                self.previous_token.expect("previous token"),
                false, /*includeJSDoc*/
            )
        } else {
            self.position
        };

        let scope_node = {
            let mut nodes = self.nodes_mut();
            get_scope_node(&mut nodes, self.context_token, adjusted_position, self.file)
        };
        let scope_node = scope_node.unwrap_or(self.file);
        self.is_in_snippet_scope = {
            let nodes = self.nodes();
            is_snippet_scope(&nodes, scope_node)
        };

        let symbol_meanings = tsc_core::core::if_else(
            self.is_type_only_location,
            SymbolFlags::NONE,
            SymbolFlags::VALUE,
        ) | SymbolFlags::TYPE
            | SymbolFlags::NAMESPACE
            | SymbolFlags::ALIAS;
        let type_only_alias_needs_promotion = self.previous_token.is_some_and(|pt| {
            let nodes = self.arena(pt);
            !ast::is_valid_type_only_alias_use_site(pt, &nodes)
        });

        let scope_symbols = {
            let mut c = self.checker_mut();
            c.get_symbols_in_scope(scope_node, symbol_meanings)
        };
        let symbols_start = self.symbols.len();
        self.symbols.extend(scope_symbols);
        // `core.CheckEachDefined` — `Vec<SymbolId>` cannot contain nil.
        for index in symbols_start..self.symbols.len() {
            let symbol = self.symbols[index];
            let declarations = self.program.symbols.get_ref(symbol)
                .declarations
                .clone();
            let is_arguments = {
                let c = self.checker_ref();
                c.is_arguments_symbol(Some(symbol))
            };
            let has_decl_in_file = tsc_core::core::some(&declarations, |decl| {
                let nodes = self.arena(*decl);
                ast::get_source_file_of_node(Some(*decl), &nodes) == Some(self.file)
            });
            if !is_arguments && !has_decl_in_file {
                self.symbol_to_sort_text_map
                    .insert(symbol, sort_text::GLOBALS_OR_KEYWORDS.to_string());
            }
            let symbol_has_value_flag = self.program.symbols.get_ref(symbol)
                .flags
                .intersects(SymbolFlags::VALUE);
            if type_only_alias_needs_promotion && !symbol_has_value_flag {
                let type_only_alias_declaration = tsc_core::core::find(&declarations, |decl| {
                    let nodes = self.arena(*decl);
                    ast::is_type_only_import_or_export_declaration(*decl, &nodes)
                });
                if let Some(type_only_alias_declaration) = type_only_alias_declaration {
                    let origin = SymbolOriginInfo {
                        kind: SymbolOriginInfoKind::TYPE_ONLY_ALIAS,
                        is_default_export: false,
                        is_from_package_json: false,
                        data: Some(SymbolOriginInfoData::TypeOnlyAlias {
                            declaration: type_only_alias_declaration,
                        }),
                    };
                    self.symbol_to_origin_info_map.insert(index as i32, origin);
                }
            }
        }

        // Need to insert 'this.' before properties of `this` type.
        {
            let nodes = self.nodes();
            let scope_node_kind = nodes[scope_node].kind;
            drop(nodes);
            if scope_node_kind != Kind::SourceFile {
                let container = {
                    let nodes = self.nodes();
                    let parent = nodes[scope_node].parent;
                    tsc_core::core::if_else(
                        parent.is_some_and(|p| ast::is_class_like(Some(p), &nodes)),
                        Some(scope_node),
                        None,
                    )
                };
                let this_type = {
                    let mut c = self.checker_mut();
                    c.try_get_this_type_at_ex_exported(
                        scope_node, false, /*includeGlobalThis*/
                        container,
                    )
                };
                if let Some(this_type) = this_type {
                    let is_probably_global = {
                        let mut c = self.checker_mut();
                        is_probably_global_type(this_type, self.file, &mut c)
                    };
                    if !is_probably_global {
                        let props = {
                            let mut c = self.checker_mut();
                            get_properties_for_completion(this_type, &mut c)
                        };
                        for symbol in props {
                            self.symbols.push(symbol);
                            self.symbol_to_origin_info_map.insert(
                                self.symbols.len() as i32 - 1,
                                SymbolOriginInfo::new(SymbolOriginInfoKind::THIS_TYPE),
                            );
                            self.symbol_to_sort_text_map
                                .insert(symbol, sort_text::SUGGESTED_CLASS_MEMBERS.to_string());
                        }
                    }
                }
            }
        }

        self.collect_auto_imports()?;
        if self.is_type_only_location {
            let parent_is_assertion = {
                let nodes = self.nodes();
                self.context_token
                    .and_then(|ct| nodes[ct].parent)
                    .is_some_and(|p| ast::is_assertion_expression(&nodes[p]))
            };
            if parent_is_assertion {
                self.keyword_filters = KeywordCompletionFilters::TYPE_ASSERTION_KEYWORDS;
            } else {
                self.keyword_filters = KeywordCompletionFilters::TYPE_KEYWORDS;
            }
        }

        Ok(GlobalsSearch::Success)
    }

    /// `tryGetGlobalSymbols`.
    fn try_get_global_symbols(&mut self) -> Result<bool, Error> {
        // Order mirrors `globalSearchFuncs`.
        let mut result = GlobalsSearch::Continue;
        result = self.try_get_object_type_literal_in_type_argument_completion_symbols();
        if result == GlobalsSearch::Continue {
            result = self.try_get_object_like_completion_symbols();
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_import_completion_symbols()?;
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_import_or_export_clause_completion_symbols();
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_import_attributes_completion_symbols();
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_local_named_export_completion_symbols();
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_constructor_completion();
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_class_like_completion_symbols();
        }
        if result == GlobalsSearch::Continue {
            result = self.try_get_jsx_completion_symbols();
        }
        if result == GlobalsSearch::Continue {
            result = self.get_global_completions()?;
        }
        Ok(result == GlobalsSearch::Success)
    }

    /// The tail of `getCompletionData` — dispatches on the site kind and
    /// builds the `completionDataData` result.
    fn finish(mut self) -> Result<Option<CompletionData>, Error> {
        if self.is_right_of_dot || self.is_right_of_question_dot {
            self.get_typescript_member_symbols();
        } else if self.is_right_of_open_tag {
            let location = self.location.expect("isRightOfOpenTag location");
            self.symbols = {
                let mut c = self.checker_mut();
                c.get_jsx_intrinsic_tag_names_at(location)
            };
            // `core.CheckEachDefined` — `Vec<SymbolId>` cannot contain nil.
            if !self.try_get_global_symbols()? {
                // Go ignores a `globalsSearchFail` here (it only errors).
            }
            self.completion_kind = CompletionKind::Global;
            self.keyword_filters = KeywordCompletionFilters::NONE;
        } else if self.is_starting_close_tag {
            let tag_name = {
                let nodes = self.nodes();
                let ct = self
                    .context_token
                    .expect("isStartingCloseTag context token");
                nodes[nodes[ct].parent.expect("closing tag parent")]
                    .parent
                    .and_then(|p| nodes[p].as_jsx_element().opening_element)
                    .and_then(|oe| nodes[oe].tag_name())
            };
            let tag_symbol = tag_name.and_then(|tag_name| {
                self.checker()
                    .borrow_mut()
                    .get_symbol_at_location_api(tag_name)
            });
            if let Some(tag_symbol) = tag_symbol {
                self.symbols = vec![tag_symbol];
            }
            self.completion_kind = CompletionKind::Global;
            self.keyword_filters = KeywordCompletionFilters::NONE;
        } else {
            // For JavaScript or TypeScript, if we're not after a dot, then just try to get the
            // global symbols in scope.  These results should be valid for either language as
            // the set of symbols that can be referenced from this location.
            if !self.try_get_global_symbols()? {
                if self.keyword_filters != KeywordCompletionFilters::NONE {
                    return Ok(Some(keyword_completion_data(
                        self.keyword_filters,
                        self.is_js_only_location,
                        self.is_new_identifier_location,
                    )));
                }
                return Ok(None);
            }
        }

        let mut contextual_type_or_constraint: Option<TypeId> = None;
        if let Some(previous_token) = self.previous_token {
            contextual_type_or_constraint = {
                let mut c = self.checker_mut();
                get_contextual_type(
                    &self.program,
                    previous_token,
                    self.position,
                    self.file,
                    &mut c,
                )
            };
            if contextual_type_or_constraint.is_none() {
                contextual_type_or_constraint = {
                    let mut c = self.checker_mut();
                    get_constraint_of_type_argument_property(
                        &self.program,
                        Some(previous_token),
                        &mut c,
                    )
                };
            }
        }

        // exclude literal suggestions after <input type="text" [||] /> microsoft/TypeScript#51667) and after closing quote (microsoft/TypeScript#52675)
        // for strings getStringLiteralCompletions handles completions
        let is_literal_expected = !(self.previous_token.is_some_and(|pt| {
            let nodes = self.nodes();
            ast::is_string_literal_like(&nodes[pt])
        })) && !self.is_jsx_identifier_expected;
        let mut literals: Vec<LiteralValue> = Vec::new();
        if is_literal_expected {
            let types: Vec<TypeId> = match contextual_type_or_constraint {
                Some(t) => {
                    let guard = self.checker_ref();
                    if guard.types.get(t).is_union() {
                        guard.types.get(t).types().to_vec()
                    } else {
                        vec![t]
                    }
                }
                None => Vec::new(),
            };
            literals = tsc_core::core::map_non_nil(&types, |t| {
                let guard = self.checker_ref();
                let ty = guard.types.get(*t);
                if is_literal(*t, &guard) && !ty.is_enum_literal() {
                    ty.as_literal_type()
                        .value
                        .clone()
                        .and_then(LiteralValue::from_evaluator_value)
                } else {
                    None
                }
            });
        }

        let recommended_completion =
            if self.previous_token.is_some() && contextual_type_or_constraint.is_some() {
                get_recommended_completion(
                    &self.program,
                    self.previous_token.unwrap(),
                    contextual_type_or_constraint.unwrap(),
                    &mut self.checker.borrow_mut(),
                )
            } else {
                None
            };

        let default_commit_characters = match self.default_commit_characters {
            Some(cc) => cc,
            None => get_default_commit_characters(self.is_new_identifier_location),
        };

        Ok(Some(CompletionData::Data(Box::new(CompletionDataData {
            symbols: self.symbols,
            auto_imports: self.auto_imports,
            completion_kind: self.completion_kind,
            is_in_snippet_scope: self.is_in_snippet_scope,
            property_access_to_convert: self.property_access_to_convert,
            is_new_identifier_location: self.is_new_identifier_location,
            location: self.location,
            keyword_filters: self.keyword_filters,
            literals,
            symbol_to_origin_info_map: self.symbol_to_origin_info_map,
            symbol_to_sort_text_map: self.symbol_to_sort_text_map,
            recommended_completion,
            previous_token: self.previous_token,
            context_token: self.context_token,
            jsx_initializer: self.jsx_initializer,
            inside_jsdoc_tag_type_expression: self.inside_jsdoc_tag_type_expression,
            is_type_only_location: self.is_type_only_location,
            is_jsx_identifier_expected: self.is_jsx_identifier_expected,
            is_right_of_open_tag: self.is_right_of_open_tag,
            is_right_of_dot_or_question_dot: self.is_right_of_dot || self.is_right_of_question_dot,
            import_statement_completion: self.import_statement_completion,
            has_unresolved_auto_imports: self.has_unresolved_auto_imports,
            default_commit_characters,
        }))))
    }
}

impl LiteralValue {
    /// Mirrors the `string | jsnum.Number | PseudoBigInt` cases of Go's
    /// `literalValue`; `bool` never reaches here (`isLiteral` excludes it).
    fn from_evaluator_value(value: tsc_evaluator::Value) -> Option<Self> {
        match value {
            tsc_evaluator::Value::String(s) => Some(LiteralValue::Str(s)),
            tsc_evaluator::Value::Number(n) => Some(LiteralValue::Number(n)),
            tsc_evaluator::Value::PseudoBigInt(b) => Some(LiteralValue::PseudoBigInt(b)),
            tsc_evaluator::Value::Bool(_) => None,
        }
    }
}

impl SymbolOriginInfo {
    /// `&symbolOriginInfo{kind: kind}` — origin with only the kind set.
    pub(crate) fn new(kind: SymbolOriginInfoKind) -> Self {
        SymbolOriginInfo {
            kind,
            is_default_export: false,
            is_from_package_json: false,
            data: None,
        }
    }
}

/// `keywordCompletionData`.
fn keyword_completion_data(
    keyword_filters: KeywordCompletionFilters,
    is_js_only_location: bool,
    is_new_identifier_location: bool,
) -> CompletionData {
    CompletionData::Keyword(CompletionDataKeyword {
        keyword_completions: get_keyword_completions(keyword_filters, is_js_only_location),
        is_new_identifier_location,
    })
}

/// `getDefaultCommitCharacters`.
pub(crate) fn get_default_commit_characters(is_new_identifier_location: bool) -> Vec<String> {
    if is_new_identifier_location {
        Vec::new()
    } else {
        all_commit_characters()
            .iter()
            .map(|s| s.to_string())
            .collect()
    }
}

/// `getRelevantTokens`.
fn get_relevant_tokens(
    nodes: &mut Vec<Node>,
    position: TextPos,
    file: NodeId,
) -> (Option<NodeId>, Option<NodeId>) {
    let previous_token = tsc_astnav::tokens::find_preceding_token(nodes, file, position);
    if let Some(previous_token) = previous_token {
        if position <= nodes[previous_token].end()
            && (ast::is_member_name(&nodes[previous_token])
                || nodes[previous_token].kind.is_keyword_kind())
        {
            let context_token =
                tsc_astnav::tokens::find_preceding_token(nodes, file, nodes[previous_token].pos());
            return (context_token, Some(previous_token));
        }
    }
    (previous_token, previous_token)
}

/// `isValidTrigger`.
fn is_valid_trigger(
    nodes: &mut Vec<Node>,
    file: NodeId,
    trigger_character: &str,
    context_token: Option<NodeId>,
    position: TextPos,
) -> bool {
    match trigger_character {
        "." | "@" => true,
        "\"" | "'" | "`" => {
            // Only automatically bring up completions if this is an opening quote.
            context_token.is_some_and(|ct| {
                is_string_literal_or_template(&nodes[ct])
                    && position
                        == tsc_astnav::tokens::get_start_of_node(
                            nodes, file, ct, false, /*includeJSDoc*/
                        ) + 1
            })
        }
        "#" => context_token.is_some_and(|ct| {
            ast::is_private_identifier(&nodes[ct]) && ast::get_containing_class(ct, nodes).is_some()
        }),
        "<" => {
            // Opening JSX tag
            context_token.is_some_and(|ct| {
                nodes[ct].kind == Kind::LessThanToken
                    && (nodes[ct]
                        .parent
                        .is_none_or(|p| !ast::is_binary_expression(&nodes[p]))
                        || nodes[ct]
                            .parent
                            .is_some_and(|p| binary_expression_may_be_open_tag(&nodes[p], nodes)))
            })
        }
        "/" => {
            let Some(context_token) = context_token else {
                return false;
            };
            if ast::is_string_literal_like(&nodes[context_token]) {
                return ast::try_get_import_from_module_specifier(context_token, nodes).is_some();
            }
            nodes[context_token].kind == Kind::LessThanSlashToken
                && nodes[context_token]
                    .parent
                    .is_some_and(|p| ast::is_jsx_closing_element(&nodes[p]))
        }
        " " => context_token.is_some_and(|ct| {
            nodes[ct].kind == Kind::ImportKeyword
                && nodes[ct]
                    .parent
                    .is_some_and(|p| nodes[p].kind == Kind::SourceFile)
        }),
        "*" => crate::jsdoc_snippet::is_potentially_valid_jsdoc_snippet_completion_position(
            nodes, file, position,
        ),
        _ => panic!("Unknown trigger character: {trigger_character}"),
    }
}

/// `isStringLiteralOrTemplate`.
fn is_string_literal_or_template(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::StringLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateExpression
            | Kind::TaggedTemplateExpression
    )
}

/// `binaryExpressionMayBeOpenTag`.
fn binary_expression_may_be_open_tag(binary_expression: &Node, nodes: &[Node]) -> bool {
    let _ = nodes;
    ast::node_is_missing(binary_expression.as_binary_expression().left, nodes)
}

/// `isCheckedFile`.
fn is_checked_file(
    nodes: &[Node],
    file: NodeId,
    compiler_options: &tsc_core::options_generated::CompilerOptions,
) -> bool {
    !ast::is_source_file_js(nodes[file].as_source_file())
        || ast::is_check_js_enabled_for_file(nodes[file].as_source_file(), compiler_options)
}

/// `isContextTokenValueLocation`.
fn is_context_token_value_location(nodes: &[Node], context_token: Option<NodeId>) -> bool {
    context_token.is_some_and(|context_token| {
        let parent = nodes[context_token].parent;
        let parent_kind = parent.map(|p| nodes[p].kind);
        (nodes[context_token].kind == Kind::TypeOfKeyword
            && (parent_kind == Some(Kind::TypeQuery)
                || parent.is_some_and(|p| ast::is_type_of_expression(&nodes[p]))))
            || (nodes[context_token].kind == Kind::AssertsKeyword
                && parent_kind == Some(Kind::TypePredicate))
    })
}

/// `isPossiblyTypeArgumentPosition`.
fn is_possibly_type_argument_position(
    program: &Program,
    token: Option<NodeId>,
    source_file: NodeId,
    type_checker: &mut Checker,
) -> bool {
    let Some(token) = token else {
        return false;
    };
    let info = {
        let mut nodes = program.nodes_mut(source_file.file_index());
        crate::utilities::get_possible_type_arguments_info(&mut nodes, token, source_file)
    };
    let Some(info) = info else {
        return false;
    };
    let is_part_of_type_node = {
        let nodes = program.arena_of(info.called);
        ast::is_part_of_type_node(info.called, &nodes)
    };
    is_part_of_type_node
        || !crate::utilities::get_possible_generic_signatures(
            info.called,
            info.n_type_arguments,
            type_checker,
        )
        .is_empty()
        || is_possibly_type_argument_position(program, Some(info.called), source_file, type_checker)
}

/// `isContextTokenTypeLocation`.
fn is_context_token_type_location(nodes: &[Node], context_token: Option<NodeId>) -> bool {
    if let Some(context_token) = context_token {
        let parent_kind = nodes[context_token].parent.map(|p| nodes[p].kind);
        match nodes[context_token].kind {
            Kind::ColonToken => {
                return matches!(
                    parent_kind,
                    Some(Kind::PropertyDeclaration)
                        | Some(Kind::PropertySignature)
                        | Some(Kind::Parameter)
                        | Some(Kind::VariableDeclaration)
                ) || parent_kind.is_some_and(|k| ast::is_function_like_kind(k));
            }
            Kind::EqualsToken => {
                return matches!(
                    parent_kind,
                    Some(Kind::TypeAliasDeclaration) | Some(Kind::TypeParameter)
                );
            }
            Kind::AsKeyword => return parent_kind == Some(Kind::AsExpression),
            Kind::LessThanToken => {
                return matches!(
                    parent_kind,
                    Some(Kind::TypeReference) | Some(Kind::TypeAssertionExpression)
                );
            }
            Kind::ExtendsKeyword => return parent_kind == Some(Kind::TypeParameter),
            Kind::SatisfiesKeyword => return parent_kind == Some(Kind::SatisfiesExpression),
            Kind::OpenBracketToken | Kind::CommaToken => {
                return parent_kind == Some(Kind::TupleType);
            }
            _ => {}
        }
    }
    false
}

/// `symbolCanBeReferencedAtTypeLocation` — true if symbol is a type or a
/// module containing at least one type.
fn symbol_can_be_referenced_at_type_location(
    symbol: SymbolId,
    type_checker: &mut Checker,
    seen_modules: &mut Set<SymbolId>,
    program: &Program,
) -> bool {
    // Since an alias can be merged with a local declaration, we need to test both the alias and its target.
    // This code used to just test the result of `skipAlias`, but that would ignore any locally introduced meanings.
    non_alias_can_be_referenced_at_type_location(symbol, type_checker, seen_modules, program) || {
        let export_symbol = program.symbols.get_ref(symbol)
            .export_symbol
            .unwrap_or(symbol);
        type_checker
            .skip_alias(export_symbol)
            .is_some_and(|aliased| {
                non_alias_can_be_referenced_at_type_location(
                    aliased,
                    type_checker,
                    seen_modules,
                    program,
                )
            })
    }
}

/// `nonAliasCanBeReferencedAtTypeLocation`.
fn non_alias_can_be_referenced_at_type_location(
    symbol: SymbolId,
    type_checker: &mut Checker,
    seen_modules: &mut Set<SymbolId>,
    program: &Program,
) -> bool {
    let flags = program.symbols.get_ref(symbol).flags;
    if flags.intersects(SymbolFlags::TYPE) || type_checker.is_unknown_symbol(Some(symbol)) {
        return true;
    }
    flags.intersects(SymbolFlags::MODULE) && seen_modules.add_if_absent(symbol) && {
        let exports = type_checker.get_exports_of_module_as_array(symbol);
        exports.into_iter().any(|e| {
            symbol_can_be_referenced_at_type_location(e, type_checker, seen_modules, program)
        })
    }
}

/// `getPropertiesForCompletion` — gets all properties on a type, but if that
/// type is a union of several types, excludes array-like types or
/// callable/constructable types.
pub(crate) fn get_properties_for_completion(
    t: TypeId,
    type_checker: &mut Checker,
) -> Vec<SymbolId> {
    let types: Option<Vec<TypeId>> = {
        let guard = &*type_checker;
        let ty = guard.types.get(t);
        if ty.is_union() {
            Some(ty.types().to_vec())
        } else {
            None
        }
    };
    match types {
        Some(types) => type_checker.get_all_possible_properties_of_types(&types),
        None => type_checker.get_apparent_properties(t),
    }
}

/// `getLeftMostName` — given `a.b.c`, returns `a`.
fn get_left_most_name(nodes: &[Node], e: NodeId) -> Option<NodeId> {
    if ast::is_identifier(&nodes[e]) {
        Some(e)
    } else if ast::is_property_access_expression(&nodes[e]) {
        nodes[e]
            .expression()
            .and_then(|expr| get_left_most_name(nodes, expr))
    } else {
        None
    }
}

/// `getFirstSymbolInChain`.
fn get_first_symbol_in_chain(
    program: &Program,
    symbol: SymbolId,
    enclosing_declaration: Option<NodeId>,
    type_checker: &mut Checker,
) -> Option<SymbolId> {
    let chain = type_checker.get_accessible_symbol_chain_exported(
        Some(symbol),
        enclosing_declaration,
        SymbolFlags::ALL, /*meaning*/
        false,            /*useOnlyExternalAliasing*/
        None,
    );
    if let Some(first) = chain.first() {
        return Some(*first);
    }
    let parent = program.symbols.get_ref(symbol).parent;
    if let Some(parent) = parent {
        if is_module_symbol(program, parent) {
            return Some(symbol);
        }
        return get_first_symbol_in_chain(program, parent, enclosing_declaration, type_checker);
    }
    None
}

/// `isModuleSymbol`.
fn is_module_symbol(program: &Program, symbol: SymbolId) -> bool {
    let declarations = program.symbols.get_ref(symbol)
        .declarations
        .clone();
    tsc_core::core::some(&declarations, |decl| {
        let nodes = program.arena_of(*decl);
        nodes[*decl].kind == Kind::SourceFile
    })
}

/// `getNullableSymbolOriginInfoKind`.
fn get_nullable_symbol_origin_info_kind(
    kind: SymbolOriginInfoKind,
    insert_question_dot: bool,
) -> SymbolOriginInfoKind {
    if insert_question_dot {
        kind | SymbolOriginInfoKind::NULLABLE
    } else {
        kind
    }
}

/// `isStaticProperty`.
fn is_static_property(program: &Program, symbol: SymbolId) -> bool {
    let value_declaration = program.symbols.get_ref(symbol).value_declaration;
    value_declaration.is_some_and(|vd| {
        let nodes = program.arena_of(vd);
        nodes[vd].modifier_flags().intersects(ModifierFlags::STATIC)
            && nodes[vd]
                .parent
                .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
    })
}

/// `getContextualTypeForConditionalExpression` — handles completion within a
/// conditional expression (ternary operator) by using the parent expression
/// to find the contextual type.
fn get_contextual_type_for_conditional_expression(
    program: &Program,
    conditional_expr: NodeId,
    position: TextPos,
    file: NodeId,
    type_checker: &mut Checker,
) -> Option<TypeId> {
    let arg_info = {
        let mut nodes = program.nodes_mut(file.file_index());
        get_argument_info_for_completions(
            &mut nodes,
            conditional_expr,
            position,
            file,
            type_checker,
        )
    };
    if let Some(arg_info) = arg_info {
        return type_checker.get_contextual_type_for_argument_at_index(
            arg_info.invocation,
            arg_info.argument_index as i32,
        );
    }
    // Fall through to regular contextual type logic if not in an argument
    let contextual_type = type_checker
        .get_contextual_type_api(conditional_expr, ContextFlags::IGNORE_NODE_INFERENCES);
    if contextual_type.is_some() {
        return contextual_type;
    }
    type_checker.get_contextual_type_api(conditional_expr, ContextFlags::NONE)
}

/// `getContextualType`.
fn get_contextual_type(
    program: &Program,
    previous_token: NodeId,
    position: TextPos,
    file: NodeId,
    type_checker: &mut Checker,
) -> Option<TypeId> {
    let (previous_kind, parent, parent_kind) = {
        let nodes = program.nodes(file.file_index());
        let parent = nodes[previous_token].parent;
        (
            nodes[previous_token].kind,
            parent,
            parent.map(|p| nodes[p].kind),
        )
    };
    match previous_kind {
        Kind::Identifier => {
            return crate::utilities::get_contextual_type_from_parent(
                previous_token,
                type_checker,
                ContextFlags::NONE,
            );
        }
        Kind::EqualsToken => {
            return match parent_kind {
                Some(Kind::VariableDeclaration) => {
                    let initializer = {
                        let nodes = program.nodes(file.file_index());
                        nodes[parent.expect("parent")].initializer()
                    };
                    initializer
                        .and_then(|i| type_checker.get_contextual_type_api(i, ContextFlags::NONE))
                }
                Some(Kind::BinaryExpression) => {
                    let left = {
                        let nodes = program.nodes(file.file_index());
                        nodes[parent.expect("parent")].as_binary_expression().left
                    };
                    left.map(|l| type_checker.get_type_at_location(l))
                }
                Some(Kind::JsxAttribute) => {
                    type_checker.get_contextual_type_for_jsx_attribute_api(parent.expect("parent"))
                }
                _ => None,
            };
        }
        Kind::NewKeyword => {
            return parent
                .and_then(|p| type_checker.get_contextual_type_api(p, ContextFlags::NONE));
        }
        Kind::CaseKeyword => {
            if let Some(case_clause) =
                parent.filter(|p| ast::is_case_clause(&program.arena_of(*p)[*p]))
            {
                return Some(get_switched_type(case_clause, type_checker));
            }
            return None;
        }
        Kind::OpenBraceToken => {
            let is_jsx_expression_with_non_element_parent = {
                let nodes = program.nodes(file.file_index());
                let parent = parent.expect("parent");
                let pp = nodes[parent].parent;
                ast::is_jsx_expression(&nodes[parent])
                    && pp.is_some_and(|pp| {
                        !ast::is_jsx_element(&nodes[pp]) && !ast::is_jsx_fragment(&nodes[pp])
                    })
            };
            if is_jsx_expression_with_non_element_parent {
                let pp = {
                    let nodes = program.nodes(file.file_index());
                    nodes[parent.expect("parent")].parent.expect("jsx parent")
                };
                return type_checker.get_contextual_type_for_jsx_attribute_api(pp);
            }
            return None;
        }
        Kind::OpenBracketToken => {
            // When completing after `[` in an array literal (e.g., `[/*here*/]`),
            // we should provide contextual type for the first element
            if parent.is_some_and(|p| {
                let nodes = program.nodes(file.file_index());
                ast::is_array_literal_expression(&nodes[p])
            }) {
                let parent = parent.unwrap();
                let contextual_array_type =
                    type_checker.get_contextual_type_api(parent, ContextFlags::NONE);
                if contextual_array_type.is_some() {
                    // Get the type for the first element (index 0)
                    return type_checker.get_contextual_type_for_array_literal_at_position(
                        contextual_array_type,
                        parent,
                        position as i64,
                    );
                }
            }
            return None;
        }
        Kind::CloseBracketToken => {
            // When completing after `]` (e.g., `[x]/*here*/`), we should not provide a contextual type
            // for the closing bracket token itself. Without this case, CloseBracketToken would fall through
            // to the default case, and if the parent is an array literal, GetContextualType would try to
            // find the token's index in the array elements (returning -1), leading to an out-of-bounds panic
            // in getContextualTypeForElementExpression.
            return None;
        }
        Kind::QuestionToken => {
            // When completing after `?` in a ternary conditional (e.g., `foo(a ? /*here*/)`),
            // we need to look at the parent conditional expression to find the contextual type.
            if parent.is_some_and(|p| {
                let nodes = program.nodes(file.file_index());
                ast::is_conditional_expression(&nodes[p])
            }) {
                return get_contextual_type_for_conditional_expression(
                    program,
                    parent.unwrap(),
                    position,
                    file,
                    type_checker,
                );
            }
            return None;
        }
        Kind::ColonToken => {
            // When completing after `:` in a ternary conditional (e.g., `foo(a ? b : /*here*/)`),
            // we need to look at the parent conditional expression to find the contextual type.
            // Only handle this if parent is ConditionalExpression, otherwise fall through to default
            // (colons are used in other contexts like object literals, type annotations, etc.)
            if parent.is_some_and(|p| {
                let nodes = program.nodes(file.file_index());
                ast::is_conditional_expression(&nodes[p])
            }) {
                return get_contextual_type_for_conditional_expression(
                    program,
                    parent.unwrap(),
                    position,
                    file,
                    type_checker,
                );
            }
        }
        Kind::CommaToken => {
            // When completing after `,` in an array literal (e.g., `[x, /*here*/]`),
            // we should provide contextual type for the element after the comma.
            if parent.is_some_and(|p| {
                let nodes = program.nodes(file.file_index());
                ast::is_array_literal_expression(&nodes[p])
            }) {
                let parent = parent.unwrap();
                let contextual_array_type =
                    type_checker.get_contextual_type_api(parent, ContextFlags::NONE);
                if contextual_array_type.is_some() {
                    return type_checker.get_contextual_type_for_array_literal_at_position(
                        contextual_array_type,
                        parent,
                        position as i64,
                    );
                }
                return None;
            }
        }
        _ => {}
    }
    // Default case: see if we're in an argument position.
    let arg_info = {
        let mut nodes = program.nodes_mut(file.file_index());
        get_argument_info_for_completions(&mut nodes, previous_token, position, file, type_checker)
    };
    if let Some(arg_info) = arg_info {
        type_checker.get_contextual_type_for_argument_at_index(
            arg_info.invocation,
            arg_info.argument_index as i32,
        )
    } else {
        let is_binary_equality = {
            let nodes = program.nodes(file.file_index());
            is_equality_operator_kind(nodes[previous_token].kind)
                && parent.is_some_and(|p| ast::is_binary_expression(&nodes[p]))
                && parent.is_some_and(|p| {
                    nodes[p]
                        .as_binary_expression()
                        .operator_token
                        .is_some_and(|op| is_equality_operator_kind(nodes[op].kind))
                })
        };
        if is_binary_equality {
            // completion at `x ===/**/`
            let left = {
                let nodes = program.nodes(file.file_index());
                nodes[parent.unwrap()].as_binary_expression().left
            };
            return left.map(|l| type_checker.get_type_at_location(l));
        }
        let contextual_type = type_checker
            .get_contextual_type_api(previous_token, ContextFlags::IGNORE_NODE_INFERENCES);
        if contextual_type.is_some() {
            return contextual_type;
        }
        type_checker.get_contextual_type_api(previous_token, ContextFlags::NONE)
    }
}

/// `isLiteral` — we disregard boolean literals for completion purposes.
fn is_literal(t: TypeId, checker: &Checker) -> bool {
    let ty = checker.types.get(t);
    ty.is_string_literal() || ty.is_number_literal() || ty.is_big_int_literal()
}

/// `getRecommendedCompletion`.
fn get_recommended_completion(
    program: &Program,
    previous_token: NodeId,
    contextual_type: TypeId,
    type_checker: &mut Checker,
) -> Option<SymbolId> {
    let types: Vec<TypeId> = {
        let ty = type_checker.types.get(contextual_type);
        if ty.is_union() {
            ty.types().to_vec()
        } else {
            vec![contextual_type]
        }
    };
    // For a union, return the first one with a recommended completion.
    tsc_core::core::first_non_nil(&types, |t| {
        let symbol = type_checker.types.get(*t).symbol;
        // Don't make a recommended completion for an abstract class.
        symbol.and_then(|symbol| {
            let flags = program.symbols.get_ref(symbol).flags;
            if flags.intersects(SymbolFlags::ENUM_MEMBER | SymbolFlags::ENUM | SymbolFlags::CLASS)
                && !is_abstract_constructor_symbol(program, symbol)
            {
                get_first_symbol_in_chain(program, symbol, Some(previous_token), type_checker)
            } else {
                None
            }
        })
    })
}

/// `isAbstractConstructorSymbol`.
fn is_abstract_constructor_symbol(program: &Program, symbol: SymbolId) -> bool {
    let flags = program.symbols.get_ref(symbol).flags;
    if flags.intersects(SymbolFlags::CLASS) {
        // `get_class_like_declaration_of_symbol` reads `&Symbol` plus the
        // arena of the symbol's declarations.
        let declaration = {
            let symbols = program.symbols.clone();
            let s = &symbols[symbol.index()];
            ast::get_class_like_declaration_of_symbol_with(s, |d| {
                ast::is_class_like(Some(d), &program.arena_of(d))
            })
        };
        return declaration.is_some_and(|declaration| {
            let nodes = program.arena_of(declaration);
            ast::has_syntactic_modifier(&nodes[declaration], ModifierFlags::ABSTRACT)
        });
    }
    false
}

/// `startsWithQuote`.
pub(crate) fn starts_with_quote(s: &str) -> bool {
    s.starts_with('"') || s.starts_with('\'')
}

/// `getClosestSymbolDeclaration`.
fn get_closest_symbol_declaration(
    nodes: &[Node],
    context_token: Option<NodeId>,
    location: Option<NodeId>,
) -> Option<NodeId> {
    context_token?;

    let mut closest_declaration =
        ast::find_ancestor_or_quit(context_token, nodes, &mut |node, _| {
            if ast::is_function_block(Some(node.id), nodes)
                || is_arrow_function_body(node, nodes)
                || ast::is_binding_pattern(node)
            {
                return ast::FindAncestorResult::Quit;
            }
            if (ast::is_parameter_declaration(node) || ast::is_type_parameter_declaration(node))
                && !node
                    .parent
                    .is_some_and(|p| ast::is_index_signature_declaration(&nodes[p]))
            {
                return ast::FindAncestorResult::True;
            }
            ast::FindAncestorResult::False
        });

    if closest_declaration.is_none() {
        closest_declaration = ast::find_ancestor_or_quit(location, nodes, &mut |node, _| {
            if ast::is_function_block(Some(node.id), nodes)
                || is_arrow_function_body(node, nodes)
                || ast::is_binding_pattern(node)
            {
                return ast::FindAncestorResult::Quit;
            }
            if ast::is_variable_declaration(node) {
                return ast::FindAncestorResult::True;
            }
            ast::FindAncestorResult::False
        });
    }
    closest_declaration
}

/// `isArrowFunctionBody`.
fn is_arrow_function_body(node: &Node, nodes: &[Node]) -> bool {
    node.parent.is_some_and(|parent| {
        ast::is_arrow_function(&nodes[parent])
            && (nodes[parent].body() == Some(node.id) || node.kind == Kind::EqualsGreaterThanToken)
    })
}

/// `isInTypeParameterDefault`.
pub(crate) fn is_in_type_parameter_default(nodes: &[Node], context_token: Option<NodeId>) -> bool {
    let Some(context_token) = context_token else {
        return false;
    };

    let mut node = context_token;
    let mut parent = nodes[context_token].parent;
    while let Some(p) = parent {
        if ast::is_type_parameter_declaration(&nodes[p]) {
            return nodes[p].as_type_parameter_declaration().default_type == Some(node)
                || nodes[node].kind == Kind::EqualsToken;
        }
        node = p;
        parent = nodes[p].parent;
    }
    false
}

/// `isDeprecated`.
fn is_deprecated(symbol: SymbolId, type_checker: &mut Checker, program: &Program) -> bool {
    let Some(aliased) = type_checker.skip_alias(symbol) else {
        return false;
    };
    let declarations = program.symbols.get_ref(aliased)
        .declarations
        .clone();
    !declarations.is_empty()
        && tsc_core::core::every(&declarations, |decl| {
            type_checker.is_deprecated_declaration(*decl)
        })
}

/// `isNamedImportsOrExports`.
fn is_named_imports_or_exports(node: &Node) -> bool {
    matches!(node.kind, Kind::NamedImports | Kind::NamedExports)
}

/// `isTypeKeywordTokenOrIdentifier`.
fn is_type_keyword_token_or_identifier(node: &Node, nodes: &[Node]) -> bool {
    ast::is_type_keyword_token(node)
        || (ast::is_identifier(node)
            && tsc_scanner::utilities::identifier_to_keyword_kind(nodes[node.id].as_identifier())
                == Kind::TypeKeyword)
}

/// `hasDocComment`.
fn has_doc_comment(nodes: &mut Vec<Node>, file: NodeId, position: TextPos) -> bool {
    let token = tsc_astnav::tokens::get_token_at_position(nodes, file, position);
    ast::find_ancestor(token, nodes, &mut |n, _| ast::is_js_doc(n)).is_some()
}

/// `getJSDocTagAtPosition` — get the corresponding JSDocTag node if the
/// position is in a JSDoc comment.
fn get_js_doc_tag_at_position(
    nodes: &[Node],
    node: Option<NodeId>,
    position: TextPos,
) -> Option<NodeId> {
    ast::find_ancestor_or_quit(node, nodes, &mut |n, _| {
        if ast::is_js_doc_tag(n) && n.loc.contains_inclusive(position) {
            return ast::FindAncestorResult::True;
        }
        if ast::is_js_doc(n) {
            return ast::FindAncestorResult::Quit;
        }
        ast::FindAncestorResult::False
    })
}

/// `tryGetTypeExpressionFromTag`.
fn try_get_type_expression_from_tag(nodes: &[Node], tag: NodeId) -> Option<NodeId> {
    if is_tag_with_type_expression(nodes, tag) {
        let type_expression = if ast::is_js_doc_template_tag(&nodes[tag]) {
            nodes[tag].as_js_doc_template_tag().constraint
        } else {
            nodes[tag].type_expression()
        };
        if let Some(type_expression) = type_expression {
            if nodes[type_expression].kind == Kind::JSDocTypeExpression {
                return Some(type_expression);
            }
        }
    }
    if ast::is_js_doc_augments_tag(&nodes[tag]) || ast::is_js_doc_implements_tag(&nodes[tag]) {
        return nodes[tag].class_name();
    }
    None
}

/// `isTagWithTypeExpression`.
fn is_tag_with_type_expression(nodes: &[Node], tag: NodeId) -> bool {
    match nodes[tag].kind {
        Kind::JSDocParameterTag
        | Kind::JSDocPropertyTag
        | Kind::JSDocReturnTag
        | Kind::JSDocTypeTag
        | Kind::JSDocTypedefTag
        | Kind::JSDocThrowsTag
        | Kind::JSDocSatisfiesTag => true,
        Kind::JSDocTemplateTag => nodes[tag].as_js_doc_template_tag().constraint.is_some(),
        _ => false,
    }
}

/// `isCurrentlyEditingNode`.
fn is_currently_editing_node(
    nodes: &mut Vec<Node>,
    node: NodeId,
    file: NodeId,
    position: TextPos,
) -> bool {
    let start =
        tsc_astnav::tokens::get_start_of_node(nodes, file, node, false /*includeJSDoc*/);
    start <= position && position <= nodes[node].end()
}

/// `computeCommitCharactersAndIsNewIdentifier`.
fn compute_commit_characters_and_is_new_identifier(
    nodes: &mut Vec<Node>,
    context_token: Option<NodeId>,
    file: NodeId,
    position: TextPos,
) -> (bool, Vec<String>) {
    let all_commit_characters = || -> Vec<String> {
        all_commit_characters()
            .iter()
            .map(|s| s.to_string())
            .collect()
    };
    let no_comma_commit_characters = || -> Vec<String> {
        no_comma_commit_characters()
            .iter()
            .map(|s| s.to_string())
            .collect()
    };
    let empty_commit_characters = Vec::<String>::new;
    let Some(context_token) = context_token else {
        return (false, all_commit_characters());
    };
    let containing_node_kind = nodes[context_token]
        .parent
        .map(|p| nodes[p].kind)
        .unwrap_or(Kind::Unknown);
    let token_kind = keyword_for_node(&nodes[context_token], nodes);
    // Previous token may have been a keyword that was converted to an identifier.
    match token_kind {
        Kind::CommaToken => match containing_node_kind {
            // func( a, |
            // new C(a, |
            Kind::CallExpression | Kind::NewExpression => {
                let expression_end = nodes[nodes[context_token].parent.unwrap()]
                    .expression()
                    .map(|e| nodes[e].end());
                // func\n(a, |
                if get_line_of_position(nodes, file, expression_end.unwrap_or(0))
                    != get_line_of_position(nodes, file, position)
                {
                    return (true, no_comma_commit_characters());
                }
                (true, all_commit_characters())
            }
            // const x = (a, |
            Kind::BinaryExpression => (true, no_comma_commit_characters()),
            // constructor( a, | /* public, protected, private keywords are allowed here, so show completion */
            // var x: (s: string, list|
            // const obj = { x, |
            Kind::Constructor | Kind::FunctionType | Kind::ObjectLiteralExpression => {
                (true, empty_commit_characters())
            }
            // [a, |
            Kind::ArrayLiteralExpression => (true, all_commit_characters()),
            _ => (false, all_commit_characters()),
        },
        Kind::OpenParenToken => match containing_node_kind {
            // func( |
            // new C(a|
            Kind::CallExpression | Kind::NewExpression => {
                let expression_end = nodes[nodes[context_token].parent.unwrap()]
                    .expression()
                    .map(|e| nodes[e].end());
                // func\n( |
                if get_line_of_position(nodes, file, expression_end.unwrap_or(0))
                    != get_line_of_position(nodes, file, position)
                {
                    return (true, no_comma_commit_characters());
                }
                (true, all_commit_characters())
            }
            // const x = (a|
            Kind::ParenthesizedExpression => (true, no_comma_commit_characters()),
            // constructor( |
            // function F(pred: (a| /* this can become an arrow function, where 'a' is the argument */
            Kind::Constructor | Kind::ParenthesizedType => (true, empty_commit_characters()),
            _ => (false, all_commit_characters()),
        },
        Kind::OpenBracketToken => match containing_node_kind {
            // [ |
            // [ | : string ]
            // [ | : string ]
            // [ |    /* this can become an index signature */
            Kind::ArrayLiteralExpression
            | Kind::IndexSignature
            | Kind::TupleType
            | Kind::ComputedPropertyName => (true, all_commit_characters()),
            _ => (false, all_commit_characters()),
        },
        // module |
        // namespace |
        // import |
        Kind::ModuleKeyword | Kind::NamespaceKeyword | Kind::ImportKeyword => {
            (true, empty_commit_characters())
        }
        Kind::DotToken => match containing_node_kind {
            // module A.|
            Kind::ModuleDeclaration => (true, empty_commit_characters()),
            _ => (false, all_commit_characters()),
        },
        Kind::OpenBraceToken => match containing_node_kind {
            // class A { |
            // const obj = { |
            Kind::ClassDeclaration | Kind::ObjectLiteralExpression => {
                (true, empty_commit_characters())
            }
            _ => (false, all_commit_characters()),
        },
        Kind::EqualsToken => match containing_node_kind {
            // const x = a|
            // x = a|
            Kind::VariableDeclaration | Kind::BinaryExpression => (true, all_commit_characters()),
            _ => (false, all_commit_characters()),
        },
        Kind::TemplateHead => {
            // `aa ${|
            (
                containing_node_kind == Kind::TemplateExpression,
                all_commit_characters(),
            )
        }
        Kind::TemplateMiddle => {
            // `aa ${10} dd ${|
            (
                containing_node_kind == Kind::TemplateSpan,
                all_commit_characters(),
            )
        }
        Kind::AsyncKeyword => {
            // const obj = { async c|()
            // const obj = { async c|
            if containing_node_kind == Kind::MethodDeclaration
                || containing_node_kind == Kind::ShorthandPropertyAssignment
            {
                return (true, empty_commit_characters());
            }
            (false, all_commit_characters())
        }
        Kind::AsteriskToken => {
            // const obj = { * c|
            if containing_node_kind == Kind::MethodDeclaration {
                return (true, empty_commit_characters());
            }
            (false, all_commit_characters())
        }
        _ => {
            if is_class_member_completion_keyword(token_kind) {
                return (true, empty_commit_characters());
            }
            (false, all_commit_characters())
        }
    }
}

/// `keywordForNode`.
fn keyword_for_node(node: &Node, nodes: &[Node]) -> Kind {
    if ast::is_identifier(node) {
        return tsc_scanner::utilities::identifier_to_keyword_kind(nodes[node.id].as_identifier());
    }
    node.kind
}

/// `getScopeNode` — finds the first node that "embraces" the position, so
/// that one may accurately aggregate locals from the closest containing
/// scope.
fn get_scope_node(
    nodes: &mut Vec<Node>,
    initial_token: Option<NodeId>,
    position: TextPos,
    file: NodeId,
) -> Option<NodeId> {
    let mut scope = initial_token;
    while let Some(s) = scope {
        if crate::utilities::position_belongs_to_node(nodes, s, position, file) {
            break;
        }
        scope = nodes[s].parent;
    }
    scope
}

/// `isSnippetScope`.
fn is_snippet_scope(nodes: &[Node], scope_node: NodeId) -> bool {
    match nodes[scope_node].kind {
        Kind::SourceFile | Kind::TemplateExpression | Kind::JsxExpression | Kind::Block => true,
        _ => ast::is_statement(&nodes[scope_node], nodes),
    }
}

/// `isProbablyGlobalType` — determines if a type is exactly the same type
/// resolved by the global 'self', 'global', or 'globalThis'.
fn is_probably_global_type(t: TypeId, file: NodeId, type_checker: &mut Checker) -> bool {
    // The type of `self` and `window` is the same in lib.dom.d.ts, but `window` does not exist in
    // lib.webworker.d.ts, so checking against `self` is also a check against `window` when it exists.
    for name in ["self", "global", "globalThis"] {
        let symbol = type_checker.get_global_symbol(name, SymbolFlags::VALUE, None);
        if let Some(symbol) = symbol {
            if type_checker.get_type_of_symbol_at_location(symbol, Some(file)) == t {
                return true;
            }
        }
    }
    false
}

/// `tryGetTypeLiteralNode`.
fn try_get_type_literal_node(nodes: &[Node], node: NodeId) -> Option<NodeId> {
    let parent = nodes[node].parent?;
    match nodes[node].kind {
        Kind::OpenBraceToken => {
            if ast::is_type_literal_node(&nodes[parent]) {
                return Some(parent);
            }
        }
        Kind::SemicolonToken | Kind::CommaToken | Kind::Identifier => {
            if nodes[parent].kind == Kind::PropertySignature {
                if let Some(gp) = nodes[parent].parent {
                    if ast::is_type_literal_node(&nodes[gp]) {
                        return Some(gp);
                    }
                }
            }
        }
        _ => {}
    }
    None
}

/// `getConstraintOfTypeArgumentProperty`.
pub(crate) fn get_constraint_of_type_argument_property(
    program: &Program,
    node: Option<NodeId>,
    type_checker: &mut Checker,
) -> Option<TypeId> {
    let node = node?;
    {
        let nodes = program.arena_of(node);
        if ast::is_type_node(&nodes[node]) {
            if let Some(constraint) = type_checker.get_type_argument_constraint_api(node) {
                return Some(constraint);
            }
        }
    }

    let t = {
        let parent = program.arena_of(node)[node].parent;
        get_constraint_of_type_argument_property(program, parent, type_checker)
    };
    let t = t?;

    let kind = program.arena_of(node)[node].kind;
    match kind {
        Kind::PropertySignature => {
            // Try to get the reparsed node first - we may be in JSDoc.
            let reparsed = {
                let nodes = program.arena_of(node);
                ast::get_reparsed_node_for_node(node, &nodes)
            };
            let symbol = {
                let nodes = program.arena_of(reparsed);
                nodes[reparsed].symbol()
            };
            if let Some(symbol) = symbol {
                let name = program.symbols.get_ref(symbol).name.clone();
                return type_checker.get_type_of_property_of_contextual_type(t, &name);
            }

            // In some cases, we won't have a corresponding symbol
            // (e.g. JSDoc types that never get re-attached) so we'll use
            // the name as declared by the property as a best-effort.
            let name = {
                let nodes = program.arena_of(reparsed);
                nodes[reparsed]
                    .name()
                    .and_then(|n| ast::try_get_text_of_property_name(n, &nodes).0)
            };
            if let Some(name) = name {
                return type_checker.get_type_of_property_of_contextual_type(t, &name);
            }
            None
        }
        Kind::ColonToken => {
            let parent_is_property_signature = {
                let nodes = program.arena_of(node);
                nodes[node]
                    .parent
                    .is_some_and(|p| nodes[p].kind == Kind::PropertySignature)
            };
            if parent_is_property_signature {
                // The cursor is at a property value location like `Foo<{ x: | }`.
                // `t` already refers to the appropriate property type.
                return Some(t);
            }
            None
        }
        Kind::IntersectionType | Kind::TypeLiteral | Kind::UnionType => Some(t),
        Kind::OpenBracketToken => type_checker.get_element_type_of_array_type(t),
        _ => None,
    }
}

/// `tryGetObjectLikeCompletionContainer`.
fn try_get_object_like_completion_container(
    nodes: &mut Vec<Node>,
    context_token: NodeId,
    position: TextPos,
    file: NodeId,
) -> Option<NodeId> {
    let parent = nodes[context_token].parent?;
    match nodes[context_token].kind {
        // const x = { |
        // const x = { a: 0, |
        Kind::OpenBraceToken | Kind::CommaToken => {
            if ast::is_object_literal_expression(&nodes[parent])
                || ast::is_object_binding_pattern(&nodes[parent])
            {
                return Some(parent);
            }
        }
        Kind::AsteriskToken => {
            if ast::is_method_declaration(&nodes[parent]) {
                if let Some(gp) = nodes[parent].parent {
                    if ast::is_object_literal_expression(&nodes[gp]) {
                        return Some(gp);
                    }
                }
            }
        }
        Kind::AsyncKeyword => {
            if let Some(gp) = nodes[parent].parent {
                if ast::is_object_literal_expression(&nodes[gp]) {
                    return Some(gp);
                }
            }
        }
        Kind::Identifier => {
            if nodes[context_token].text(&nodes) == "async"
                && ast::is_shorthand_property_assignment(&nodes[parent])
            {
                return nodes[parent].parent;
            } else {
                let gp = nodes[parent].parent;
                if let Some(gp) = gp {
                    if ast::is_object_literal_expression(&nodes[gp])
                        && (ast::is_spread_assignment(&nodes[parent])
                            || (ast::is_shorthand_property_assignment(&nodes[parent])
                                && get_line_of_position(nodes, file, nodes[context_token].end())
                                    != get_line_of_position(nodes, file, position)))
                    {
                        return Some(gp);
                    }
                }
                let ancestor_node = ast::find_ancestor(Some(parent), nodes, &mut |n, _| {
                    ast::is_property_assignment(n)
                });
                if let Some(ancestor_node) = ancestor_node {
                    let last_token =
                        tsc_lsutil::children::get_last_token(nodes, Some(ancestor_node), file);
                    if last_token == Some(context_token)
                        && nodes[ancestor_node]
                            .parent
                            .is_some_and(|p| ast::is_object_literal_expression(&nodes[p]))
                    {
                        return nodes[ancestor_node].parent;
                    }
                }
            }
        }
        _ => {
            let gp = nodes[parent].parent;
            let ggp = gp.and_then(|p| nodes[p].parent);
            if let (Some(gp), Some(ggp)) = (gp, ggp) {
                if (ast::is_method_declaration(&nodes[gp])
                    || ast::is_get_accessor_declaration(&nodes[gp])
                    || ast::is_set_accessor_declaration(&nodes[gp]))
                    && ast::is_object_literal_expression(&nodes[ggp])
                {
                    return Some(ggp);
                }
            }
            if ast::is_spread_assignment(&nodes[parent]) {
                if let Some(gp) = gp {
                    if ast::is_object_literal_expression(&nodes[gp]) {
                        return Some(gp);
                    }
                }
            }
            let ancestor_node = ast::find_ancestor(Some(parent), nodes, &mut |n, _| {
                ast::is_property_assignment(n)
            });
            if nodes[context_token].kind != Kind::ColonToken {
                if let Some(ancestor_node) = ancestor_node {
                    let last_token =
                        tsc_lsutil::children::get_last_token(nodes, Some(ancestor_node), file);
                    if last_token == Some(context_token)
                        && nodes[ancestor_node]
                            .parent
                            .is_some_and(|p| ast::is_object_literal_expression(&nodes[p]))
                    {
                        return nodes[ancestor_node].parent;
                    }
                }
            }
        }
    }
    None
}

/// `tryGetObjectLiteralContextualType`.
fn try_get_object_literal_contextual_type(
    program: &Program,
    node: NodeId,
    type_checker: &mut Checker,
) -> Option<TypeId> {
    let t = type_checker.get_contextual_type_api(node, ContextFlags::NONE);
    if t.is_some() {
        return t;
    }

    let parent = {
        let nodes = program.arena_of(node);
        nodes[node]
            .parent
            .and_then(|p| ast::walk_up_parenthesized_expressions(p, &nodes))
    };
    let parent = parent?;
    {
        let nodes = program.arena_of(parent);
        if ast::is_binary_expression(&nodes[parent])
            && nodes[parent]
                .as_binary_expression()
                .operator_token
                .is_some_and(|op| nodes[op].kind == Kind::EqualsToken)
            && nodes[parent].as_binary_expression().left == Some(node)
        {
            // Object literal is assignment pattern: ({ | } = x)
            return Some(type_checker.get_type_at_location(parent));
        }
        if ast::is_expression(&nodes[parent], &nodes) {
            // f(() => (({ | })));
            return type_checker.get_contextual_type_api(parent, ContextFlags::NONE);
        }
    }
    None
}

/// `getPropertiesForObjectExpression`.
pub(crate) fn get_properties_for_object_expression(
    program: &Program,
    contextual_type: TypeId,
    completions_type: Option<TypeId>,
    obj: NodeId,
    type_checker: &mut Checker,
) -> Vec<SymbolId> {
    let has_completions_type =
        completions_type.is_some() && completions_type != Some(contextual_type);
    let types: Vec<TypeId> = {
        let ty = type_checker.types.get(contextual_type);
        if ty.is_union() {
            ty.types().to_vec()
        } else {
            vec![contextual_type]
        }
    };
    let filtered_types: Vec<TypeId> = types
        .into_iter()
        .filter_map(|t| {
            if type_checker.get_promised_type_of_promise(t).is_none() {
                Some(t)
            } else {
                None
            }
        })
        .collect();
    let promise_filtered_contextual_type = type_checker.get_union_type(&filtered_types);

    let t = if has_completions_type
        && !type_checker
            .types
            .get(completions_type.unwrap())
            .flags()
            .intersects(tsc_checker::types::TypeFlags::ANY_OR_UNKNOWN)
    {
        type_checker.get_union_type(&[promise_filtered_contextual_type, completions_type.unwrap()])
    } else {
        promise_filtered_contextual_type
    };

    // Filter out members whose only declaration is the object literal itself to avoid
    // self-fulfilling completions like:
    //
    // function f<T>(x: T) {}
    // f({ abc/**/: "" }) // `abc` is a member of `T` but only because it declares itself
    let has_declaration_other_than_self = |member: SymbolId| -> bool {
        let declarations = program.symbols.get_ref(member)
            .declarations
            .clone();
        if declarations.is_empty() {
            return true;
        }
        tsc_core::core::some(&declarations, |decl| {
            let nodes = program.arena_of(*decl);
            nodes[*decl].parent != Some(obj)
        })
    };

    let properties = get_apparent_properties(t, obj, type_checker);
    let t_is_class = type_checker.types.get(t).is_class();
    if t_is_class && contains_non_public_properties(&properties, type_checker) {
        return Vec::new();
    } else if has_completions_type {
        properties
            .into_iter()
            .filter(|&p| has_declaration_other_than_self(p))
            .collect()
    } else {
        properties
    }
}

/// `getApparentProperties` (the completions-local variant).
fn get_apparent_properties(t: TypeId, node: NodeId, type_checker: &mut Checker) -> Vec<SymbolId> {
    if !type_checker.types.get(t).is_union() {
        return type_checker.get_apparent_properties(t);
    }
    let types: Vec<TypeId> = type_checker.types.get(t).types().to_vec();
    let filtered: Vec<TypeId> = types
        .into_iter()
        .filter(|&member_type| {
            if type_checker
                .types
                .get(member_type)
                .flags()
                .intersects(tsc_checker::types::TypeFlags::PRIMITIVE)
            {
                return false;
            }
            if type_checker.is_array_like_type(member_type)
                || type_checker.is_type_invalid_due_to_union_discriminant(member_type, node)
                || type_checker.type_has_call_or_construct_signatures(member_type)
            {
                return false;
            }
            if type_checker.types.get(member_type).is_class()
                && contains_non_public_properties(
                    &type_checker.get_apparent_properties(member_type),
                    type_checker,
                )
            {
                return false;
            }
            true
        })
        .collect();
    type_checker.get_all_possible_properties_of_types(&filtered)
}

/// `containsNonPublicProperties`.
fn contains_non_public_properties(props: &[SymbolId], type_checker: &Checker) -> bool {
    tsc_core::core::some(props, |p| {
        tsc_checker::utilities::get_declaration_modifier_flags_from_symbol(type_checker, *p)
            .intersects(ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER)
    })
}

/// `filterObjectMembersList` — filters out members that are already declared
/// in the object literal or binding pattern; also computes the set of
/// existing members declared by spread assignment.
fn filter_object_members_list(
    program: &Program,
    contextual_member_symbols: &[SymbolId],
    existing_members: &[NodeId],
    file: NodeId,
    position: TextPos,
    type_checker: &mut Checker,
) -> (Vec<SymbolId>, Set<String>) {
    if existing_members.is_empty() {
        return (contextual_member_symbols.to_vec(), Set::default());
    }

    let mut members_declared_by_spread_assignment: Set<String> = Set::default();
    let mut existing_member_names: Set<String> = Set::default();
    for &member in existing_members {
        let (member_kind, skip) = {
            let nodes = program.arena_of(member);
            let kind = nodes[member].kind;
            let skip = !matches!(
                kind,
                Kind::PropertyAssignment
                    | Kind::ShorthandPropertyAssignment
                    | Kind::BindingElement
                    | Kind::MethodDeclaration
                    | Kind::GetAccessor
                    | Kind::SetAccessor
                    | Kind::SpreadAssignment
            );
            (kind, skip)
        };
        let _ = member_kind;
        // Ignore omitted expressions for missing members.
        if skip {
            continue;
        }

        // If this is the current item we are editing right now, do not filter it out.
        let editing = {
            let mut nodes = program.nodes_mut(file.file_index());
            is_currently_editing_node(&mut nodes, member, file, position)
        };
        if editing {
            continue;
        }

        let mut existing_name = String::new();
        {
            let nodes = program.arena_of(member);
            if ast::is_spread_assignment(&nodes[member]) {
                set_member_declared_by_spread_assignment(
                    program,
                    member,
                    &mut members_declared_by_spread_assignment,
                    type_checker,
                );
            } else if ast::is_binding_element(&nodes[member])
                && nodes[member].property_name().is_some()
            {
                // include only identifiers in completion list
                let property_name = nodes[member].property_name().unwrap();
                if nodes[property_name].kind == Kind::Identifier {
                    existing_name = nodes[property_name].text(&nodes).to_string();
                }
            } else {
                // TODO: Account for computed property name
                // NOTE: if one only performs this step when m.name is an identifier,
                // things like '__proto__' are not filtered out.
                let name = ast::get_name_of_declaration(Some(member), &nodes);
                if let Some(name) = name {
                    if ast::is_property_name_literal(&nodes[name]) {
                        existing_name = nodes[name].text(&nodes).to_string();
                    }
                }
            }
        }

        if !existing_name.is_empty() {
            existing_member_names.add(existing_name);
        }
    }

    let filtered_symbols: Vec<SymbolId> = contextual_member_symbols
        .iter()
        .copied()
        .filter(|m| !existing_member_names.has(program.symbols.get_ref(*m).name.as_ref()))
        .collect();

    (filtered_symbols, members_declared_by_spread_assignment)
}

/// `setMemberDeclaredBySpreadAssignment`.
fn set_member_declared_by_spread_assignment(
    program: &Program,
    declaration: NodeId,
    members: &mut Set<String>,
    type_checker: &mut Checker,
) {
    let expression = {
        let nodes = program.arena_of(declaration);
        nodes[declaration].expression()
    };
    let Some(expression) = expression else {
        return;
    };
    let symbol = type_checker.get_symbol_at_location_api(expression);
    let t =
        symbol.map(|symbol| type_checker.get_type_of_symbol_at_location(symbol, Some(expression)));
    let properties: Vec<SymbolId> = match t {
        Some(t)
            if type_checker
                .types
                .get(t)
                .flags()
                .intersects(tsc_checker::types::TypeFlags::STRUCTURED_TYPE) =>
        {
            type_checker
                .types
                .get(t)
                .as_structured_type()
                .map(|st| st.properties.clone())
                .unwrap_or_default()
        }
        _ => Vec::new(),
    };
    for property in properties {
        members.add(program.symbols.get_ref(property).name.to_string());
    }
}

/// `tryGetConstructorLikeCompletionContainer` — returns the immediate owning
/// class declaration of a context token, on the condition that one exists
/// and that the context implies completion should be given.
fn try_get_constructor_like_completion_container(
    nodes: &[Node],
    context_token: NodeId,
) -> Option<NodeId> {
    let parent = nodes[context_token].parent?;
    match nodes[context_token].kind {
        Kind::OpenParenToken | Kind::CommaToken => {
            if ast::is_constructor_declaration(&nodes[parent]) {
                return Some(parent);
            }
            None
        }
        _ => {
            if is_constructor_parameter_completion(nodes, context_token) {
                return nodes[parent].parent;
            }
            None
        }
    }
}

/// `isConstructorParameterCompletion`.
fn is_constructor_parameter_completion(nodes: &[Node], node: NodeId) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    let Some(grandparent) = nodes[parent].parent else {
        return false;
    };
    ast::is_parameter_declaration(&nodes[parent])
        && ast::is_constructor_declaration(&nodes[grandparent])
        && (ast::is_parameter_property_modifier(nodes[node].kind)
            || ast::is_declaration_name(node, nodes))
}

/// `tryGetObjectTypeDeclarationCompletionContainer` — returns the immediate
/// owning class declaration of a context token, on the condition that one
/// exists and that the context implies completion should be given.
fn try_get_object_type_declaration_completion_container(
    nodes: &mut Vec<Node>,
    file: NodeId,
    context_token: Option<NodeId>,
    location: Option<NodeId>,
    position: TextPos,
) -> Option<NodeId> {
    // class c { method() { } | method2() { } }
    let location_kind = location.map(|l| nodes[l].kind);
    match location_kind {
        Some(Kind::SyntaxList) => {
            let parent = nodes[location.unwrap()].parent;
            if let Some(p) = parent {
                if ast::is_object_type_declaration(&nodes[p], &nodes) {
                    return Some(p);
                }
            }
            return None;
        }
        Some(Kind::EndOfFile) => {
            let stmt_list = nodes[location.unwrap()]
                .parent
                .and_then(|p| nodes[p].statement_list().map(|sl| sl.nodes.clone()));
            if let Some(stmt_list) = stmt_list {
                if let Some(&cls) = stmt_list.last() {
                    if ast::is_object_type_declaration(&nodes[cls], &nodes)
                        && tsc_astnav::tokens::find_child_of_kind(
                            nodes,
                            file,
                            cls,
                            Kind::CloseBraceToken,
                        )
                        .is_none()
                    {
                        return Some(cls);
                    }
                }
            }
        }
        Some(Kind::PrivateIdentifier) => {
            let location = location.unwrap();
            if nodes[location]
                .parent
                .is_some_and(|p| ast::is_property_declaration(&nodes[p]))
            {
                return ast::find_ancestor(Some(location), nodes, &mut |n, nodes| {
                    ast::is_class_like(Some(n.id), nodes)
                });
            }
        }
        Some(Kind::Identifier) => {
            let location = location.unwrap();
            let original_keyword_kind =
                tsc_scanner::utilities::identifier_to_keyword_kind(nodes[location].as_identifier());
            if original_keyword_kind != Kind::Unknown {
                return None;
            }
            // class c { public prop = c| }
            if nodes[location]
                .parent
                .is_some_and(|p| ast::is_property_declaration(&nodes[p]))
                && nodes[nodes[location].parent.unwrap()].initializer() == Some(location)
            {
                return None;
            }
            // class c extends React.Component { a: () => 1\n compon| }
            if is_from_object_type_declaration(nodes, location) {
                return ast::find_ancestor(Some(location), nodes, &mut |n, _| {
                    ast::is_object_type_declaration(n, nodes)
                });
            }
        }
        _ => {}
    }

    let context_token = context_token?;

    // class C { blah; constructor/**/ }
    // or
    // class C { blah \n constructor/**/ }
    if location_kind == Some(Kind::ConstructorKeyword)
        || (ast::is_identifier(&nodes[context_token])
            && nodes[context_token]
                .parent
                .is_some_and(|p| ast::is_property_declaration(&nodes[p]))
            && location.is_some_and(|l| ast::is_class_like(Some(l), &nodes)))
    {
        return ast::find_ancestor(Some(context_token), nodes, &mut |n, nodes| {
            ast::is_class_like(Some(n.id), nodes)
        });
    }

    match nodes[context_token].kind {
        // class c { public prop = | /* global completions */ }
        Kind::EqualsToken => None,
        // class c {getValue(): number; | }
        // class c { method() { } | }
        Kind::SemicolonToken | Kind::CloseBraceToken => {
            // class c { method() { } b| }
            if let Some(location) = location {
                if is_from_object_type_declaration(nodes, location)
                    && nodes[nodes[location].parent.unwrap()].name() == Some(location)
                {
                    return nodes[nodes[location].parent.unwrap()].parent;
                }
            }
            if location.is_some_and(|l| ast::is_object_type_declaration(&nodes[l], &nodes)) {
                return location;
            }
            None
        }
        // class c { |
        // class c {getValue(): number, | }
        Kind::OpenBraceToken | Kind::CommaToken => {
            let parent = nodes[context_token].parent;
            if let Some(p) = parent {
                if ast::is_object_type_declaration(&nodes[p], &nodes) {
                    return Some(p);
                }
            }
            None
        }
        _ => {
            if let Some(location) = location {
                if ast::is_object_type_declaration(&nodes[location], &nodes) {
                    // class C extends React.Component { a: () => 1\n| }
                    // class C { prop = ""\n | }
                    if get_line_of_position(nodes, file, nodes[context_token].end())
                        != get_line_of_position(nodes, file, position)
                    {
                        return Some(location);
                    }
                    let is_valid_keyword: fn(Kind) -> bool = {
                        let parent_parent =
                            nodes[context_token].parent.and_then(|p| nodes[p].parent);
                        if parent_parent.is_some_and(|pp| ast::is_class_like(Some(pp), &nodes)) {
                            is_class_member_completion_keyword
                        } else {
                            is_interface_or_type_literal_completion_keyword
                        }
                    };

                    if is_valid_keyword(nodes[context_token].kind)
                        || nodes[context_token].kind == Kind::AsteriskToken
                        || (ast::is_identifier(&nodes[context_token])
                            && is_valid_keyword(
                                tsc_scanner::utilities::identifier_to_keyword_kind(
                                    nodes[context_token].as_identifier(),
                                ),
                            ))
                    {
                        return nodes[context_token].parent.and_then(|p| nodes[p].parent);
                    }
                }
            }
            None
        }
    }
}

/// `isFromObjectTypeDeclaration`.
fn is_from_object_type_declaration(nodes: &[Node], node: NodeId) -> bool {
    nodes[node].parent.is_some_and(|p| {
        ast::is_class_or_type_element(&nodes[p])
            && nodes[p]
                .parent
                .is_some_and(|pp| ast::is_object_type_declaration(&nodes[pp], &nodes))
    })
}

/// `filterClassMembersList` — filters out completion suggestions for class
/// elements.
fn filter_class_members_list(
    program: &Program,
    base_symbols: &[SymbolId],
    existing_members: &[NodeId],
    class_element_modifier_flags: ModifierFlags,
    file: NodeId,
    position: TextPos,
    type_checker: &Checker,
) -> Vec<SymbolId> {
    let mut existing_member_names: Set<String> = Set::default();
    for &member in existing_members {
        let nodes = program.arena_of(member);
        // Ignore omitted expressions for missing members.
        if !matches!(
            nodes[member].kind,
            Kind::PropertyDeclaration
                | Kind::MethodDeclaration
                | Kind::GetAccessor
                | Kind::SetAccessor
        ) {
            continue;
        }

        // If this is the current item we are editing right now, do not filter it out
        drop(nodes);
        let editing = {
            let mut nodes = program.nodes_mut(member.file_index());
            is_currently_editing_node(&mut nodes, member, file, position)
        };
        let nodes = program.arena_of(member);
        if editing {
            continue;
        }

        // Don't filter member even if the name matches if it is declared private in the list.
        if nodes[member]
            .modifier_flags()
            .intersects(ModifierFlags::PRIVATE)
        {
            continue;
        }

        // Do not filter it out if the static presence doesn't match.
        if ast::is_static(&nodes[member])
            != class_element_modifier_flags.intersects(ModifierFlags::STATIC)
        {
            continue;
        }

        let existing_name = nodes[member]
            .name()
            .map(|name| ast::get_property_name_for_property_name_node(name, &nodes))
            .unwrap_or_default();
        if !existing_name.is_empty() {
            existing_member_names.add(existing_name);
        }
    }

    base_symbols
        .iter()
        .copied()
        .filter(|&property_symbol| {
            let (declarations, value_declaration) = {
                let symbols = program.symbols.clone();
                (
                    symbols[property_symbol.index()].declarations.clone(),
                    symbols[property_symbol.index()].value_declaration,
                )
            };
            let name = {
                let symbols = program.symbols.clone();
                let symbol = &symbols[property_symbol.index()];
                match value_declaration.or_else(|| declarations.first().copied()) {
                    Some(decl) => {
                        let nodes = program.arena_of(decl);
                        ast::symbol_name(symbol, &nodes).to_string()
                    }
                    None => symbol.name.to_string(),
                }
            };
            !existing_member_names.has(&name)
                && !declarations.is_empty()
                && !tsc_checker::utilities::get_declaration_modifier_flags_from_symbol(
                    type_checker,
                    property_symbol,
                )
                .intersects(ModifierFlags::PRIVATE)
                && !value_declaration.is_some_and(|vd| {
                    let nodes = program.arena_of(vd);
                    ast::is_private_identifier_class_element_declaration(&nodes[vd], &nodes)
                })
        })
        .collect()
}

/// `tryGetContainingJsxElement`.
fn try_get_containing_jsx_element(
    nodes: &mut Vec<Node>,
    context_token: NodeId,
    file: NodeId,
) -> Option<NodeId> {
    let parent = nodes[context_token].parent;
    match nodes[context_token].kind {
        Kind::GreaterThanToken
        | Kind::LessThanSlashToken
        | Kind::SlashToken
        | Kind::Identifier
        | Kind::PropertyAccessExpression
        | Kind::JsxNamespacedName
        | Kind::JsxAttributes
        | Kind::JsxAttribute
        | Kind::JsxSpreadAttribute => {
            if parent.is_some_and(|p| {
                matches!(
                    nodes[p].kind,
                    Kind::JsxSelfClosingElement | Kind::JsxOpeningElement
                )
            }) {
                if nodes[context_token].kind == Kind::GreaterThanToken {
                    let parent = parent.unwrap();
                    let preceding_token = tsc_astnav::tokens::find_preceding_token(
                        nodes,
                        file,
                        nodes[context_token].pos(),
                    );
                    let type_arguments_empty = nodes[parent]
                        .type_arguments()
                        .map(|t| t.is_empty())
                        .unwrap_or(true);
                    if type_arguments_empty
                        || preceding_token.is_some_and(|pt| nodes[pt].kind == Kind::SlashToken)
                    {
                        return None;
                    }
                }
                return parent;
            } else if parent.is_some_and(|p| ast::is_jsx_namespaced_name(&nodes[p])) {
                let parent = parent.unwrap();
                if nodes[parent].parent.is_some_and(|pp| {
                    matches!(
                        nodes[pp].kind,
                        Kind::JsxSelfClosingElement | Kind::JsxOpeningElement
                    )
                }) {
                    return nodes[parent].parent;
                }
            } else if parent.is_some_and(|p| nodes[p].kind == Kind::JsxAttribute) {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                let parent = parent.unwrap();
                return nodes[parent].parent.and_then(|p| nodes[p].parent);
            }
        }
        // The context token is the closing } or " of an attribute, which means
        // its parent is a JsxExpression, whose parent is a JsxAttribute,
        // whose parent is a JsxOpeningLikeElement
        Kind::StringLiteral => {
            if parent.is_some_and(|p| {
                matches!(nodes[p].kind, Kind::JsxAttribute | Kind::JsxSpreadAttribute)
            }) {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                let parent = parent.unwrap();
                return nodes[parent].parent.and_then(|p| nodes[p].parent);
            }
        }
        Kind::CloseBraceToken => {
            if parent.is_some_and(|p| nodes[p].kind == Kind::JsxExpression) {
                let parent = parent.unwrap();
                if let Some(pp) = nodes[parent].parent {
                    if nodes[pp].kind == Kind::JsxAttribute {
                        // Currently we parse JsxOpeningLikeElement as:
                        //      JsxOpeningLikeElement
                        //          attributes: JsxAttributes
                        //             properties: NodeArray<JsxAttributeLike>
                        //                  each JsxAttribute can have initializer as JsxExpression
                        return nodes[pp].parent.and_then(|p| nodes[p].parent);
                    }
                }
            }
            if parent.is_some_and(|p| nodes[p].kind == Kind::JsxSpreadAttribute) {
                // Currently we parse JsxOpeningLikeElement as:
                //      JsxOpeningLikeElement
                //          attributes: JsxAttributes
                //             properties: NodeArray<JsxAttributeLike>
                let parent = parent.unwrap();
                return nodes[parent].parent.and_then(|p| nodes[p].parent);
            }
        }
        _ => {}
    }
    None
}

/// `filterJsxAttributes` — filters out completion suggestions from `symbols`
/// according to existing JSX attributes. Returns symbols to be suggested in
/// a JSX element, barring those whose attributes do not occur at the current
/// position and have not otherwise been typed.
fn filter_jsx_attributes(
    program: &Program,
    symbols: &[SymbolId],
    attributes: &[NodeId],
    file: NodeId,
    position: TextPos,
    type_checker: &mut Checker,
) -> (Vec<SymbolId>, Set<String>) {
    let mut existing_names: Set<String> = Set::default();
    let mut members_declared_by_spread_assignment: Set<String> = Set::default();
    for &attr in attributes {
        // If this is the item we are editing right now, do not filter it out.
        let editing = {
            let mut nodes = program.nodes_mut(attr.file_index());
            is_currently_editing_node(&mut nodes, attr, file, position)
        };
        if editing {
            continue;
        }

        let nodes = program.arena_of(attr);
        if nodes[attr].kind == Kind::JsxAttribute {
            if let Some(name) = nodes[attr].name() {
                existing_names.add(nodes[name].text(&nodes).to_string());
            }
        } else if ast::is_jsx_spread_attribute(&nodes[attr]) {
            drop(nodes);
            set_member_declared_by_spread_assignment(
                program,
                attr,
                &mut members_declared_by_spread_assignment,
                type_checker,
            );
        }
    }

    (
        symbols
            .iter()
            .copied()
            .filter(|a| !existing_names.has(program.symbols.get_ref(*a).name.as_ref()))
            .collect(),
        members_declared_by_spread_assignment,
    )
}

/// `getLineOfPosition`.
fn get_line_of_position(nodes: &[Node], file: NodeId, position: TextPos) -> TextPos {
    tsc_scanner::scanner::get_ecma_line_of_position(nodes[file].as_source_file(), position)
}

/// `getLineEndOfPosition`.
fn get_line_end_of_position(nodes: &[Node], file: NodeId, position: TextPos) -> TextPos {
    let source_file = nodes[file].as_source_file();
    let line = get_line_of_position(nodes, file, position);
    let line_starts = tsc_scanner::scanner::get_ecma_line_starts(source_file);
    let last_char_pos = if (line as usize) + 1 >= line_starts.len() {
        nodes[file].end()
    } else {
        line_starts[line as usize + 1] - 1
    };
    let full_text = source_file.text.as_bytes();
    if last_char_pos > 0
        && (last_char_pos as usize) < full_text.len()
        && full_text[last_char_pos as usize] == b'\n'
        && full_text[last_char_pos as usize - 1] == b'\r'
    {
        return last_char_pos - 1;
    }
    last_char_pos
}

/// `isCompletionListBlocker`.
fn is_completion_list_blocker(
    context_token: NodeId,
    previous_token: Option<NodeId>,
    location: Option<NodeId>,
    file: NodeId,
    position: TextPos,
    type_checker: &mut Checker,
    program: &Program,
) -> bool {
    {
        let nodes = program.nodes(file.file_index());
        if is_in_string_or_regular_expression_or_template_literal(&nodes, context_token, position)
            || is_dot_of_numeric_literal(&nodes, context_token)
            || is_in_jsx_text(&nodes, context_token, location)
            || ast::is_big_int_literal(&nodes[context_token])
        {
            return true;
        }
    }
    is_solely_identifier_definition_location(
        program,
        context_token,
        previous_token,
        file,
        position,
        type_checker,
    )
}

/// `isInStringOrRegularExpressionOrTemplateLiteral`.
fn is_in_string_or_regular_expression_or_template_literal(
    nodes: &[Node],
    context_token: NodeId,
    position: TextPos,
) -> bool {
    // To be "in" one of these literals, the position has to be:
    //   1. entirely within the token text.
    //   2. at the end position of an unterminated token.
    //   3. at the end of a regular expression (due to trailing flags like '/foo/g').
    (ast::is_regular_expression_literal(&nodes[context_token])
        || ast::is_string_text_containing_node(&nodes[context_token]))
        && nodes[context_token].loc.contains_exclusive(position)
        || position == nodes[context_token].end()
            && (ast::is_unterminated_literal(&nodes[context_token])
                || ast::is_regular_expression_literal(&nodes[context_token]))
}

/// `isSolelyIdentifierDefinitionLocation` — true if we are certain that the
/// currently edited location must define a new location; false otherwise.
fn is_solely_identifier_definition_location(
    program: &Program,
    context_token: NodeId,
    previous_token: Option<NodeId>,
    file: NodeId,
    position: TextPos,
    type_checker: &mut Checker,
) -> bool {
    let parent = {
        let nodes = program.nodes(file.file_index());
        nodes[context_token].parent
    };
    let Some(parent) = parent else {
        return false;
    };
    let (ct_kind, containing_node_kind) = {
        let nodes = program.nodes(file.file_index());
        (nodes[context_token].kind, nodes[parent].kind)
    };
    match ct_kind {
        Kind::CommaToken => {
            let is_var_decl_list_but_not_type_arg = containing_node_kind
                == Kind::VariableDeclarationList
                && !is_possibly_type_argument_position(
                    program,
                    Some(context_token),
                    file,
                    type_checker,
                );
            let is_class_like_with_type_params = {
                let nodes = program.nodes(file.file_index());
                ast::is_class_like(Some(parent), &nodes)
                    && nodes[parent]
                        .type_parameter_list()
                        .is_some_and(|tpl| tpl.loc.end() >= nodes[context_token].pos())
            };
            return containing_node_kind == Kind::VariableDeclaration
                || is_var_decl_list_but_not_type_arg
                || containing_node_kind == Kind::VariableStatement
                || containing_node_kind == Kind::EnumDeclaration // enum a { foo, |
                || is_function_like_but_not_constructor(containing_node_kind)
                || containing_node_kind == Kind::InterfaceDeclaration // interface A<T, |
                || containing_node_kind == Kind::ArrayBindingPattern // var [x, y|
                || containing_node_kind == Kind::TypeAliasDeclaration // type Map, K, |
                // class A<T, |
                // var C = class D<T, |
                || is_class_like_with_type_params;
        }
        Kind::DotToken => {
            return containing_node_kind == Kind::ArrayBindingPattern; // var [.|
        }
        Kind::ColonToken => {
            return containing_node_kind == Kind::BindingElement; // var {x :html|
        }
        Kind::OpenBracketToken => {
            return containing_node_kind == Kind::ArrayBindingPattern; // var [x|
        }
        Kind::OpenParenToken => {
            return containing_node_kind == Kind::CatchClause
                || is_function_like_but_not_constructor(containing_node_kind);
        }
        Kind::OpenBraceToken => {
            return containing_node_kind == Kind::EnumDeclaration; // enum a { |
        }
        Kind::LessThanToken => {
            return containing_node_kind == Kind::ClassDeclaration // class A< |
                || containing_node_kind == Kind::ClassExpression // var C = class D< |
                || containing_node_kind == Kind::InterfaceDeclaration // interface A< |
                || containing_node_kind == Kind::TypeAliasDeclaration // type List< |
                || ast::is_function_like_kind(containing_node_kind);
        }
        Kind::StaticKeyword => {
            return containing_node_kind == Kind::PropertyDeclaration && {
                let nodes = program.nodes(file.file_index());
                !nodes[parent]
                    .parent
                    .is_some_and(|pp| ast::is_class_like(Some(pp), &nodes))
            };
        }
        Kind::DotDotDotToken => {
            return containing_node_kind == Kind::Parameter || {
                let nodes = program.nodes(file.file_index());
                nodes[parent]
                    .parent
                    .is_some_and(|pp| nodes[pp].kind == Kind::ArrayBindingPattern)
            }; // var [...z|
        }
        Kind::PublicKeyword | Kind::PrivateKeyword | Kind::ProtectedKeyword => {
            return containing_node_kind == Kind::Parameter && {
                let nodes = program.nodes(file.file_index());
                !nodes[parent]
                    .parent
                    .is_some_and(|pp| ast::is_constructor_declaration(&nodes[pp]))
            };
        }
        Kind::AsKeyword => {
            return matches!(
                containing_node_kind,
                Kind::ImportSpecifier | Kind::ExportSpecifier | Kind::NamespaceImport
            );
        }
        Kind::GetKeyword | Kind::SetKeyword => {
            let nodes = program.nodes(file.file_index());
            return !is_from_object_type_declaration(&nodes, context_token);
        }
        Kind::Identifier => {
            if matches!(
                containing_node_kind,
                Kind::ImportSpecifier | Kind::ExportSpecifier
            ) {
                let nodes = program.nodes(file.file_index());
                if nodes[parent].name() == Some(context_token)
                    && nodes[context_token].text(&nodes) == "type"
                {
                    // import { type | }
                    return false;
                }
            }
            let ancestor_variable_declaration = {
                let nodes = program.nodes(file.file_index());
                ast::find_ancestor(Some(parent), &nodes, &mut |n, _| {
                    ast::is_variable_declaration(n)
                })
            };
            if ancestor_variable_declaration.is_some() {
                let nodes = program.nodes(file.file_index());
                if get_line_end_of_position(&nodes, file, nodes[context_token].end()) < position {
                    // let a
                    // |
                    return false;
                }
            }
        }
        Kind::ClassKeyword
        | Kind::EnumKeyword
        | Kind::InterfaceKeyword
        | Kind::FunctionKeyword
        | Kind::VarKeyword
        | Kind::ImportKeyword
        | Kind::LetKeyword
        | Kind::ConstKeyword
        | Kind::InferKeyword => {
            return true;
        }
        Kind::TypeKeyword => {
            // import { type foo| }
            return containing_node_kind != Kind::ImportSpecifier;
        }
        Kind::AsteriskToken => {
            let nodes = program.nodes(file.file_index());
            return ast::is_function_like(Some(parent), &nodes)
                && !ast::is_method_declaration(&nodes[parent]);
        }
        _ => {}
    }

    let token_kind = {
        let nodes = program.nodes(file.file_index());
        keyword_for_node(&nodes[context_token], &nodes)
    };
    // If the previous token is keyword corresponding to class member completion keyword
    // there will be completion available here
    if is_class_member_completion_keyword(token_kind) && {
        let nodes = program.nodes(file.file_index());
        is_from_object_type_declaration(&nodes, context_token)
    } {
        return false;
    }

    if {
        let nodes = program.nodes(file.file_index());
        is_constructor_parameter_completion(&nodes, context_token)
    } {
        // constructor parameter completion is available only if
        // - its modifier of the constructor parameter or
        // - its name of the parameter and not being edited
        // eg. constructor(a |<- this shouldnt show completion
        let is_identifier = {
            let nodes = program.nodes(file.file_index());
            ast::is_identifier(&nodes[context_token])
        };
        if !is_identifier || ast::is_parameter_property_modifier(token_kind) || {
            let mut nodes = program.nodes_mut(file.file_index());
            is_currently_editing_node(&mut nodes, context_token, file, position)
        } {
            return false;
        }
    }

    // Previous token may have been a keyword that was converted to an identifier.
    match token_kind {
        Kind::AbstractKeyword
        | Kind::ClassKeyword
        | Kind::DeclareKeyword
        | Kind::EnumKeyword
        | Kind::FunctionKeyword
        | Kind::InterfaceKeyword
        | Kind::LetKeyword
        | Kind::PrivateKeyword
        | Kind::ProtectedKeyword
        | Kind::PublicKeyword
        | Kind::StaticKeyword
        | Kind::VarKeyword => {
            return true;
        }
        Kind::AsyncKeyword => {
            let nodes = program.nodes(file.file_index());
            return ast::is_property_declaration(&nodes[parent]);
        }
        _ => {}
    }

    // If we are inside a class declaration, and `constructor` is totally not present,
    // but we request a completion manually at a whitespace...
    let (ancestor_class_like, ancestor_property_declaration) = {
        let nodes = program.nodes(file.file_index());
        (
            ast::find_ancestor(Some(parent), &nodes, &mut |n, nodes| {
                ast::is_class_like(Some(n.id), nodes)
            }),
            ast::find_ancestor(Some(parent), &nodes, &mut |n, _| {
                ast::is_property_declaration(n)
            }),
        )
    };
    if ancestor_class_like.is_some() && previous_token == Some(context_token) && {
        let nodes = program.nodes(file.file_index());
        is_previous_property_declaration_terminated(&nodes, context_token, file, position)
    } {
        // Don't block completions.
        return false;
    }

    // If we are inside a class declaration and typing `constructor` after property declaration...
    if ancestor_property_declaration.is_some()
        && previous_token.is_some()
        && previous_token != Some(context_token)
    {
        let previous_token = previous_token.unwrap();
        let (is_class_like_ggparent, is_initialized_or_typed, prev_end) = {
            let nodes = program.nodes(file.file_index());
            let ggparent = nodes[previous_token].parent.and_then(|p| nodes[p].parent);
            let ancestor_property_declaration = ancestor_property_declaration.unwrap();
            (
                ggparent.is_some_and(|ggp| ast::is_class_like(Some(ggp), &nodes)),
                ast::is_initialized_property(&nodes[ancestor_property_declaration])
                    || nodes[ancestor_property_declaration].type_().is_some(),
                nodes[previous_token].end(),
            )
        };
        if is_class_like_ggparent && position <= prev_end {
            // If we are sure that the previous property declaration is terminated according to newline or semicolon...
            if {
                let nodes = program.nodes(file.file_index());
                is_previous_property_declaration_terminated(&nodes, context_token, file, prev_end)
            } {
                // Don't block completions.
                return false;
            } else if ct_kind != Kind::EqualsToken && is_initialized_or_typed {
                // Should not block: `class C { blah = c/**/ }`
                // But should block: `class C { blah = somewhat c/**/ }` and `class C { blah: SomeType c/**/ }`
                return true;
            }
        }
    }
    if token_kind == Kind::ConstKeyword {
        return true;
    }
    {
        let nodes = program.nodes(file.file_index());
        ast::is_declaration_name(context_token, &nodes)
            && !ast::is_shorthand_property_assignment(&nodes[parent])
            && !ast::is_jsx_attribute(&nodes[parent])
            // Don't block completions if we're in `class C /**/`, `interface I /**/` or `<T /**/>` ,
            // because we're *past* the end of the identifier and might want to complete `extends`.
            // If `contextToken !== previousToken`, this is `class C ex/**/`, `interface I ex/**/` or `<T ex/**/>`.
            && !((ast::is_class_like(Some(parent), &nodes)
                || ast::is_interface_declaration(&nodes[parent])
                || ast::is_type_parameter_declaration(&nodes[parent]))
                && (previous_token != Some(context_token)
                    || previous_token.is_some_and(|pt| position > nodes[pt].end())))
    }
}

/// `isFunctionLikeButNotConstructor`.
fn is_function_like_but_not_constructor(kind: Kind) -> bool {
    ast::is_function_like_kind(kind) && kind != Kind::Constructor
}

/// `isPreviousPropertyDeclarationTerminated`.
fn is_previous_property_declaration_terminated(
    nodes: &[Node],
    context_token: NodeId,
    file: NodeId,
    position: TextPos,
) -> bool {
    nodes[context_token].kind != Kind::EqualsToken
        && (nodes[context_token].kind == Kind::SemicolonToken
            || get_line_of_position(nodes, file, nodes[context_token].end())
                != get_line_of_position(nodes, file, position))
}

/// `isDotOfNumericLiteral`.
fn is_dot_of_numeric_literal(nodes: &[Node], context_token: NodeId) -> bool {
    if nodes[context_token].kind == Kind::NumericLiteral {
        // Numeric literals can technically contain a dot, but in these cases the dot
        // belongs to the literal itself, not to a property access expression:
        // e.g. `const x = 12.|`
        // or `const x = 12.e1|`
        // (Actually `12.` is a legal numeric literal, but we don't want to complete on it.)
        let text = nodes[context_token].text(&nodes);
        return text.ends_with('.');
    }
    false
}

/// `isInJsxText`.
fn is_in_jsx_text(nodes: &[Node], context_token: NodeId, location: Option<NodeId>) -> bool {
    if nodes[context_token].kind == Kind::JsxText {
        return true;
    }

    if nodes[context_token].kind == Kind::GreaterThanToken {
        if let Some(parent) = nodes[context_token].parent {
            // <Component<string> /**/ />
            // <Component<string> /**/ ><Component>
            // - contextToken: GreaterThanToken (before cursor)
            // - location: JsxSelfClosingElement or JsxOpeningElement
            // - contextToken.parent === location
            if location == Some(parent) && ast::is_jsx_opening_like_element(&nodes[parent]) {
                return false;
            }

            if nodes[parent].kind == Kind::JsxOpeningElement {
                // <div>/**/
                // - contextToken: GreaterThanToken (before cursor)
                // - location: JSXElement
                // - different parents (JSXOpeningElement, JSXElement)
                return location.is_some_and(|l| {
                    nodes[l]
                        .parent
                        .is_some_and(|lp| nodes[lp].kind != Kind::JsxOpeningElement)
                });
            }

            if matches!(
                nodes[parent].kind,
                Kind::JsxClosingElement | Kind::JsxSelfClosingElement
            ) {
                return nodes[parent]
                    .parent
                    .is_some_and(|pp| nodes[pp].kind == Kind::JsxElement);
            }
        }
    }
    false
}

/// `strPtrIsEmpty`.
pub(crate) fn str_ptr_is_empty(ptr: Option<&str>) -> bool {
    ptr.map_or(true, |p| p.is_empty())
}

/// `strPtrTo`.
pub(crate) fn str_ptr_to(v: String) -> Option<String> {
    if v.is_empty() { None } else { Some(v) }
}

/// `boolToPtr`.
pub(crate) fn bool_to_ptr(v: bool) -> Option<bool> {
    if v { Some(true) } else { None }
}

/// `isMemberCompletionKind`.
pub(crate) fn is_member_completion_kind(kind: CompletionKind) -> bool {
    matches!(
        kind,
        CompletionKind::ObjectPropertyDeclaration
            | CompletionKind::MemberLike
            | CompletionKind::PropertyAccess
    )
}

/// `tryGetFunctionLikeBodyCompletionContainer`.
fn try_get_function_like_body_completion_container(
    nodes: &[Node],
    context_token: Option<NodeId>,
) -> Option<NodeId> {
    let context_token = context_token?;

    let mut prev: Option<NodeId> = None;
    ast::find_ancestor_or_quit(Some(context_token), nodes, &mut |node, nodes| {
        if ast::is_class_like(Some(node.id), nodes) {
            return ast::FindAncestorResult::Quit;
        }
        if ast::is_function_like_declaration(Some(node.id), nodes) && prev == node.body() {
            return ast::FindAncestorResult::True;
        }
        prev = Some(node.id);
        ast::FindAncestorResult::False
    })
}

/// `clientSupportsItemLabelDetails`.
fn client_supports_item_label_details(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .label_details_support
}

/// `clientSupportsItemSnippet`.
pub(crate) fn client_supports_item_snippet(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .snippet_support
}

/// `clientSupportsItemCommitCharacters`.
pub(crate) fn client_supports_item_commit_characters(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .commit_characters_support
}

/// `clientSupportsItemInsertReplace`.
pub(crate) fn client_supports_item_insert_replace(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_item
        .insert_replace_support
}

/// `clientSupportsDefaultCommitCharacters`.
fn client_supports_default_commit_characters(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_list
        .item_defaults
        .iter()
        .any(|d| d == "commitCharacters")
}

/// `clientSupportsDefaultEditRange`.
fn client_supports_default_edit_range(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .completion
        .completion_list
        .item_defaults
        .iter()
        .any(|d| d == "editRange")
}

/// `type argumentInfoForCompletions struct`.
pub(crate) struct ArgumentInfoForCompletions {
    /// `invocation *ast.CallLikeExpression`.
    pub(crate) invocation: NodeId,
    /// `argumentIndex`.
    pub(crate) argument_index: usize,
    /// `argumentCount`.
    pub(crate) argument_count: usize,
}

/// `getArgumentInfoForCompletions`.
pub(crate) fn get_argument_info_for_completions(
    nodes: &mut Vec<Node>,
    node: NodeId,
    position: TextPos,
    file: NodeId,
    type_checker: &mut Checker,
) -> Option<ArgumentInfoForCompletions> {
    let info = crate::signaturehelp::get_immediately_containing_argument_info(
        nodes,
        node,
        position,
        file,
        type_checker,
    )?;
    if info.is_type_parameter_list || info.invocation.call_invocation.is_none() {
        return None;
    }
    Some(ArgumentInfoForCompletions {
        invocation: info.invocation.call_invocation.unwrap().node,
        argument_index: info.argument_index,
        argument_count: info.argument_count,
    })
}

/// `isRecommendedCompletionMatch`.
fn is_recommended_completion_match(
    local_symbol: SymbolId,
    recommended_completion: Option<SymbolId>,
    type_checker: &mut Checker,
    program: &Program,
) -> bool {
    let Some(recommended_completion) = recommended_completion else {
        return false;
    };
    if local_symbol == recommended_completion {
        return true;
    }
    let flags = program.symbols.get_ref(local_symbol).flags;
    flags.intersects(SymbolFlags::EXPORT_VALUE)
        && type_checker.get_export_symbol_of_symbol(local_symbol) == recommended_completion
}

/// `wordSeparators` — ported from vscode.
fn word_separators() -> &'static Set<char> {
    static WORD_SEPARATORS: std::sync::OnceLock<Set<char>> = std::sync::OnceLock::new();
    WORD_SEPARATORS.get_or_init(|| {
        let mut set = Set::default();
        for c in [
            '`', '~', '!', '@', '%', '^', '&', '*', '(', ')', '-', '=', '+', '[', '{', ']', '}',
            '\\', '|', ';', ':', '\'', '"', ',', '.', '<', '>', '/', '?',
        ] {
            set.add(c);
        }
        set
    })
}

/// `getWordLengthAndStart` — finds the length and first rune of the word
/// that ends at the given position. e.g. for "abc def.ghi|jkl", the word
/// length is 3 and the word start is 'g'.
fn get_word_length_and_start(nodes: &[Node], file: NodeId, position: TextPos) -> (usize, char) {
    // !!! Port other case of vscode's `DEFAULT_WORD_REGEXP` that covers words that
    // start like numbers, e.g. -123.456abcd.
    let text = &nodes[file].as_source_file().text()[..position.max(0) as usize];
    let mut total_size = 0usize;
    let mut first_rune = '\0';
    let mut rest = text;
    while let Some(ch) = rest.chars().next_back() {
        if word_separators().has(&ch) || ch.is_whitespace() {
            break;
        }
        let size = ch.len_utf8();
        total_size += size;
        first_rune = ch;
        rest = &rest[..rest.len() - size];
    }
    // If word starts with `@`, disregard this first character.
    if first_rune == '@' {
        total_size = total_size.saturating_sub(1);
        first_rune = text[text.len() - total_size..]
            .chars()
            .next()
            .unwrap_or('\0');
    }
    (total_size, first_rune)
}

/// `trimElementAccess` — `["ab c"]` -> `ab c`, `['ab c']` -> `ab c`,
/// `[123]` -> `123`.
fn trim_element_access(text: &str) -> &str {
    let mut text = text.strip_prefix('[').unwrap_or(text);
    text = text.strip_suffix(']').unwrap_or(text);
    if text.starts_with('\'') && text.ends_with('\'') {
        text = &text[1..text.len() - 1];
    }
    if text.starts_with('"') && text.ends_with('"') {
        text = &text[1..text.len() - 1];
    }
    text
}

/// `getFilterText` — ported from vscode ts extension.
fn get_filter_text(
    nodes: &[Node],
    file: NodeId,
    position: TextPos,
    insert_text: &str,
    label: &str,
    word_start: char,
    dot_accessor: &str,
) -> String {
    // Private field completion, e.g. label `#bar`.
    if let Some(after) = label.strip_prefix('#') {
        if !insert_text.is_empty() {
            if let Some(after) = insert_text.strip_prefix("this.#") {
                if word_start == '#' {
                    // `method() { this.#| }`
                    // `method() { #| }`
                    return String::new();
                } else {
                    // `method() { this.| }`
                    // `method() { | }`
                    return after.to_string();
                }
            }
        } else if word_start == '#' {
            // `method() { this.#| }`
            return String::new();
        } else {
            // `method() { this.| }`
            // `method() { | }`
            return after.to_string();
        }
    }

    // For `this.` completions, generally don't set the filter text since we don't want them
    // to be overly deprioritized. microsoft/vscode#74164
    if insert_text.starts_with("this.") {
        return String::new();
    }

    // Handle the case:
    // ```
    // const xyz = { 'ab c': 1 };
    // xyz.ab|
    // ```
    // In which case we want to insert a bracket accessor but should use `.abc` as the
    // filter text instead of the bracketed insert text.
    if insert_text.starts_with('[') {
        return format!("{}{}", dot_accessor, trim_element_access(insert_text));
    }

    if insert_text.starts_with("?.") {
        if let Some(rest) = insert_text.strip_prefix("?.[") {
            // filterText should be `.ab c` instead of `?.['ab c']`.
            return format!("{}{}", dot_accessor, trim_element_access(rest));
        } else {
            // filterText should be `.abc` instead of `?.abc`.
            return format!("{}{}", dot_accessor, &insert_text[2..]);
        }
    }

    // In all other cases, fall back to using the insertText.
    insert_text.to_string()
}

/// `getDotAccessor` — ported from vscode's `provideCompletionItems`.
fn get_dot_accessor(nodes: &[Node], file: NodeId, position: TextPos) -> String {
    let text = &nodes[file].as_source_file().text()[..position.max(0) as usize];
    if text.ends_with("?.") {
        return text[position as usize - 2..position as usize].to_string();
    }
    if text.ends_with('.') {
        return text[position as usize - 1..position as usize].to_string();
    }
    String::new()
}

/// `isClassLikeMemberCompletion`.
fn is_class_like_member_completion(
    program: &Program,
    symbol: SymbolId,
    location: Option<NodeId>,
    file: NodeId,
) -> bool {
    let Some(location) = location else {
        return false;
    };
    let nodes = program.arena_of(location);
    if ast::is_in_js_file(Some(location), &nodes) {
        return false;
    }
    let member_flags = SymbolFlags::CLASS_MEMBER & SymbolFlags::ENUM_MEMBER_EXCLUDES;
    let symbol_flags = program.symbols.get_ref(symbol).flags;
    symbol_flags.intersects(member_flags)
        && (ast::is_class_like(Some(location), &nodes)
            || (nodes[location].parent.is_some()
                && nodes[nodes[location].parent.unwrap()].parent.is_some()
                && ast::is_class_element(&nodes[nodes[location].parent.unwrap()])
                && {
                    let parent = nodes[location].parent.unwrap();
                    let mut nodes = program.nodes_mut(location.file_index());
                    let last_token =
                        tsc_lsutil::children::get_last_token(&mut nodes, Some(parent), file);
                    let nodes = program.nodes(location.file_index());
                    last_token == Some(location)
                        && nodes[parent].name() == Some(location)
                        && nodes[parent]
                            .parent
                            .is_some_and(|pp| ast::is_class_like(Some(pp), &nodes))
                })
            || (nodes[location].parent.is_some_and(|p| {
                nodes[location].kind == Kind::SyntaxList && ast::is_class_like(Some(p), &nodes)
            })))
}

/// `symbolAppearsToBeTypeOnly`.
fn symbol_appears_to_be_type_only(
    program: &Program,
    symbol: SymbolId,
    type_checker: &mut Checker,
) -> bool {
    let aliased = type_checker.skip_alias(symbol).unwrap_or(symbol);
    let flags = combined_local_and_export_symbol_flags(&program.symbols, aliased);
    let declarations_empty_or_not_in_js = {
        let symbols = program.symbols.clone();
        let declarations = &symbols[symbol.index()].declarations;
        declarations.is_empty()
            || !declarations.first().is_some_and(|d| {
                let nodes = program.arena_of(*d);
                ast::is_in_js_file(Some(*d), &nodes)
            })
    };
    !flags.intersects(SymbolFlags::VALUE)
        && (declarations_empty_or_not_in_js || flags.intersects(SymbolFlags::TYPE))
}

/// `symbol.CombinedLocalAndExportSymbolFlags()`.
fn combined_local_and_export_symbol_flags(
    symbols: &tsc_ast::SymbolArena,
    s: SymbolId,
) -> SymbolFlags {
    let arena = symbols.clone();
    let sym = &arena[s.index()];
    let mut flags = sym.flags;
    if let Some(export_symbol) = sym.export_symbol {
        flags |= arena[export_symbol.index()].flags;
    }
    flags
}

/// `shouldIncludeSymbol`.
fn should_include_symbol(
    program: &Program,
    symbol: SymbolId,
    data: &CompletionDataData,
    closest_symbol_declaration: Option<NodeId>,
    file: NodeId,
    type_checker: &mut Checker,
) -> bool {
    let (mut all_flags, symbol_value_declaration, symbol_declarations, symbol_parent) = {
        let symbols = program.symbols.clone();
        let s = &symbols[symbol.index()];
        (
            s.flags,
            s.value_declaration,
            s.declarations.clone(),
            s.parent,
        )
    };
    let location = data.location;
    {
        let nodes = program.nodes(file.file_index());
        // export = /**/ here we want to get all meanings, so any symbol is ok
        if location.is_some_and(|l| {
            nodes[l]
                .parent
                .is_some_and(|p| ast::is_export_assignment(&nodes[p]))
        }) {
            return true;
        }
    }

    // Filter out variables from their own initializers
    // `const a = /* no 'a' here */`
    if let Some(closest_symbol_declaration) = closest_symbol_declaration {
        let nodes = program.arena_of(closest_symbol_declaration);
        if ast::is_variable_declaration(&nodes[closest_symbol_declaration])
            && symbol_value_declaration == Some(closest_symbol_declaration)
        {
            return false;
        }
    }

    // Filter out current and latter parameters from defaults
    // `function f(a = /* no 'a' and 'b' here */, b) { }` or
    // `function f<T = /* no 'T' and 'T2' here */>(a: T, b: T2) { }`
    let symbol_declaration =
        symbol_value_declaration.or_else(|| symbol_declarations.first().copied());

    if let (Some(closest_symbol_declaration), Some(symbol_declaration)) =
        (closest_symbol_declaration, symbol_declaration)
    {
        let (is_param_param, is_tparam_tparam) = {
            let nodes = program.arena_of(closest_symbol_declaration);
            (
                ast::is_parameter_declaration(&nodes[closest_symbol_declaration]),
                ast::is_type_parameter_declaration(&nodes[closest_symbol_declaration]),
            )
        };
        if is_param_param && {
            let nodes = program.arena_of(symbol_declaration);
            ast::is_parameter_declaration(&nodes[symbol_declaration])
        } {
            let in_range = {
                let nodes = program.arena_of(closest_symbol_declaration);
                let parameters = nodes[nodes[closest_symbol_declaration].parent.unwrap()]
                    .parameter_list()
                    .expect("parameters");
                let symbol_pos = {
                    let nodes = program.arena_of(symbol_declaration);
                    nodes[symbol_declaration].pos()
                };
                symbol_pos >= nodes[closest_symbol_declaration].pos()
                    && symbol_pos < parameters.loc.end()
            };
            if in_range {
                return false;
            }
        } else if is_tparam_tparam && {
            let nodes = program.arena_of(symbol_declaration);
            ast::is_type_parameter_declaration(&nodes[symbol_declaration])
        } {
            if closest_symbol_declaration == symbol_declaration
                && data.context_token.is_some_and(|ct| {
                    let nodes = program.arena_of(ct);
                    nodes[ct].kind == Kind::ExtendsKeyword
                })
            {
                // filter out the directly self-recursive type parameters
                // `type A<K extends /* no 'K' here*/> = K`
                return false;
            }
            let (in_default, parent_not_infer) = {
                let nodes = program.nodes(file.file_index());
                (
                    is_in_type_parameter_default(&nodes, data.context_token),
                    nodes[closest_symbol_declaration]
                        .parent
                        .is_some_and(|p| !ast::is_infer_type_node(&nodes[p])),
                )
            };
            if in_default && parent_not_infer {
                let in_range = {
                    let nodes = program.arena_of(closest_symbol_declaration);
                    let type_parameters = nodes[nodes[closest_symbol_declaration].parent.unwrap()]
                        .type_parameter_list();
                    if let Some(type_parameters) = type_parameters {
                        let symbol_pos = {
                            let nodes = program.arena_of(symbol_declaration);
                            nodes[symbol_declaration].pos()
                        };
                        symbol_pos >= nodes[closest_symbol_declaration].pos()
                            && symbol_pos < type_parameters.loc.end()
                    } else {
                        false
                    }
                };
                if in_range {
                    return false;
                }
            }
        }
    }

    // External modules can have global export declarations that will be
    // available as global keywords in all scopes. But if the external module
    // already has an explicit export and user only wants to use explicit
    // module imports then the global keywords will be filtered out so auto
    // import suggestions will win in the completion.
    let symbol_origin = type_checker.skip_alias(symbol).unwrap_or(symbol);
    // We only want to filter out the global keywords.
    // Auto Imports are not available for scripts so this conditional is always false.
    {
        let nodes = program.nodes(file.file_index());
        let external_module_indicator = nodes[file]
            .as_source_file()
            .external_module_indicator
            .is_some();
        if external_module_indicator
            && self_compiler_options_allow_umd_global_access(program)
                != tsc_core::tristate::Tristate::True
            && symbol != symbol_origin
            && data
                .symbol_to_sort_text_map
                .get(&symbol)
                .is_some_and(|st| st == sort_text::GLOBALS_OR_KEYWORDS)
            && symbol_parent.is_some_and(|parent| {
                tsc_checker::utilities::is_external_module_symbol(parent, type_checker)
            })
        {
            return false;
        }
    }

    all_flags |= combined_local_and_export_symbol_flags(&program.symbols, symbol_origin);
    if program.symbols.get_ref(symbol)
        .flags
        .intersects(SymbolFlags::ALIAS)
    {
        all_flags |= type_checker.get_symbol_flags(symbol);
    }

    // import m = /**/ <-- It can only access namespace (if typing import = x. this would get member symbols and not namespace)
    if location.is_some_and(|l| {
        let nodes = program.arena_of(l);
        crate::utilities::is_in_right_side_of_internal_import_equals_declaration(l, &nodes)
    }) {
        return all_flags.intersects(SymbolFlags::NAMESPACE);
    }

    if data.is_type_only_location {
        // It's a type, but you can reach it by namespace.type as well.
        return symbol_can_be_referenced_at_type_location(
            symbol,
            type_checker,
            &mut Set::default(),
            program,
        );
    }

    // expressions are value space (which includes the value namespaces)
    all_flags.intersects(SymbolFlags::VALUE)
}

/// `compilerOptions.AllowUmdGlobalAccess` accessor shim.
fn self_compiler_options_allow_umd_global_access(
    program: &Program,
) -> tsc_core::tristate::Tristate {
    program.options().allow_umd_global_access
}

/// `getCompletionEntryDisplayNameForSymbol`.
fn get_completion_entry_display_name_for_symbol(
    nodes: &mut Vec<Node>,
    file: NodeId,
    preferences: &UserPreferences,
    symbol: SymbolId,
    origin: Option<&SymbolOriginInfo>,
    completion_kind: CompletionKind,
    is_jsx_identifier_expected: bool,
    type_checker: &Checker,
    program: &Program,
) -> (String, bool) {
    if origin_is_ignore(origin) {
        return (String::new(), false);
    }

    let name: String = if origin_includes_symbol_name(origin) {
        origin.unwrap().symbol_name().to_string()
    } else {
        let (name, value_declaration) = {
            let symbols = program.symbols.clone();
            let s = &symbols[symbol.index()];
            (s.name.to_string(), s.value_declaration)
        };
        let _ = value_declaration;
        name
    };
    if name.is_empty() ||
        // If the symbol is external module, don't show it in the completion list
        // (i.e declare module "http" { const x; } | // <= request completion here, "http" should not be there)
        program.symbols.get_ref(symbol)
            .flags
            .intersects(SymbolFlags::MODULE)
            && starts_with_quote(&name)
        // If the symbol is the internal name of an ES symbol, it is not a valid entry. Internal names for ES symbols start with "__@"
        || tsc_checker::utilities::is_known_symbol(type_checker, symbol)
    {
        return (String::new(), false);
    }

    let variant = if is_jsx_identifier_expected {
        tsc_core::languagevariant::LanguageVariant::Jsx
    } else {
        tsc_core::languagevariant::LanguageVariant::Standard
    };
    // name is a valid identifier or private identifier text
    let (is_identifier_text, is_private_identifier_decl) = {
        (
            tsc_scanner::utilities::is_identifier_text(&name, variant),
            program.symbols.get_ref(symbol)
                .value_declaration
                .is_some_and(|vd| {
                    let nodes = program.arena_of(vd);
                    ast::is_private_identifier_class_element_declaration(&nodes[vd], &nodes)
                }),
        )
    };
    if is_identifier_text || is_private_identifier_decl {
        return (name, false);
    }
    if program.symbols.get_ref(symbol)
        .flags
        .intersects(SymbolFlags::ALIAS)
    {
        // Allow non-identifier import/export aliases since we can insert them as string literals
        return (name, true);
    }

    match completion_kind {
        CompletionKind::MemberLike => {
            if origin_is_computed_property_name(origin) {
                return (origin.unwrap().symbol_name().to_string(), false);
            }
            (String::new(), false)
        }
        CompletionKind::ObjectPropertyDeclaration => (
            crate::utilities::quote(nodes, file, preferences, &name),
            false,
        ),
        CompletionKind::PropertyAccess | CompletionKind::Global => {
            // For a 'this.' completion it will be in a global context, but may have a non-identifier name.
            // Don't add a completion for a name starting with a space. See https://github.com/Microsoft/TypeScript/pull/20547
            if name.starts_with(' ') {
                return (String::new(), false);
            }
            (name, true)
        }
        CompletionKind::None | CompletionKind::String => (name, false),
    }
}

// !!! refactor symbolOriginInfo so that we can tell the difference between flags and the kind of data it has

/// `originIsIgnore`.
pub(crate) fn origin_is_ignore(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| o.kind.intersects(SymbolOriginInfoKind::IGNORE))
}

/// `originIncludesSymbolName`.
fn origin_includes_symbol_name(origin: Option<&SymbolOriginInfo>) -> bool {
    origin_is_computed_property_name(origin)
}

/// `originIsComputedPropertyName`.
pub(crate) fn origin_is_computed_property_name(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| {
        o.kind
            .intersects(SymbolOriginInfoKind::COMPUTED_PROPERTY_NAME)
    })
}

/// `originIsObjectLiteralMethod`.
pub(crate) fn origin_is_object_literal_method(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| {
        o.kind
            .intersects(SymbolOriginInfoKind::OBJECT_LITERAL_METHOD)
    })
}

/// `originIsThisTypeNode`.
fn origin_is_this_type_node(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| o.kind.intersects(SymbolOriginInfoKind::THIS_TYPE))
}

/// `originIsTypeOnlyAlias`.
pub(crate) fn origin_is_type_only_alias(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| o.kind.intersects(SymbolOriginInfoKind::TYPE_ONLY_ALIAS))
}

/// `originIsSymbolMember`.
fn origin_is_symbol_member(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| o.kind.intersects(SymbolOriginInfoKind::SYMBOL_MEMBER))
}

/// `originIsNullableMember`.
fn origin_is_nullable_member(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| o.kind.intersects(SymbolOriginInfoKind::NULLABLE))
}

/// `originIsPromise`.
fn origin_is_promise(origin: Option<&SymbolOriginInfo>) -> bool {
    origin.is_some_and(|o| o.kind.intersects(SymbolOriginInfoKind::PROMISE))
}

/// `getSourceFromOrigin`.
fn get_source_from_origin(origin: Option<&SymbolOriginInfo>) -> &'static str {
    if origin_is_this_type_node(origin) {
        return completion_source::THIS_PROPERTY;
    }
    if origin_is_type_only_alias(origin) {
        return completion_source::TYPE_ONLY_ALIAS;
    }
    ""
}

/// `escapeSnippetText`.
fn escape_snippet_text(text: &str) -> String {
    text.replace('$', "\\$")
}

/// `generateIdentifierForArbitraryString` — converts "(example, text)" into
/// "_example_text_".
fn generate_identifier_for_arbitrary_string(text: &str) -> String {
    let mut needs_underscore = false;
    let mut identifier = String::new();

    for (pos, ch) in text.char_indices() {
        let valid_char = if pos == 0 {
            tsc_scanner::scanner::is_identifier_start(ch as i32)
        } else {
            tsc_scanner::scanner::is_identifier_part(ch as i32)
        };
        if valid_char {
            if needs_underscore {
                identifier.push('_');
            }
            identifier.push(ch);
            needs_underscore = false;
        } else {
            needs_underscore = true;
        }
    }

    if needs_underscore {
        identifier.push('_');
    }

    // Default to "_" if the provided text was empty
    if identifier.is_empty() {
        return "_".to_string();
    }
    identifier
}

/// `getCompletionsSymbolKind` — copied from vscode TS extension.
fn get_completions_symbol_kind(
    kind: tsc_lsutil::symbol_display::ScriptElementKind,
) -> lsproto::CompletionItemKind {
    use tsc_lsutil::symbol_display::ScriptElementKind as S;
    match kind {
        S::PrimitiveType | S::Keyword => lsproto::CompletionItemKind::Keyword,
        S::ConstElement
        | S::LetElement
        | S::VariableElement
        | S::LocalVariableElement
        | S::Alias
        | S::ParameterElement => lsproto::CompletionItemKind::Variable,
        S::MemberVariableElement | S::MemberGetAccessorElement | S::MemberSetAccessorElement => {
            lsproto::CompletionItemKind::Field
        }
        S::FunctionElement | S::LocalFunctionElement => lsproto::CompletionItemKind::Function,
        S::MemberFunctionElement
        | S::ConstructSignatureElement
        | S::CallSignatureElement
        | S::IndexSignatureElement => lsproto::CompletionItemKind::Method,
        S::EnumElement => lsproto::CompletionItemKind::Enum,
        S::EnumMemberElement => lsproto::CompletionItemKind::EnumMember,
        S::ModuleElement | S::ExternalModuleName => lsproto::CompletionItemKind::Module,
        S::ClassElement | S::TypeElement => lsproto::CompletionItemKind::Class,
        S::InterfaceElement => lsproto::CompletionItemKind::Interface,
        S::Warning => lsproto::CompletionItemKind::Text,
        S::ScriptElement => lsproto::CompletionItemKind::File,
        S::Directory => lsproto::CompletionItemKind::Folder,
        S::String => lsproto::CompletionItemKind::Constant,
        _ => lsproto::CompletionItemKind::Property,
    }
}

/// `CompareCompletionEntries`.
pub(crate) fn compare_completion_entries(
    a: &LspCompletionItem,
    b: &LspCompletionItem,
) -> tsc_stringutil::Comparison {
    let compare_strings = tsc_stringutil::compare_strings_case_insensitive_then_sensitive;
    let result = compare_strings(
        a.sort_text.as_deref().unwrap_or("").as_bytes(),
        b.sort_text.as_deref().unwrap_or("").as_bytes(),
    );
    if result == tsc_stringutil::COMPARISON_EQUAL {
        return compare_strings(a.label.as_bytes(), b.label.as_bytes());
    }
    result
}

/// Keyword names for `Kind::FIRST_KEYWORD..=Kind::LAST_KEYWORD`
/// (`BreakKeyword..=SourceKeyword`); Go iterates the kind range and calls
/// `scanner.TokenToString`, which yields exactly these strings.
const KEYWORD_NAMES: &[&str] = &[
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "null",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "implements",
    "interface",
    "let",
    "package",
    "private",
    "protected",
    "public",
    "static",
    "yield",
    "abstract",
    "accessor",
    "as",
    "asserts",
    "assert",
    "any",
    "async",
    "await",
    "boolean",
    "constructor",
    "declare",
    "get",
    "immediate",
    "infer",
    "intrinsic",
    "is",
    "keyof",
    "module",
    "namespace",
    "never",
    "out",
    "readonly",
    "require",
    "number",
    "object",
    "satisfies",
    "set",
    "string",
    "symbol",
    "type",
    "undefined",
    "unique",
    "unknown",
    "using",
    "from",
    "global",
    "bigint",
    "override",
    "of",
    "defer",
    "source",
];

/// `allKeywordCompletions` — memoized like Go's `sync.OnceValue`.
fn all_keyword_completions() -> &'static Vec<LspCompletionItem> {
    static ALL: std::sync::OnceLock<Vec<LspCompletionItem>> = std::sync::OnceLock::new();
    ALL.get_or_init(|| {
        KEYWORD_NAMES
            .iter()
            .map(|name| LspCompletionItem {
                label: name.to_string(),
                kind: Some(lsproto::CompletionItemKind::Keyword),
                sort_text: Some(sort_text::GLOBALS_OR_KEYWORDS.to_string()),
                ..Default::default()
            })
            .collect()
    })
}

/// `cloneItems`.
fn clone_items(items: &[LspCompletionItem]) -> Vec<CompletionItem> {
    items
        .iter()
        .map(|item| CompletionItem {
            item: item.clone(),
            symbol: None,
        })
        .collect()
}

/// `getKeywordCompletions`.
fn get_keyword_completions(
    keyword_filter: KeywordCompletionFilters,
    filter_out_ts_only_keywords: bool,
) -> Vec<CompletionItem> {
    if !filter_out_ts_only_keywords {
        return clone_items(&get_typescript_keyword_completions(keyword_filter));
    }
    let filtered = get_typescript_keyword_completions(keyword_filter)
        .into_iter()
        .filter(|ci| !is_type_script_only_keyword(tsc_scanner::scanner::string_to_token(&ci.label)))
        .collect::<Vec<_>>();
    clone_items(&filtered)
}

/// `getTypescriptKeywordCompletions`.
fn get_typescript_keyword_completions(
    keyword_filter: KeywordCompletionFilters,
) -> Vec<LspCompletionItem> {
    all_keyword_completions()
        .iter()
        .filter(|entry| {
            let kind = tsc_scanner::scanner::string_to_token(&entry.label);
            match keyword_filter {
                KeywordCompletionFilters::NONE => false,
                KeywordCompletionFilters::ALL => {
                    is_function_like_body_keyword(kind)
                        || kind == Kind::DeclareKeyword
                        || kind == Kind::ModuleKeyword
                        || kind == Kind::TypeKeyword
                        || kind == Kind::NamespaceKeyword
                        || kind == Kind::AbstractKeyword
                        || crate::utilities::is_type_keyword(kind) && kind != Kind::UndefinedKeyword
                }
                KeywordCompletionFilters::FUNCTION_LIKE_BODY_KEYWORDS => {
                    is_function_like_body_keyword(kind)
                }
                KeywordCompletionFilters::CLASS_ELEMENT_KEYWORDS => {
                    is_class_member_completion_keyword(kind)
                }
                KeywordCompletionFilters::INTERFACE_ELEMENT_KEYWORDS => {
                    is_interface_or_type_literal_completion_keyword(kind)
                }
                KeywordCompletionFilters::CONSTRUCTOR_PARAMETER_KEYWORDS => {
                    ast::is_parameter_property_modifier(kind)
                }
                KeywordCompletionFilters::TYPE_ASSERTION_KEYWORDS => {
                    crate::utilities::is_type_keyword(kind) || kind == Kind::ConstKeyword
                }
                KeywordCompletionFilters::TYPE_KEYWORDS => crate::utilities::is_type_keyword(kind),
                KeywordCompletionFilters::TYPE_KEYWORD => kind == Kind::TypeKeyword,
                _ => panic!("Unknown keyword filter: {}", keyword_filter.0),
            }
        })
        .cloned()
        .collect()
}

/// `isTypeScriptOnlyKeyword`.
fn is_type_script_only_keyword(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::AbstractKeyword
            | Kind::AnyKeyword
            | Kind::BigIntKeyword
            | Kind::BooleanKeyword
            | Kind::DeclareKeyword
            | Kind::EnumKeyword
            | Kind::GlobalKeyword
            | Kind::ImplementsKeyword
            | Kind::InferKeyword
            | Kind::InterfaceKeyword
            | Kind::IsKeyword
            | Kind::KeyOfKeyword
            | Kind::ModuleKeyword
            | Kind::NamespaceKeyword
            | Kind::NeverKeyword
            | Kind::NumberKeyword
            | Kind::ObjectKeyword
            | Kind::OverrideKeyword
            | Kind::PrivateKeyword
            | Kind::ProtectedKeyword
            | Kind::PublicKeyword
            | Kind::ReadonlyKeyword
            | Kind::StringKeyword
            | Kind::SymbolKeyword
            | Kind::TypeKeyword
            | Kind::UniqueKeyword
            | Kind::UnknownKeyword
    )
}

/// `isFunctionLikeBodyKeyword`.
fn is_function_like_body_keyword(kind: Kind) -> bool {
    kind == Kind::AsyncKeyword
        || kind == Kind::AwaitKeyword
        || kind == Kind::UsingKeyword
        || kind == Kind::AsKeyword
        || kind == Kind::SatisfiesKeyword
        || kind == Kind::TypeKeyword
        || !ast::is_contextual_keyword(kind) && !is_class_member_completion_keyword(kind)
}

/// `isClassMemberCompletionKeyword`.
fn is_class_member_completion_keyword(kind: Kind) -> bool {
    match kind {
        Kind::AbstractKeyword
        | Kind::AccessorKeyword
        | Kind::ConstructorKeyword
        | Kind::GetKeyword
        | Kind::SetKeyword
        | Kind::AsyncKeyword
        | Kind::DeclareKeyword
        | Kind::OverrideKeyword => true,
        _ => ast::is_class_member_modifier(kind),
    }
}

/// `isInterfaceOrTypeLiteralCompletionKeyword`.
fn is_interface_or_type_literal_completion_keyword(kind: Kind) -> bool {
    kind == Kind::ReadonlyKeyword
}

/// `isContextualKeywordInAutoImportableExpressionSpace`.
fn is_contextual_keyword_in_auto_importable_expression_space(keyword: &str) -> bool {
    matches!(
        keyword,
        "abstract"
            | "async"
            | "await"
            | "declare"
            | "module"
            | "namespace"
            | "type"
            | "satisfies"
            | "as"
    )
}

/// `getContextualKeywords`.
fn get_contextual_keywords(
    nodes: &[Node],
    file: NodeId,
    context_token: Option<NodeId>,
    position: TextPos,
) -> Vec<LspCompletionItem> {
    let mut entries: Vec<LspCompletionItem> = Vec::new();
    // An `AssertClause` can come after an import declaration:
    //  import * from "foo" |
    //  import "foo" |
    // or after a re-export declaration that has a module specifier:
    //  export { foo } from "foo" |
    // Source: https://tc39.es/proposal-import-assertions/
    if let Some(context_token) = context_token {
        let parent = nodes[context_token].parent;
        let token_line = get_line_of_position(nodes, file, nodes[context_token].end());
        let current_line = get_line_of_position(nodes, file, position);
        let is_module_specifier = parent.is_some_and(|parent| {
            (ast::is_import_declaration(&nodes[parent])
                || ast::is_export_declaration(&nodes[parent])
                    && nodes[parent].module_specifier().is_some())
                && nodes[parent].module_specifier() == Some(context_token)
        });
        if is_module_specifier && token_line == current_line {
            entries.push(LspCompletionItem {
                label: tsc_scanner::scanner::token_to_string(Kind::AssertKeyword).to_string(),
                kind: Some(lsproto::CompletionItemKind::Keyword),
                sort_text: Some(sort_text::GLOBALS_OR_KEYWORDS.to_string()),
                ..Default::default()
            });
        }
    }
    entries
}

/// `completionNameForLiteral`.
fn completion_name_for_literal(
    nodes: &[Node],
    file: NodeId,
    preferences: &UserPreferences,
    literal: &LiteralValue,
) -> String {
    match literal {
        LiteralValue::Str(s) => crate::utilities::quote(nodes, file, preferences, s),
        LiteralValue::Number(n) => n.to_string(),
        LiteralValue::PseudoBigInt(b) => format!("{}n", b),
    }
}

/// `createCompletionItemForLiteral`.
fn create_completion_item_for_literal(
    nodes: &[Node],
    file: NodeId,
    preferences: &UserPreferences,
    literal: &LiteralValue,
) -> LspCompletionItem {
    LspCompletionItem {
        label: completion_name_for_literal(nodes, file, preferences, literal),
        kind: Some(lsproto::CompletionItemKind::Constant),
        sort_text: Some(sort_text::LOCATION_PRIORITY.to_string()),
        commit_characters: Some(Vec::new()),
        ..Default::default()
    }
}

impl LanguageService<'_> {
    /// `getOptionalReplacementSpan` — `location` is `Option<NodeId>`
    /// (`*ast.Node`).
    pub(crate) fn get_optional_replacement_span(
        &self,
        location: Option<NodeId>,
        file: NodeId,
    ) -> Option<lsproto::Range> {
        // StringLiteralLike locations are handled separately in stringCompletions.
        if let Some(location) = location {
            let program = self.get_program();
            let kind = {
                let nodes = program.nodes(file.file_index());
                nodes[location].kind
            };
            if matches!(kind, Kind::Identifier | Kind::PrivateIdentifier) {
                let start = {
                    let mut nodes = program.nodes_mut(file.file_index());
                    tsc_astnav::tokens::get_start_of_node(
                        &mut nodes, file, location, false, /*includeJSDoc*/
                    )
                };
                let end = program.nodes(file.file_index())[location].end();
                let (lsp_range, fidelity) = self.create_lsp_range_from_bounds(start, end, file);
                if fidelity.is_exact() {
                    return Some(lsp_range);
                }
            }
        }
        None
    }

    /// `setItemDefaults`.
    pub(crate) fn set_item_defaults(
        &self,
        ctx: &Context,
        position: TextPos,
        file: NodeId,
        items: &mut [CompletionItem],
        default_commit_characters: Option<&Vec<String>>,
        optional_replacement_span: Option<&lsproto::Range>,
    ) -> Option<lsproto::CompletionItemDefaults> {
        let mut item_defaults: Option<lsproto::CompletionItemDefaults> = None;
        if let Some(default_commit_characters) = default_commit_characters {
            let supports_item_commit_characters = client_supports_item_commit_characters(ctx);
            if client_supports_default_commit_characters(ctx) && supports_item_commit_characters {
                item_defaults = Some(lsproto::CompletionItemDefaults {
                    commit_characters: Some(default_commit_characters.clone()),
                    ..Default::default()
                });
            } else if supports_item_commit_characters {
                for item in items.iter_mut() {
                    if item.item.commit_characters.is_none() {
                        item.item.commit_characters = Some(default_commit_characters.clone());
                    }
                }
            }
        }
        if let Some(optional_replacement_span) = optional_replacement_span {
            // Ported from vscode ts extension.
            let (end, fidelity) = self.create_lsp_position(position, file);
            if !fidelity.is_exact() {
                return item_defaults;
            }
            let insert_range = lsproto::Range {
                start: optional_replacement_span.start,
                end,
            };
            if client_supports_default_edit_range(ctx) {
                item_defaults
                    .get_or_insert_with(Default::default)
                    .edit_range = Some(lsproto::RangeOrEditRangeWithInsertReplace {
                    range: None,
                    edit_range_with_insert_replace: Some(lsproto::EditRangeWithInsertReplace {
                        insert: insert_range.clone(),
                        replace: optional_replacement_span.clone(),
                    }),
                });
                for item in items.iter_mut() {
                    // If `edit_range` is set, `insert_text` is ignored by the client, so we need to
                    // provide `text_edit` instead.
                    if item.item.insert_text.is_some() && item.item.text_edit.is_none() {
                        item.item.text_edit = Some(lsproto::TextEditOrInsertReplaceEdit {
                            text_edit: None,
                            insert_replace_edit: Some(lsproto::InsertReplaceEdit {
                                new_text: item.item.insert_text.clone().unwrap_or_default(),
                                insert: insert_range.clone(),
                                replace: optional_replacement_span.clone(),
                            }),
                        });
                        item.item.insert_text = None;
                    }
                }
            } else if client_supports_item_insert_replace(ctx) {
                for item in items.iter_mut() {
                    if item.item.text_edit.is_none() {
                        let new_text = item
                            .item
                            .insert_text
                            .clone()
                            .unwrap_or_else(|| item.item.label.clone());
                        item.item.text_edit = Some(lsproto::TextEditOrInsertReplaceEdit {
                            text_edit: None,
                            insert_replace_edit: Some(lsproto::InsertReplaceEdit {
                                new_text,
                                insert: insert_range.clone(),
                                replace: optional_replacement_span.clone(),
                            }),
                        });
                    }
                }
            }
        }

        item_defaults
    }

    /// `specificKeywordCompletionInfo`.
    fn specific_keyword_completion_info(
        &self,
        ctx: &Context,
        position: TextPos,
        file: NodeId,
        mut items: Vec<CompletionItem>,
        is_new_identifier_location: bool,
        optional_replacement_span: Option<lsproto::Range>,
    ) -> CompletionList {
        let default_commit_characters = get_default_commit_characters(is_new_identifier_location);
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            optional_replacement_span.as_ref(),
        );
        CompletionList {
            is_incomplete: false,
            item_defaults,
            items: items.into_iter().map(Some).collect(),
            ..Default::default()
        }
    }

    /// `jsDocCompletionInfo`.
    fn js_doc_completion_info(
        &self,
        ctx: &Context,
        position: TextPos,
        file: NodeId,
        mut items: Vec<CompletionItem>,
    ) -> CompletionList {
        let default_commit_characters = get_default_commit_characters(false);
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            None,
        );
        CompletionList {
            is_incomplete: false,
            item_defaults,
            items: items.into_iter().map(Some).collect(),
            ..Default::default()
        }
    }

    /// `getJsxClosingTagCompletion`.
    fn get_jsx_closing_tag_completion(
        &self,
        ctx: &Context,
        location: Option<NodeId>,
        file: NodeId,
        position: TextPos,
    ) -> Option<CompletionList> {
        let program = self.get_program();
        // We wanna walk up the tree till we find a JSX closing element.
        let jsx_closing_element = {
            let nodes = program.nodes(file.file_index());
            ast::find_ancestor_or_quit(location, &nodes, &mut |node, _| match node.kind {
                Kind::JsxClosingElement => ast::FindAncestorResult::True,
                Kind::LessThanSlashToken
                | Kind::GreaterThanToken
                | Kind::Identifier
                | Kind::PropertyAccessExpression => ast::FindAncestorResult::False,
                _ => ast::FindAncestorResult::Quit,
            })
        };
        let jsx_closing_element = jsx_closing_element?;

        // In the TypeScript JSX element, if such element is not defined. When users query for
        // completion at closing tag, instead of simply giving unknown value, the completion
        // will return the tag-name of an associated opening-element.
        let has_closing_angle_bracket = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::find_child_of_kind(
                &mut nodes,
                file,
                jsx_closing_element,
                Kind::GreaterThanToken,
            )
            .is_some()
        };
        let closing_tag = {
            let nodes = program.nodes(file.file_index());
            let opening_element = nodes[nodes[jsx_closing_element]
                .parent
                .expect("closing tag parent")]
            .as_jsx_element()
            .opening_element
            .expect("opening element");
            tsc_scanner::utilities::get_text_of_node(
                nodes[opening_element].tag_name().expect("tag name"),
                &nodes,
            )
        };
        let full_closing_tag = if has_closing_angle_bracket {
            closing_tag
        } else {
            format!("{closing_tag}>")
        };
        let tag_name_node = {
            let nodes = program.nodes(file.file_index());
            nodes[jsx_closing_element]
                .tag_name()
                .expect("closing tag name")
        };
        let (optional_replacement_span, fidelity) =
            self.create_lsp_range_from_node(tag_name_node, file);
        if !fidelity.is_exact() {
            return None;
        }
        let default_commit_characters = get_default_commit_characters(false);

        let lsp_item = self.create_lsp_completion_item(
            ctx,
            full_closing_tag.clone(), /*name*/
            "",                       /*insertText*/
            "",                       /*filterText*/
            sort_text::LOCATION_PRIORITY.to_string(),
            tsc_lsutil::symbol_display::ScriptElementKind::ClassElement,
            tsc_lsutil::symbol_display::ScriptElementKindModifier::NONE,
            None, /*replacementSpan*/
            None, /*commitCharacters*/
            None, /*labelDetails*/
            file,
            position,
            true,  /*isMemberCompletion*/
            false, /*isSnippet*/
            false, /*hasAction*/
            false, /*preselect*/
            "",    /*source*/
            None,  /*autoImportEntryData*/
            // !!! jsx autoimports
            None, /*additionalTextEdits*/
            None, /*detail*/
        );
        let item = CompletionItem {
            item: lsp_item,
            symbol: None,
        };
        let mut items = vec![item];
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            Some(&optional_replacement_span),
        );

        Some(CompletionList {
            is_incomplete: false,
            item_defaults,
            items: items.into_iter().map(Some).collect(),
            ..Default::default()
        })
    }

    /// `createLSPCompletionItem`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn create_lsp_completion_item(
        &self,
        ctx: &Context,
        name: String,
        insert_text: &str,
        filter_text: &str,
        sort_text: SortText,
        element_kind: tsc_lsutil::symbol_display::ScriptElementKind,
        kind_modifiers: tsc_lsutil::symbol_display::ScriptElementKindModifier,
        replacement_span: Option<&lsproto::Range>,
        commit_characters: Option<Vec<String>>,
        label_details: Option<lsproto::CompletionItemLabelDetails>,
        file: NodeId,
        position: TextPos,
        is_member_completion: bool,
        is_snippet: bool,
        has_action: bool,
        preselect: bool,
        source: &str,
        auto_import_fix: Option<lsproto::AutoImportFix>,
        additional_text_edits: Option<Vec<lsproto::TextEdit>>,
        detail: Option<String>,
    ) -> LspCompletionItem {
        let kind = get_completions_symbol_kind(element_kind);
        let (original_file_name, supplemental_file_index) = {
            let program = self.get_program();
            let nodes = program.nodes(file.file_index());
            (
                nodes[file]
                    .as_source_file()
                    .original_file_name(&nodes)
                    .as_string()
                    .to_string(),
                supplemental_file_index(&nodes, file),
            )
        };
        let data = Some(lsproto::CompletionItemData {
            file_name: original_file_name,
            position,
            supplemental_file_index,
            source: source.to_string(),
            name: name.clone(),
            auto_import: auto_import_fix,
            ..Default::default()
        });

        // Text edit
        let text_edit =
            replacement_span.map(|replacement_span| lsproto::TextEditOrInsertReplaceEdit {
                text_edit: Some(lsproto::TextEdit {
                    new_text: if insert_text.is_empty() {
                        name.clone()
                    } else {
                        insert_text.to_string()
                    },
                    range: replacement_span.clone(),
                }),
                insert_replace_edit: None,
            });

        // Filter text — ported from vscode ts extension.
        let program = self.get_program();
        let mut name = name;
        let mut insert_text = insert_text.to_string();
        let mut filter_text = filter_text.to_string();
        let (word_size, word_start) = {
            let nodes = program.nodes(file.file_index());
            get_word_length_and_start(&nodes, file, position)
        };
        let dot_accessor = {
            let nodes = program.nodes(file.file_index());
            get_dot_accessor(&nodes, file, position - word_size as i32)
        };
        if filter_text.is_empty() {
            filter_text = {
                let nodes = program.nodes(file.file_index());
                get_filter_text(
                    &nodes,
                    file,
                    position,
                    &insert_text,
                    &name,
                    word_start,
                    &dot_accessor,
                )
            };
        }

        // Adjustments based on kind modifiers.
        let mut tags = None;
        // Copied from vscode ts extension: `MyCompletionItem.constructor`.
        if is_member_completion
            && kind_modifiers
                .intersects(tsc_lsutil::symbol_display::ScriptElementKindModifier::OPTIONAL)
        {
            if insert_text.is_empty() {
                insert_text = name.clone();
            }
            if filter_text.is_empty() || is_snippet {
                filter_text = name.clone();
            }
            name = format!("{name}?");
        }
        if kind_modifiers
            .intersects(tsc_lsutil::symbol_display::ScriptElementKindModifier::DEPRECATED)
        {
            tags = Some(vec![lsproto::CompletionItemTag::Deprecated]);
        }

        if has_action && !source.is_empty() {
            // !!! adjust label like vscode does
        }

        // Client assumes plain text by default.
        let insert_text_format = if is_snippet {
            Some(lsproto::InsertTextFormat::Snippet)
        } else {
            None
        };

        LspCompletionItem {
            label: name,
            label_details,
            kind: Some(kind),
            tags,
            detail,
            preselect: if preselect { Some(true) } else { None },
            sort_text: Some(sort_text),
            filter_text: if filter_text.is_empty() {
                None
            } else {
                Some(filter_text)
            },
            insert_text: if insert_text.is_empty() {
                None
            } else {
                Some(insert_text)
            },
            insert_text_format,
            text_edit,
            commit_characters,
            additional_text_edits,
            data,
            ..Default::default()
        }
    }

    /// `getLabelCompletionsAtPosition` — `node` is the parent
    /// `*ast.BreakOrContinueStatement`.
    fn get_label_completions_at_position(
        &self,
        ctx: &Context,
        node: NodeId,
        file: NodeId,
        position: TextPos,
        optional_replacement_span: Option<lsproto::Range>,
    ) -> CompletionList {
        let mut items = self.get_label_statement_completions(ctx, node, file, position);
        if items.is_empty() {
            return CompletionList::default();
        }
        let default_commit_characters = get_default_commit_characters(false);
        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut items,
            Some(&default_commit_characters),
            optional_replacement_span.as_ref(),
        );
        CompletionList {
            is_incomplete: false,
            item_defaults,
            items: items.into_iter().map(Some).collect(),
            ..Default::default()
        }
    }

    /// `getLabelStatementCompletions`.
    fn get_label_statement_completions(
        &self,
        ctx: &Context,
        node: NodeId,
        file: NodeId,
        position: TextPos,
    ) -> Vec<CompletionItem> {
        let program = self.get_program();
        let mut uniques: Set<String> = Set::default();
        let mut items = Vec::new();
        let mut current = Some(node);
        while let Some(cur) = current {
            let (is_function_like, label_name, parent) = {
                let nodes = program.nodes(file.file_index());
                (
                    ast::is_function_like(Some(cur), &nodes),
                    if ast::is_labeled_statement(&nodes[cur]) {
                        nodes[cur]
                            .label()
                            .map(|l| nodes[l].text(&nodes).to_string())
                    } else {
                        None
                    },
                    nodes[cur].parent,
                )
            };
            if is_function_like {
                break;
            }
            if let Some(name) = label_name {
                if !uniques.has(&name) {
                    uniques.add(name.clone());
                    let lsp_item = self.create_lsp_completion_item(
                        ctx,
                        name, /*name*/
                        "",   /*insertText*/
                        "",   /*filterText*/
                        sort_text::LOCATION_PRIORITY.to_string(),
                        tsc_lsutil::symbol_display::ScriptElementKind::Label,
                        tsc_lsutil::symbol_display::ScriptElementKindModifier::NONE,
                        None, /*replacementSpan*/
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
            }
            current = parent;
        }
        items
    }

    /// `getImportStatementCompletionInfo` — see Go for when this is a known
    /// invalid completion location.
    fn get_import_statement_completion_info(
        &self,
        context_token: NodeId,
        source_file: NodeId,
    ) -> ImportStatementCompletionInfo {
        let program = self.get_program();
        let mut result = ImportStatementCompletionInfo::default();
        let mut candidate: Option<NodeId> = None;
        {
            let mut nodes = program.nodes_mut(source_file.file_index());
            let nodes = &mut *nodes;
            let parent = nodes[context_token].parent;
            if let Some(parent) = parent {
                let context_kind = nodes[context_token].kind;
                if ast::is_import_equals_declaration(&nodes[parent]) {
                    // import Foo |
                    // import Foo f|
                    let last_token =
                        tsc_lsutil::children::get_last_token(nodes, Some(parent), source_file);
                    if context_kind == Kind::Identifier && last_token != Some(context_token) {
                        result.keyword_completion = Kind::FromKeyword;
                        result.is_keyword_only_completion = true;
                    } else {
                        if context_kind != Kind::TypeKeyword {
                            result.keyword_completion = Kind::TypeKeyword;
                        }
                        if is_module_specifier_missing_or_empty(
                            nodes[parent]
                                .as_import_equals_declaration()
                                .module_reference,
                            nodes,
                        ) {
                            candidate = Some(parent);
                        }
                    }
                } else if could_be_type_only_import_specifier(parent, context_token, nodes)
                    && nodes[parent]
                        .parent
                        .is_some_and(|p| can_complete_from_named_bindings(p, nodes))
                {
                    candidate = Some(parent);
                } else if ast::is_named_imports(&nodes[parent])
                    || ast::is_namespace_import(&nodes[parent])
                {
                    if !nodes[parent]
                        .parent
                        .is_some_and(|p| nodes[p].is_type_only())
                        && matches!(
                            context_kind,
                            Kind::OpenBraceToken | Kind::ImportKeyword | Kind::CommaToken
                        )
                    {
                        result.keyword_completion = Kind::TypeKeyword;
                    }
                    if can_complete_from_named_bindings(parent, nodes) {
                        // At `import { ... } |` or `import * as Foo |`, the only possible completion is `from`
                        if matches!(context_kind, Kind::CloseBraceToken | Kind::Identifier) {
                            result.is_keyword_only_completion = true;
                            result.keyword_completion = Kind::FromKeyword;
                        } else {
                            candidate = nodes[parent].parent.and_then(|p| nodes[p].parent);
                        }
                    }
                } else if (ast::is_export_declaration(&nodes[parent])
                    && context_kind == Kind::AsteriskToken)
                    || (ast::is_named_exports(&nodes[parent])
                        && context_kind == Kind::CloseBraceToken)
                {
                    result.is_keyword_only_completion = true;
                    result.keyword_completion = Kind::FromKeyword;
                } else if context_kind == Kind::ImportKeyword {
                    if nodes[parent].kind == Kind::SourceFile {
                        // A lone import keyword with nothing following it does not parse as a statement at all
                        result.keyword_completion = Kind::TypeKeyword;
                        candidate = Some(context_token);
                    } else if ast::is_import_declaration(&nodes[parent]) {
                        // `import s| from`
                        result.keyword_completion = Kind::TypeKeyword;
                        if is_module_specifier_missing_or_empty(
                            nodes[parent].module_specifier(),
                            nodes,
                        ) {
                            candidate = Some(parent);
                        }
                    }
                }
            }
        }

        if let Some(candidate) = candidate {
            result.is_new_identifier_location = true;
            result.replacement_span =
                self.get_single_line_replacement_span_for_import_completion_node(candidate);
            {
                let nodes = program.nodes(source_file.file_index());
                result.could_be_type_only_import_specifier =
                    could_be_type_only_import_specifier(candidate, context_token, &nodes);
                if ast::is_import_declaration(&nodes[candidate]) {
                    if let Some(import_clause) = nodes[candidate].import_clause() {
                        result.is_top_level_type_only = nodes[import_clause].is_type_only();
                    }
                } else if nodes[candidate].kind == Kind::ImportEqualsDeclaration {
                    result.is_top_level_type_only = nodes[candidate].is_type_only();
                }
            }
        } else {
            result.is_new_identifier_location = result.keyword_completion == Kind::TypeKeyword;
        }
        result
    }

    /// `getSingleLineReplacementSpanForImportCompletionNode` — `node` is
    /// `ImportDeclaration | ImportEqualsDeclaration | ImportSpecifier |
    /// JSDocImportTag | Token<SyntaxKind.ImportKeyword>`.
    fn get_single_line_replacement_span_for_import_completion_node(
        &self,
        node: NodeId,
    ) -> Option<lsproto::Range> {
        let program = self.get_program();
        let node = {
            let nodes = program.nodes(node.file_index());
            ast::find_ancestor(Some(node), &nodes, &mut |n, _| {
                ast::is_import_declaration(n)
                    || ast::is_import_equals_declaration(n)
                    || ast::is_js_doc_import_tag(n)
            })
            .unwrap_or(node)
        };
        let source_file = {
            let nodes = program.nodes(node.file_index());
            ast::get_source_file_of_node(Some(node), &nodes)
        }?;
        // Use token position (excluding JSDoc/trivia) instead of node.Pos() to avoid
        // including JSDoc comments.
        let (token_pos, node_end) = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            (
                tsc_scanner::scanner::get_token_pos_of_node(
                    node,
                    nodes[source_file].as_source_file(),
                    false, /*includeJSDoc*/
                    &nodes,
                ),
                nodes[node].end(),
            )
        };
        if {
            let nodes = program.nodes(source_file.file_index());
            get_line_of_position(&nodes, source_file, token_pos)
                == get_line_of_position(&nodes, source_file, node_end)
        } {
            let (lsp_range, fidelity) = self.create_lsp_range_from_node(node, source_file);
            if !fidelity.is_exact() {
                return None;
            }
            return Some(lsp_range);
        }

        debug_assert!(
            !matches!(
                program.nodes(node.file_index())[node].kind,
                Kind::ImportKeyword | Kind::ImportSpecifier
            ),
            "ImportKeyword was necessarily on one line; ImportSpecifier was necessarily parented in an ImportDeclaration"
        );

        // Guess which point in the import might actually be a later statement parsed as part of the
        // import during parser recovery - either in the middle of named imports, or the module specifier.
        let potential_split_point = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            let node_kind = nodes[node].kind;
            if node_kind == Kind::ImportDeclaration || node_kind == Kind::JSDocImportTag {
                let named_bindings = nodes[node]
                    .import_clause()
                    .map(|import_clause| nodes[import_clause].as_import_clause().named_bindings);
                let specifier = named_bindings.and_then(|named_bindings| {
                    get_potentially_invalid_import_specifier(named_bindings, &mut nodes)
                });
                specifier.or_else(|| nodes[node].module_specifier())
            } else {
                nodes[node].as_import_equals_declaration().module_reference
            }
        }?;
        // The module specifier/reference was previously found to be missing, empty, or
        // not a string literal - in this last case, it's likely that statement on a following
        // line was parsed as the module specifier of a partially-typed import, e.g.
        //   import Foo|
        //   interface Blah {}
        // This appears to be a multiline-import, and editors can't replace multiple lines.
        // But if everything but the "module specifier" is on one line, by this point we can
        // assume that the "module specifier" is actually just another statement, and return
        // the single-line range of the import excluding that probable statement.
        let without_module_specifier = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            let first_token = tsc_lsutil::children::get_first_token(&mut nodes, node, source_file);
            first_token.map(|first_token| {
                TextRange::new(
                    tsc_scanner::scanner::get_token_pos_of_node(
                        first_token,
                        nodes[source_file].as_source_file(),
                        false, /*includeJSDoc*/
                        &nodes,
                    ),
                    nodes[potential_split_point].pos(),
                )
            })
        }?;
        if {
            let nodes = program.nodes(source_file.file_index());
            get_line_of_position(&nodes, source_file, without_module_specifier.pos())
                == get_line_of_position(&nodes, source_file, without_module_specifier.end())
        } {
            let (lsp_range, fidelity) = self.create_lsp_range_from_bounds(
                without_module_specifier.pos(),
                without_module_specifier.end(),
                source_file,
            );
            if !fidelity.is_exact() {
                return None;
            }
            return Some(lsp_range);
        }
        None
    }

    /// `getJSCompletionEntries`.
    fn get_js_completion_entries(
        &self,
        _ctx: &Context,
        file: NodeId,
        position: TextPos,
        unique_names: &mut Set<String>,
        sorted_entries: &mut Vec<CompletionItem>,
    ) {
        let program = self.get_program();
        let mut nodes = program.nodes_mut(file.file_index());
        let name_table = ast::get_name_table(&mut nodes, file);
        for (name, pos) in name_table.clone().iter() {
            // Skip identifiers produced only from the current location
            if *pos == position {
                continue;
            }
            if !unique_names.has(name)
                && tsc_scanner::utilities::is_identifier_text(
                    name,
                    tsc_core::languagevariant::LanguageVariant::Standard,
                )
            {
                unique_names.add(name.clone());
                sorted_entries.push(CompletionItem {
                    item: LspCompletionItem {
                        label: name.clone(),
                        kind: Some(lsproto::CompletionItemKind::Text),
                        sort_text: Some(sort_text::JAVASCRIPT_IDENTIFIERS.to_string()),
                        commit_characters: Some(Vec::new()),
                        ..Default::default()
                    },
                    symbol: None,
                });
            }
        }
    }
}

/// `couldBeTypeOnlyImportSpecifier`.
fn could_be_type_only_import_specifier(
    import_specifier: NodeId,
    context_token: NodeId,
    nodes: &[Node],
) -> bool {
    ast::is_import_specifier(&nodes[import_specifier])
        && (nodes[import_specifier].is_type_only()
            || (Some(context_token) == nodes[import_specifier].name()
                && is_type_keyword_token_or_identifier(&nodes[context_token], nodes)))
}

/// `canCompleteFromNamedBindings` — `named_bindings` is
/// `*ast.NamedImportBindings` (NamedImports | NamespaceImport).
fn can_complete_from_named_bindings(named_bindings: NodeId, nodes: &mut Vec<Node>) -> bool {
    let declaration = nodes[named_bindings].parent.and_then(|p| nodes[p].parent);
    let Some(declaration) = declaration else {
        return false;
    };
    if !is_module_specifier_missing_or_empty(nodes[declaration].module_specifier(), nodes)
        || nodes[declaration].name().is_some()
    {
        return false;
    }
    if ast::is_named_imports(&nodes[named_bindings]) {
        // We can only complete on named imports if there are no other named imports already,
        // but parser recovery sometimes puts later statements in the named imports list, so
        // we try to only consider the probably-valid ones.
        let invalid_named_import =
            get_potentially_invalid_import_specifier(Some(named_bindings), nodes);
        let elements = nodes[named_bindings].elements().unwrap_or(&[]).to_vec();
        let valid_imports = match invalid_named_import {
            Some(invalid_named_import) => elements
                .iter()
                .position(|&e| e == invalid_named_import)
                .map(|i| i as i32)
                .unwrap_or(-1),
            None => elements.len() as i32,
        };
        return (0..2).contains(&valid_imports);
    }
    true
}

/// `getPotentiallyInvalidImportSpecifier` — tries to identify the first named
/// import that is not really a named import, but rather just parser recovery
/// for a situation like:
///
/// ```text
/// import { Foo|
/// interface Bar {}
/// ```
///
/// in which `Foo`, `interface`, and `Bar` are all parsed as import specifiers.
/// The caller will also check if this token is on a separate line from the
/// rest of the import.
fn get_potentially_invalid_import_specifier(
    named_bindings: Option<NodeId>,
    nodes: &mut Vec<Node>,
) -> Option<NodeId> {
    let named_bindings = named_bindings?;
    if nodes[named_bindings].kind != Kind::NamedImports {
        return None;
    }
    let elements: Vec<NodeId> = nodes[named_bindings].elements().unwrap_or(&[]).to_vec();
    elements.into_iter().find(|&e| {
        if nodes[e].property_name().is_some() {
            return false;
        }
        let Some(name) = nodes[e].name() else {
            return false;
        };
        if !tsc_lsutil::utilities::is_non_contextual_keyword(tsc_scanner::scanner::string_to_token(
            &nodes[name].text(&nodes),
        )) {
            return false;
        }
        let source_file = match ast::get_source_file_of_node(Some(named_bindings), nodes) {
            Some(source_file) => source_file,
            None => return false,
        };
        tsc_astnav::tokens::find_preceding_token(nodes, source_file, nodes[name].pos())
            .is_some_and(|t| nodes[t].kind != Kind::CommaToken)
    })
}

/// `isModuleSpecifierMissingOrEmpty`.
fn is_module_specifier_missing_or_empty(specifier: Option<NodeId>, nodes: &[Node]) -> bool {
    if ast::node_is_missing(specifier, nodes) {
        return true;
    }
    let Some(mut specifier) = specifier else {
        return false;
    };
    if ast::is_external_module_reference(&nodes[specifier]) {
        let Some(expr) = nodes[specifier].expression() else {
            return true;
        };
        specifier = expr;
    }
    if !ast::is_string_literal_like(&nodes[specifier]) {
        return true;
    }
    nodes[specifier].text(&nodes).is_empty()
}

/// `getJSDocTagNameCompletions`.
fn get_js_doc_tag_name_completions() -> Vec<CompletionItem> {
    clone_items(js_doc_tag_name_completion_items())
}

/// `getJSDocTagCompletions`.
fn get_js_doc_tag_completions() -> Vec<CompletionItem> {
    clone_items(js_doc_tag_completion_items())
}

/// `jsDocTagNames`.
const JS_DOC_TAG_NAMES: &[&str] = &[
    "abstract",
    "access",
    "alias",
    "argument",
    "async",
    "augments",
    "author",
    "borrows",
    "callback",
    "class",
    "classdesc",
    "constant",
    "constructor",
    "constructs",
    "copyright",
    "default",
    "deprecated",
    "description",
    "emits",
    "enum",
    "event",
    "example",
    "exports",
    "extends",
    "external",
    "field",
    "file",
    "fileoverview",
    "fires",
    "function",
    "generator",
    "global",
    "hideconstructor",
    "host",
    "ignore",
    "implements",
    "import",
    "inheritdoc",
    "inner",
    "instance",
    "interface",
    "kind",
    "lends",
    "license",
    "link",
    "linkcode",
    "linkplain",
    "listens",
    "member",
    "memberof",
    "method",
    "mixes",
    "module",
    "name",
    "namespace",
    "overload",
    "override",
    "package",
    "param",
    "private",
    "prop",
    "property",
    "protected",
    "public",
    "readonly",
    "requires",
    "returns",
    "satisfies",
    "see",
    "since",
    "static",
    "summary",
    "template",
    "this",
    "throws",
    "todo",
    "tutorial",
    "type",
    "typedef",
    "var",
    "variation",
    "version",
    "virtual",
    "yields",
];

/// `jsDocTagNameCompletionItems` — memoized like Go's `sync.OnceValue`.
fn js_doc_tag_name_completion_items() -> &'static Vec<LspCompletionItem> {
    static ITEMS: std::sync::OnceLock<Vec<LspCompletionItem>> = std::sync::OnceLock::new();
    ITEMS.get_or_init(|| {
        JS_DOC_TAG_NAMES
            .iter()
            .map(|tag_name| LspCompletionItem {
                label: tag_name.to_string(),
                kind: Some(lsproto::CompletionItemKind::Keyword),
                sort_text: Some(sort_text::LOCATION_PRIORITY.to_string()),
                ..Default::default()
            })
            .collect()
    })
}

/// `jsDocTagCompletionItems` — memoized like Go's `sync.OnceValue`.
fn js_doc_tag_completion_items() -> &'static Vec<LspCompletionItem> {
    static ITEMS: std::sync::OnceLock<Vec<LspCompletionItem>> = std::sync::OnceLock::new();
    ITEMS.get_or_init(|| {
        JS_DOC_TAG_NAMES
            .iter()
            .map(|tag_name| LspCompletionItem {
                label: format!("@{tag_name}"),
                kind: Some(lsproto::CompletionItemKind::Keyword),
                sort_text: Some(sort_text::LOCATION_PRIORITY.to_string()),
                ..Default::default()
            })
            .collect()
    })
}

/// `quotePropertyName`.
fn quote_property_name(
    nodes: &[Node],
    file: NodeId,
    preferences: &UserPreferences,
    name: &str,
) -> String {
    if name.chars().next().is_some_and(|r| r.is_ascii_digit()) {
        return name.to_string();
    }
    crate::utilities::quote(nodes, file, preferences, name)
}

/// `isStringAndEmptyAnonymousObjectIntersection` — checks whether the type is
/// `string & {}`, which is semantically equivalent to `string` but is not
/// reduced by the checker; a special case used for supporting string literal
/// completions for `string` type.
fn is_string_and_empty_anonymous_object_intersection(
    type_checker: &mut Checker,
    t: TypeId,
) -> bool {
    let (is_intersection, constituents) = {
        let t_ref = type_checker.types.get(t);
        (
            t_ref
                .flags()
                .intersects(tsc_checker::types::TypeFlags::INTERSECTION),
            t_ref.types().to_vec(),
        )
    };
    if !is_intersection {
        return false;
    }
    constituents.len() == 2
        && (are_intersected_types_avoiding_string_reduction(
            type_checker,
            constituents[0],
            constituents[1],
        ) || are_intersected_types_avoiding_string_reduction(
            type_checker,
            constituents[1],
            constituents[0],
        ))
}

/// `areIntersectedTypesAvoidingStringReduction`.
fn are_intersected_types_avoiding_string_reduction(
    type_checker: &mut Checker,
    t1: TypeId,
    t2: TypeId,
) -> bool {
    type_checker.types.get(t1).is_string() && type_checker.is_empty_anonymous_object_type(t2)
}

/// `getJSDocParameterCompletions`.
fn get_js_doc_parameter_completions(
    ctx: &Context,
    file: NodeId,
    position: TextPos,
    type_checker: &mut Checker,
    options: &tsc_core::options_generated::CompilerOptions,
    preferences: &UserPreferences,
    tag_name_only: bool,
    program: &Program,
) -> Vec<CompletionItem> {
    let program = program;
    let current_token = {
        let mut nodes = program.nodes_mut(file.file_index());
        tsc_astnav::tokens::get_token_at_position(&mut nodes, file, position)
    };
    let Some(current_token) = current_token else {
        return Vec::new();
    };
    let js_doc = {
        let nodes = program.nodes(file.file_index());
        if !ast::is_js_doc_tag(&nodes[current_token]) && !ast::is_js_doc(&nodes[current_token]) {
            return Vec::new();
        }
        if ast::is_js_doc(&nodes[current_token]) {
            current_token
        } else {
            nodes[current_token].parent.expect("JSDoc tag parent")
        }
    };
    {
        let nodes = program.nodes(file.file_index());
        if !ast::is_js_doc(&nodes[js_doc]) {
            return Vec::new();
        }
    }
    let fun = {
        let nodes = program.nodes(file.file_index());
        nodes[js_doc].parent
    };
    let Some(fun) = fun else {
        return Vec::new();
    };
    {
        let nodes = program.nodes(file.file_index());
        if !ast::is_function_like(Some(fun), &nodes) {
            return Vec::new();
        }
    }

    let is_js = {
        let nodes = program.nodes(file.file_index());
        ast::is_source_file_js(nodes[file].as_source_file())
    };
    // isSnippet := clientSupportsItemSnippet(clientOptions)
    // !!! need snippet printer
    let _ = ctx;
    let is_snippet = false;
    let mut param_tag_count = 0;
    let tags: Vec<NodeId> = {
        let nodes = program.nodes(file.file_index());
        nodes[js_doc]
            .as_js_doc()
            .tags
            .as_ref()
            .map(|tags| tags.nodes.to_vec())
            .unwrap_or_default()
    };
    for tag in &tags {
        let count = {
            let nodes = program.nodes(file.file_index());
            ast::is_js_doc_parameter_tag(&nodes[*tag])
        };
        if count {
            let mut nodes = program.nodes_mut(file.file_index());
            let tag_start = tsc_astnav::tokens::get_start_of_node(
                &mut nodes, file, *tag, false, /*includeJSDoc*/
            );
            if tag_start < position
                && nodes[*tag]
                    .name()
                    .is_some_and(|n| ast::is_identifier(&nodes[n]))
            {
                param_tag_count += 1;
            }
        }
    }
    let mut param_index: i64 = -1;
    let mut emit_context: Option<tsc_printer::EmitContext> = None;
    let params: Vec<NodeId> = {
        let nodes = program.nodes(file.file_index());
        nodes[fun].parameters().unwrap_or(&[]).to_vec()
    };
    params
        .into_iter()
        .filter_map(|param| {
            param_index += 1;
            if param_index < param_tag_count {
                // This parameter is already annotated.
                return None;
            }
            let param_name_node = {
                let nodes = program.nodes(file.file_index());
                nodes[param].name()
            };
            let is_named_param = {
                let nodes = program.nodes(file.file_index());
                param_name_node.is_some_and(|n| ast::is_identifier(&nodes[n]))
            };
            let program = program.clone();
            if is_named_param {
                // Named parameter
                let mut tabstop_counter = 1;
                let (param_name, initializer, dot_dot_dot_token) = {
                    let nodes = program.nodes(file.file_index());
                    (
                        nodes[param_name_node.unwrap()].text(&nodes).to_string(),
                        nodes[param].initializer(),
                        nodes[param].as_parameter_declaration().dot_dot_dot_token,
                    )
                };
                let mut display_text = get_js_doc_param_annotation(
                    &mut emit_context,
                    &param_name,
                    initializer,
                    dot_dot_dot_token,
                    is_js,
                    /*isObject*/ false,
                    /*isSnippet*/ false,
                    type_checker,
                    options,
                    preferences,
                    &mut tabstop_counter,
                    file,
                    &program,
                );
                let mut snippet_text = String::new();
                if is_snippet {
                    snippet_text = get_js_doc_param_annotation(
                        &mut emit_context,
                        &param_name,
                        initializer,
                        dot_dot_dot_token,
                        is_js,
                        /*isObject*/ false,
                        /*isSnippet*/ true,
                        type_checker,
                        options,
                        preferences,
                        &mut tabstop_counter,
                        file,
                        &program,
                    );
                }
                if tag_name_only {
                    // Remove `@`
                    display_text = display_text[1..].to_string();
                    if !snippet_text.is_empty() {
                        snippet_text = snippet_text[1..].to_string();
                    }
                }

                return Some(CompletionItem {
                    item: LspCompletionItem {
                        label: display_text,
                        kind: Some(lsproto::CompletionItemKind::Variable),
                        sort_text: Some(sort_text::LOCATION_PRIORITY.to_string()),
                        insert_text: if snippet_text.is_empty() {
                            None
                        } else {
                            Some(snippet_text)
                        },
                        insert_text_format: if is_snippet {
                            Some(lsproto::InsertTextFormat::Snippet)
                        } else {
                            None
                        },
                        ..Default::default()
                    },
                    symbol: None,
                });
            } else if param_index == param_tag_count {
                // Destructuring parameter; do it positionally
                let param_path = format!("param{param_index}");
                let (name_node, initializer, dot_dot_dot_token) = {
                    let nodes = program.nodes(file.file_index());
                    (
                        nodes[param].name(),
                        nodes[param].initializer(),
                        nodes[param].as_parameter_declaration().dot_dot_dot_token,
                    )
                };
                let display_text_result = generate_jsdoc_param_tags_for_destructuring(
                    &mut emit_context,
                    &param_path,
                    name_node,
                    initializer,
                    dot_dot_dot_token,
                    is_js,
                    /*isSnippet*/ false,
                    type_checker,
                    options,
                    preferences,
                    file,
                    &program,
                );
                let mut snippet_text_result = Vec::new();
                if is_snippet {
                    snippet_text_result = generate_jsdoc_param_tags_for_destructuring(
                        &mut emit_context,
                        &param_path,
                        name_node,
                        initializer,
                        dot_dot_dot_token,
                        is_js,
                        /*isSnippet*/ true,
                        type_checker,
                        options,
                        preferences,
                        file,
                        &program,
                    );
                }
                let new_line = options.new_line.get_new_line_character();
                let mut display_text = format!("{}* ", display_text_result.join(&new_line));
                let mut snippet_text = if snippet_text_result.is_empty() {
                    String::new()
                } else {
                    format!("{}* ", snippet_text_result.join(&new_line))
                };
                if tag_name_only {
                    // Remove `@`
                    display_text = display_text.trim_start_matches('@').to_string();
                    snippet_text = snippet_text.trim_start_matches('@').to_string();
                }
                return Some(CompletionItem {
                    item: LspCompletionItem {
                        label: display_text,
                        kind: Some(lsproto::CompletionItemKind::Variable),
                        sort_text: Some(sort_text::LOCATION_PRIORITY.to_string()),
                        insert_text: if snippet_text.is_empty() {
                            None
                        } else {
                            Some(snippet_text)
                        },
                        insert_text_format: if is_snippet {
                            Some(lsproto::InsertTextFormat::Snippet)
                        } else {
                            None
                        },
                        ..Default::default()
                    },
                    symbol: None,
                });
            }
            None
        })
        .collect()
}

/// `getJSDocParamAnnotation`.
#[allow(clippy::too_many_arguments)]
fn get_js_doc_param_annotation(
    emit_context: &mut Option<tsc_printer::EmitContext>,
    param_name: &str,
    initializer: Option<NodeId>,
    dot_dot_dot_token: Option<NodeId>,
    is_js: bool,
    is_object: bool,
    is_snippet: bool,
    type_checker: &mut Checker,
    options: &tsc_core::options_generated::CompilerOptions,
    preferences: &UserPreferences,
    tabstop_counter: &mut i32,
    file: NodeId,
    program: &Program,
) -> String {
    let _ = options;
    let mut param_name = param_name.to_string();
    if let Some(initializer) = initializer {
        param_name = {
            let nodes = program.nodes(file.file_index());
            get_js_doc_param_name_with_initializer(&param_name, initializer, &nodes)
        };
    }
    if is_snippet {
        param_name = escape_snippet_text(&param_name);
    }
    if is_js {
        let mut t = "*".to_string();
        if is_object {
            debug_assert!(
                dot_dot_dot_token.is_none(),
                "Cannot annotate a rest parameter with type 'object'."
            );
            t = "object".to_string();
        } else {
            if let Some(initializer) = initializer {
                let initializer_parent = {
                    let nodes = program.nodes(file.file_index());
                    nodes[initializer].parent.expect("initializer parent")
                };
                let inferred_type = type_checker.get_type_at_location(initializer_parent);
                let flags = type_checker.types.get(inferred_type).flags();
                if !flags.intersects(
                    tsc_checker::types::TypeFlags::ANY | tsc_checker::types::TypeFlags::VOID,
                ) {
                    let init_file = {
                        let nodes = program.nodes(file.file_index());
                        ast::get_source_file_of_node(Some(initializer), &nodes)
                    };
                    let builder_flags = {
                        let nodes = program.nodes(file.file_index());
                        if let Some(init_file) = init_file {
                            let quote_preference = tsc_lsutil::utilities::get_quote_preference(
                                &nodes,
                                init_file,
                                preferences,
                            );
                            if quote_preference == tsc_lsutil::QuotePreference::SINGLE {
                                tsc_nodebuilder::Flags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE
                            } else {
                                tsc_nodebuilder::Flags::NONE
                            }
                        } else {
                            tsc_nodebuilder::Flags::NONE
                        }
                    };
                    let enclosing = {
                        let nodes = program.nodes(file.file_index());
                        ast::find_ancestor(Some(initializer), &nodes, &mut |n, _| {
                            ast::is_function_like(Some(n.id), &nodes)
                        })
                    };
                    let type_node = type_checker.type_to_type_node(
                        inferred_type,
                        enclosing,
                        builder_flags,
                        Default::default(), /*idToSymbol*/
                    );
                    if let Some(type_node) = type_node {
                        let emit_ctx =
                            emit_context.get_or_insert_with(tsc_printer::EmitContext::new);
                        // !!! snippet p
                        emit_ctx.set_emit_flags(type_node, tsc_printer::EmitFlags::SINGLE_LINE);
                        let mut nodes = program.nodes_mut(file.file_index());
                        let symbols = program.symbols.clone();
                        let mut p = tsc_printer::Printer::new(
                            tsc_printer::PrinterOptions {
                                remove_comments: true,
                                // !!!
                                // Module: options.Module,
                                // ModuleResolution: options.ModuleResolution,
                                // Target: options.Target,
                                ..Default::default()
                            },
                            tsc_printer::PrintHandlers::default(),
                            emit_ctx,
                            &mut nodes,
                            &symbols,
                        );
                        t = p.emit(Some(type_node), Some(file));
                    }
                }
            }
            if is_snippet && t == "*" {
                let tabstop = *tabstop_counter;
                *tabstop_counter += 1;
                t = format!("${{{tabstop}:{t}}}");
            }
        }
        let dot_dot_dot = if !is_object && dot_dot_dot_token.is_some() {
            "..."
        } else {
            ""
        };
        let mut description = String::new();
        if is_snippet {
            let tabstop = *tabstop_counter;
            *tabstop_counter += 1;
            description = format!("${{{tabstop}}}");
        }
        format!("@param {{{dot_dot_dot}{t}}} {param_name} {description}")
    } else {
        let mut description = String::new();
        if is_snippet {
            let tabstop = *tabstop_counter;
            *tabstop_counter += 1;
            description = format!("${{{tabstop}}}");
        }
        format!("@param {param_name} {description}")
    }
}

/// `getJSDocParamNameWithInitializer`.
fn get_js_doc_param_name_with_initializer(
    param_name: &str,
    initializer: NodeId,
    nodes: &[Node],
) -> String {
    let initializer_text = tsc_scanner::utilities::get_text_of_node(initializer, nodes)
        .trim()
        .to_string();
    if initializer_text.contains('\n') || initializer_text.len() > 80 {
        return format!("[{param_name}]");
    }
    format!("[{param_name}={initializer_text}]")
}

/// `generateJSDocParamTagsForDestructuring` — `pattern` is a
/// `*ast.BindingPatternNode`.
#[allow(clippy::too_many_arguments)]
fn generate_jsdoc_param_tags_for_destructuring(
    emit_context: &mut Option<tsc_printer::EmitContext>,
    path: &str,
    pattern: Option<NodeId>,
    initializer: Option<NodeId>,
    dot_dot_dot_token: Option<NodeId>,
    is_js: bool,
    is_snippet: bool,
    type_checker: &mut Checker,
    options: &tsc_core::options_generated::CompilerOptions,
    preferences: &UserPreferences,
    file: NodeId,
    program: &Program,
) -> Vec<String> {
    let mut tabstop_counter = 1;
    if !is_js {
        return vec![get_js_doc_param_annotation(
            emit_context,
            path,
            initializer,
            dot_dot_dot_token,
            is_js,
            /*isObject*/ false,
            is_snippet,
            type_checker,
            options,
            preferences,
            &mut tabstop_counter,
            file,
            program,
        )];
    }
    js_doc_param_pattern_worker(
        emit_context,
        path,
        pattern,
        initializer,
        dot_dot_dot_token,
        is_js,
        is_snippet,
        type_checker,
        options,
        preferences,
        &mut tabstop_counter,
        file,
        program,
    )
}

/// `jsDocParamPatternWorker`.
#[allow(clippy::too_many_arguments)]
fn js_doc_param_pattern_worker(
    emit_context: &mut Option<tsc_printer::EmitContext>,
    path: &str,
    pattern: Option<NodeId>,
    initializer: Option<NodeId>,
    dot_dot_dot_token: Option<NodeId>,
    is_js: bool,
    is_snippet: bool,
    type_checker: &mut Checker,
    options: &tsc_core::options_generated::CompilerOptions,
    preferences: &UserPreferences,
    counter: &mut i32,
    file: NodeId,
    program: &Program,
) -> Vec<String> {
    let is_object_binding_pattern = pattern.is_some_and(|pattern| {
        let nodes = program.nodes(file.file_index());
        ast::is_object_binding_pattern(&nodes[pattern])
    });
    if is_object_binding_pattern && dot_dot_dot_token.is_none() {
        let mut child_counter = *counter;
        let root_param = get_js_doc_param_annotation(
            emit_context,
            path,
            initializer,
            dot_dot_dot_token,
            is_js,
            /*isObject*/ true,
            is_snippet,
            type_checker,
            options,
            preferences,
            &mut child_counter,
            file,
            program,
        );
        let mut child_tags: Vec<String> = Vec::new();
        let elements: Vec<NodeId> = {
            let nodes = program.nodes(file.file_index());
            nodes[pattern.unwrap()].elements().unwrap_or(&[]).to_vec()
        };
        let mut all_valid = true;
        for element in &elements {
            let element_tags = js_doc_param_element_worker(
                emit_context,
                path,
                *element,
                initializer,
                dot_dot_dot_token,
                is_js,
                is_snippet,
                type_checker,
                options,
                preferences,
                &mut child_counter,
                file,
                program,
            );
            if element_tags.is_empty() {
                all_valid = false;
                break;
            }
            child_tags.extend(element_tags);
        }
        if !all_valid {
            child_tags = Vec::new();
        }
        if !child_tags.is_empty() {
            *counter = child_counter;
            let mut result = vec![root_param];
            result.extend(child_tags);
            return result;
        }
    }
    vec![get_js_doc_param_annotation(
        emit_context,
        path,
        initializer,
        dot_dot_dot_token,
        is_js,
        /*isObject*/ false,
        is_snippet,
        type_checker,
        options,
        preferences,
        counter,
        file,
        program,
    )]
}

/// `jsDocParamElementWorker` — assumes the binding element is inside an object
/// binding pattern; we can't deeply annotate an array binding pattern.
#[allow(clippy::too_many_arguments)]
fn js_doc_param_element_worker(
    emit_context: &mut Option<tsc_printer::EmitContext>,
    path: &str,
    element: NodeId,
    initializer: Option<NodeId>,
    dot_dot_dot_token: Option<NodeId>,
    is_js: bool,
    is_snippet: bool,
    type_checker: &mut Checker,
    options: &tsc_core::options_generated::CompilerOptions,
    preferences: &UserPreferences,
    counter: &mut i32,
    file: NodeId,
    program: &Program,
) -> Vec<String> {
    let (name, property_name, element_initializer, element_dot_dot_dot) = {
        let nodes = program.nodes(file.file_index());
        (
            nodes[element].name(),
            nodes[element].property_name(),
            nodes[element].initializer(),
            nodes[element].as_binding_element().dot_dot_dot_token,
        )
    };
    let Some(name) = name else {
        return Vec::new();
    };
    let name_is_identifier = {
        let nodes = program.nodes(file.file_index());
        ast::is_identifier(&nodes[name])
    };
    if name_is_identifier {
        // `{ b }` or `{ b: newB }`
        let property_name = {
            let nodes = program.nodes(file.file_index());
            match property_name {
                Some(property_name) => ast::try_get_text_of_property_name(property_name, &nodes).0,
                None => Some(nodes[name].text(&nodes).to_string()),
            }
        };
        let Some(property_name) = property_name.filter(|p| !p.is_empty()) else {
            return Vec::new();
        };
        let param_name = format!("{path}.{property_name}");
        return vec![get_js_doc_param_annotation(
            emit_context,
            &param_name,
            element_initializer,
            element_dot_dot_dot,
            is_js,
            /*isObject*/ false,
            is_snippet,
            type_checker,
            options,
            preferences,
            counter,
            file,
            program,
        )];
    } else if let Some(property_name) = property_name {
        // `{ b: {...} }` or `{ b: [...] }`
        let property_name = {
            let nodes = program.nodes(file.file_index());
            ast::try_get_text_of_property_name(property_name, &nodes).0
        };
        let Some(property_name) = property_name.filter(|p| !p.is_empty()) else {
            return Vec::new();
        };
        return js_doc_param_pattern_worker(
            emit_context,
            &format!("{path}.{property_name}"),
            Some(name),
            element_initializer,
            element_dot_dot_dot,
            is_js,
            is_snippet,
            type_checker,
            options,
            preferences,
            counter,
            file,
            program,
        );
    }
    Vec::new()
}

/// `getJSDocParameterNameCompletions` — `tag` is a
/// `*ast.JSDocParameterOrPropertyTag`.
fn get_js_doc_parameter_name_completions(nodes: &[Node], tag: NodeId) -> Vec<CompletionItem> {
    let Some(name_node) = nodes[tag].name() else {
        return Vec::new();
    };
    if !ast::is_identifier(&nodes[name_node]) {
        return Vec::new();
    }
    let name_thus_far = nodes[name_node].text(&nodes).to_string();
    let js_doc = nodes[tag].parent.expect("tag parent");
    let fun = nodes[js_doc].parent;
    let Some(fun) = fun else {
        return Vec::new();
    };
    if !ast::is_function_like(Some(fun), nodes) {
        return Vec::new();
    }

    let tags: Vec<NodeId> = nodes[js_doc]
        .as_js_doc()
        .tags
        .as_ref()
        .map(|tags| tags.nodes.to_vec())
        .unwrap_or_default();

    nodes[fun]
        .parameters()
        .unwrap_or(&[])
        .iter()
        .filter_map(|&param| {
            let param_name_node = nodes[param].name()?;
            if !ast::is_identifier(&nodes[param_name_node]) {
                return None;
            }
            let name = nodes[param_name_node].text(&nodes).to_string();
            if tags.iter().any(|&t| {
                t != tag
                    && ast::is_js_doc_parameter_tag(&nodes[t])
                    && nodes[t].name().is_some_and(|n| {
                        ast::is_identifier(&nodes[n]) && nodes[n].text(&nodes).as_ref() == name
                    })
            }) || (!name_thus_far.is_empty() && !name.starts_with(&name_thus_far))
            {
                return None;
            }
            Some(CompletionItem {
                item: LspCompletionItem {
                    label: name,
                    kind: Some(lsproto::CompletionItemKind::Variable),
                    sort_text: Some(sort_text::LOCATION_PRIORITY.to_string()),
                    ..Default::default()
                },
                symbol: None,
            })
        })
        .collect()
}

impl LanguageService<'_> {
    /// `getReplacementRangeForContextToken`.
    pub(crate) fn get_replacement_range_for_context_token(
        &self,
        file: NodeId,
        context_token: Option<NodeId>,
        position: TextPos,
    ) -> Option<lsproto::Range> {
        let context_token = context_token?;

        // !!! ensure range is single line
        let kind = {
            let program = self.get_program();
            let nodes = program.nodes(file.file_index());
            nodes[context_token].kind
        };
        match kind {
            Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral => {
                self.create_range_from_string_literal_like_content(file, context_token, position)
            }
            _ => {
                let (lsp_range, fidelity) = self.create_lsp_range_from_node(context_token, file);
                if !fidelity.is_exact() {
                    return None;
                }
                Some(lsp_range)
            }
        }
    }

    /// `createRangeFromStringLiteralLikeContent` — `node` is
    /// `*ast.StringLiteralLike`.
    pub(crate) fn create_range_from_string_literal_like_content(
        &self,
        file: NodeId,
        node: NodeId,
        position: TextPos,
    ) -> Option<lsproto::Range> {
        let program = self.get_program();
        let (mut replacement_end, node_start, node_end) = {
            let mut nodes = program.nodes_mut(file.file_index());
            (
                nodes[node].end() - 1,
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes, file, node, false, /*includeJSDoc*/
                ),
                nodes[node].end(),
            )
        };
        if {
            let nodes = program.nodes(file.file_index());
            ast::is_unterminated_literal(&nodes[node])
        } {
            // we return no replacement range only if unterminated string is empty
            if node_start == replacement_end {
                return None;
            }
            replacement_end = position.min(node_end);
        }
        let (lsp_range, fidelity) =
            self.create_lsp_range_from_bounds(node_start + 1, replacement_end, file);
        if !fidelity.is_exact() {
            return None;
        }
        Some(lsp_range)
    }
}

/// `type memberCompletionEntry struct`.
#[derive(Default)]
pub(crate) struct MemberCompletionEntry {
    /// `insertText`.
    pub(crate) insert_text: String,
    /// `filterText`.
    pub(crate) filter_text: String,
    /// `isSnippet`.
    pub(crate) is_snippet: bool,
    /// `additionalTextEdits`.
    pub(crate) additional_text_edits: Vec<lsproto::TextEdit>,
}

/// `type objectLiteralMethodSymbol struct`.
pub(crate) struct ObjectLiteralMethodSymbol {
    /// `symbol`.
    pub(crate) symbol: SymbolId,
    /// `origin`.
    pub(crate) origin: SymbolOriginInfo,
}

/// `isObjectLiteralMethodSymbol`.
fn is_object_literal_method_symbol(
    symbols: &tsc_ast::SymbolArena,
    symbol: SymbolId,
) -> bool {
    symbols.get_ref(symbol)
        .flags
        .intersects(SymbolFlags::PROPERTY | SymbolFlags::METHOD)
}

/// `getInsertTextAndReplacementSpanForImportCompletion`.
#[allow(clippy::too_many_arguments)]
fn get_insert_text_and_replacement_span_for_import_completion(
    fix: &crate::autoimport::Fix,
    import_kind: lsproto::ImportKind,
    import_statement_completion: &ImportStatementCompletionInfo,
    use_semicolons: bool,
    file: NodeId,
    preferences: &UserPreferences,
    is_snippet: bool,
    program: &Program,
) -> (String, Option<lsproto::Range>) {
    let quoted_module_specifier = escape_snippet_text(&crate::utilities::quote(
        &program.nodes(file.file_index()),
        file,
        preferences,
        &fix.auto_import_fix.module_specifier,
    ));
    let tab_stop = if is_snippet { "$1" } else { "" };
    let suffix = if use_semicolons { ";" } else { "" };
    let top_level_type_only_text = if import_statement_completion.is_top_level_type_only {
        " type "
    } else {
        " "
    };
    let name = escape_snippet_text(&fix.auto_import_fix.name);
    let replacement_span = import_statement_completion.replacement_span.clone();

    let insert_text = match import_kind {
        lsproto::ImportKind::CommonJS => format!(
            "import{top_level_type_only_text}{name}{tab_stop} = require({quoted_module_specifier}){suffix}"
        ),
        lsproto::ImportKind::Default => format!(
            "import{top_level_type_only_text}{name}{tab_stop} from {quoted_module_specifier}{suffix}"
        ),
        lsproto::ImportKind::Namespace => format!(
            "import{top_level_type_only_text}* as {name} from {quoted_module_specifier}{suffix}"
        ),
        lsproto::ImportKind::Named => format!(
            "import{top_level_type_only_text}{{ {}{}{} }} from {}{}",
            if import_statement_completion.could_be_type_only_import_specifier {
                "type "
            } else {
                ""
            },
            name,
            tab_stop,
            quoted_module_specifier,
            suffix
        ),
        _ => panic!("unhandled import kind: {import_kind}"),
    };
    (insert_text, replacement_span)
}

impl LanguageService<'_> {
    /// `getEntryForMemberCompletion`.
    ///
    /// PORT(deferred): needs `autoimport::ImportAdder` + `MissingMemberFixer`
    /// + `change.Tracker` (sibling-owned). Returns `Ok(None)` for now, which
    /// matches Go's `nil` entry path (the symbol is skipped).
    #[allow(clippy::too_many_arguments)]
    fn get_entry_for_member_completion(
        &self,
        _ctx: &Context,
        _type_checker: &mut Checker,
        _symbol: SymbolId,
        _name: &str,
        _location: Option<NodeId>,
        _position: TextPos,
        _context_token: Option<NodeId>,
        _file: NodeId,
    ) -> Result<Option<MemberCompletionEntry>, Error> {
        Ok(None)
    }

    /// `getExhaustiveCaseSnippets`.
    ///
    /// PORT(deferred): needs `autoimport::ImportAdder`,
    /// `TypeToAutoImportableTypeNode` and `snippetPrinter` (sibling-owned).
    fn get_exhaustive_case_snippets(
        &self,
        _ctx: &Context,
        _case_block: NodeId,
        _file: NodeId,
        _position: TextPos,
        _options: &CompilerOptions,
        _program: &Program,
        _type_checker: &mut Checker,
    ) -> Result<Option<LspCompletionItem>, Error> {
        Ok(None)
    }

    /// `getEntryForObjectLiteralMethodCompletion`.
    ///
    /// PORT(deferred): needs `snippetPrinter` (sibling-owned printer harness).
    fn get_entry_for_object_literal_method_completion(
        &self,
        _ctx: &Context,
        _type_checker: &mut Checker,
        _symbol: SymbolId,
        _enclosing_declaration: Option<NodeId>,
        _file: NodeId,
    ) -> Option<SymbolOriginInfoObjectLiteralMethod> {
        None
    }

    /// `completionInfoFromData`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn completion_info_from_data(
        &self,
        ctx: &Context,
        type_checker: &mut Checker,
        file: NodeId,
        compiler_options: &CompilerOptions,
        data: &mut CompletionDataData,
        position: TextPos,
        optional_replacement_span: Option<lsproto::Range>,
        include_symbols: bool,
    ) -> Result<Option<CompletionList>, Error> {
        let program = self.get_program();
        let keyword_filters = data.keyword_filters;
        let is_new_identifier_location = data.is_new_identifier_location;
        let context_token = data.context_token;
        let mut literals = std::mem::take(&mut data.literals);

        // Verify if the file is JSX language variant
        if {
            let nodes = program.nodes(file.file_index());
            nodes[file].as_source_file().language_variant
                == tsc_core::languagevariant::LanguageVariant::Jsx
        } && let Some(list) =
            self.get_jsx_closing_tag_completion(ctx, data.location, file, position)
        {
            return Ok(Some(list));
        }

        // When the completion is for the expression of a case clause (e.g. `case |`),
        // filter literals & enum symbols whose values are already present in existing case clauses.
        let case_clause = {
            let nodes = program.nodes(file.file_index());
            ast::find_ancestor(context_token, &nodes, &mut |n, _| ast::is_case_clause(n))
        };
        if let Some(case_clause) = case_clause {
            let (ct_is_case_keyword, is_descendant_of_expression, clauses) = {
                let nodes = program.nodes(file.file_index());
                (
                    context_token.is_some_and(|ct| nodes[ct].kind == Kind::CaseKeyword),
                    context_token.is_some_and(|ct| {
                        ast::is_node_descendant_of(
                            Some(ct),
                            nodes[case_clause].expression(),
                            &nodes,
                        )
                    }),
                    nodes[nodes[case_clause].parent.expect("case block")]
                        .as_case_block()
                        .clauses
                        .as_ref()
                        .map(|c| c.nodes.to_vec())
                        .unwrap_or_default(),
                )
            };
            if ct_is_case_keyword || is_descendant_of_expression {
                let tracker = crate::utilities::new_case_clause_tracker(type_checker, &clauses);
                literals.retain(|literal| {
                    let value = match literal {
                        LiteralValue::Str(s) => crate::utilities::TrackerHasValue::Str(s.clone()),
                        LiteralValue::Number(n) => crate::utilities::TrackerHasValue::Number(*n),
                        LiteralValue::PseudoBigInt(b) => {
                            crate::utilities::TrackerHasValue::PseudoBigInt(b.clone())
                        }
                    };
                    !tracker.has_value(value)
                });
                data.symbols.retain(|&symbol| {
                    let value_declaration =
                        program.symbols.get_ref(symbol).value_declaration;
                    let is_enum_member = value_declaration.is_some_and(|vd| {
                        let nodes = program.nodes(vd.file_index());
                        ast::is_enum_member(&nodes[vd])
                    });
                    if is_enum_member {
                        if let Some(value) = type_checker
                            .get_constant_value(value_declaration.expect("valueDeclaration"))
                        {
                            let has_value = match value {
                                tsc_evaluator::Value::String(s) => {
                                    tracker.has_value(crate::utilities::TrackerHasValue::Str(s))
                                }
                                tsc_evaluator::Value::Number(n) => {
                                    tracker.has_value(crate::utilities::TrackerHasValue::Number(n))
                                }
                                tsc_evaluator::Value::PseudoBigInt(b) => tracker
                                    .has_value(crate::utilities::TrackerHasValue::PseudoBigInt(b)),
                                tsc_evaluator::Value::Bool(_) => false,
                            };
                            if has_value {
                                return false;
                            }
                        }
                    }
                    true
                });
            }
        }

        let is_checked = is_checked_file(&program.nodes(file.file_index()), file, compiler_options);
        if is_checked
            && !is_new_identifier_location
            && data.symbols.is_empty()
            && keyword_filters == KeywordCompletionFilters::NONE
        {
            return Ok(None);
        }

        let (mut unique_names, mut sorted_entries) = self.get_completion_entries_from_symbols(
            ctx,
            type_checker,
            data,
            None, /*replacementToken*/
            position,
            file,
            compiler_options,
            include_symbols,
        )?;

        if data.keyword_filters != KeywordCompletionFilters::NONE {
            let is_js = {
                let nodes = program.nodes(file.file_index());
                ast::is_source_file_js(nodes[file].as_source_file())
            };
            let keyword_completions = get_keyword_completions(
                data.keyword_filters,
                !data.inside_jsdoc_tag_type_expression && is_js,
            );
            for keyword_entry in keyword_completions {
                let label_kind = tsc_scanner::scanner::string_to_token(&keyword_entry.item.label);
                if (data.is_type_only_location && crate::utilities::is_type_keyword(label_kind))
                    || (!data.is_type_only_location
                        && is_contextual_keyword_in_auto_importable_expression_space(
                            &keyword_entry.item.label,
                        ))
                    || !unique_names.has(&keyword_entry.item.label)
                {
                    unique_names.add(keyword_entry.item.label.clone());
                    sorted_entries.push(keyword_entry);
                }
            }
        }

        for keyword_entry in get_contextual_keywords(
            &program.nodes(file.file_index()),
            file,
            context_token,
            position,
        ) {
            if !unique_names.has(&keyword_entry.label) {
                unique_names.add(keyword_entry.label.clone());
                sorted_entries.push(CompletionItem {
                    item: keyword_entry,
                    symbol: None,
                });
            }
        }

        for literal in &literals {
            let literal_entry = create_completion_item_for_literal(
                &program.nodes(file.file_index()),
                file,
                self.user_preferences(),
                literal,
            );
            unique_names.add(literal_entry.label.clone());
            sorted_entries.push(CompletionItem {
                item: literal_entry,
                symbol: None,
            });
        }

        if !is_checked {
            self.get_js_completion_entries(
                ctx,
                file,
                position,
                &mut unique_names,
                &mut sorted_entries,
            );
        }

        if context_token.is_some()
            && !data.is_right_of_open_tag
            && !data.is_right_of_dot_or_question_dot
        {
            let case_block = {
                let nodes = program.nodes(file.file_index());
                ast::find_ancestor_kind(context_token, Kind::CaseBlock, &nodes)
            };
            if let Some(case_block) = case_block {
                if let Some(cases_item) = self.get_exhaustive_case_snippets(
                    ctx,
                    case_block,
                    file,
                    position,
                    compiler_options,
                    &program,
                    type_checker,
                )? {
                    sorted_entries.push(CompletionItem {
                        item: cases_item,
                        symbol: None,
                    });
                }
            }
        }

        let item_defaults = self.set_item_defaults(
            ctx,
            position,
            file,
            &mut sorted_entries,
            Some(&data.default_commit_characters),
            optional_replacement_span.as_ref(),
        );

        Ok(Some(CompletionList {
            is_incomplete: data.has_unresolved_auto_imports,
            item_defaults,
            items: sorted_entries.into_iter().map(Some).collect(),
            ..Default::default()
        }))
    }
}

impl LanguageService<'_> {
    /// `getCompletionEntriesFromSymbols`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn get_completion_entries_from_symbols(
        &self,
        ctx: &Context,
        type_checker: &mut Checker,
        data: &CompletionDataData,
        replacement_token: Option<NodeId>,
        position: TextPos,
        file: NodeId,
        compiler_options: &CompilerOptions,
        include_symbols: bool,
    ) -> Result<(Set<String>, Vec<CompletionItem>), Error> {
        let program = self.get_program();
        let closest_symbol_declaration = get_closest_symbol_declaration(
            &program.nodes(file.file_index()),
            data.context_token,
            data.location,
        );
        let use_semicolons = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_lsutil::probably_uses_semicolons(&mut nodes, file)
        };
        let preferences = self.user_preferences();
        let is_member_completion = is_member_completion_kind(data.completion_kind);
        let mut sorted_entries: Vec<CompletionItem> =
            Vec::with_capacity(data.symbols.len() + data.auto_imports.len());
        // Tracks unique names.
        // Value is set to false for global variables or completions from external module exports, because we can have multiple of those;
        // true otherwise. Based on the order we add things we will always see locals first, then globals, then module exports.
        // So adding a completion for a local will prevent us from adding completions for external module exports sharing the same name.
        let mut uniques: UniqueNamesMap = UniqueNamesMap::new();
        for (index, &symbol) in data.symbols.iter().enumerate() {
            let origin = data.symbol_to_origin_info_map.get(&(index as i32));
            let (name, needs_convert_property_access) = {
                let mut nodes = program.nodes_mut(file.file_index());
                get_completion_entry_display_name_for_symbol(
                    &mut nodes,
                    file,
                    preferences,
                    symbol,
                    origin,
                    data.completion_kind,
                    data.is_jsx_identifier_expected,
                    type_checker,
                    &program,
                )
            };
            if name.is_empty()
                || (uniques.get(&name) == Some(&true)
                    && !(origin.is_some_and(|o| origin_is_object_literal_method(Some(o)))))
                || (data.completion_kind == CompletionKind::Global
                    && !should_include_symbol(
                        &program,
                        symbol,
                        data,
                        closest_symbol_declaration,
                        file,
                        type_checker,
                    ))
            {
                continue;
            }

            // When in a value location in a JS file, ignore symbols that definitely seem to be type-only.
            let is_source_file_js = {
                let nodes = program.nodes(file.file_index());
                ast::is_source_file_js(nodes[file].as_source_file())
            };
            if !data.is_type_only_location
                && is_source_file_js
                && symbol_appears_to_be_type_only(&program, symbol, type_checker)
            {
                continue;
            }

            let original_sort_text = data
                .symbol_to_sort_text_map
                .get(&symbol)
                .cloned()
                .unwrap_or_else(|| sort_text::LOCATION_PRIORITY.to_string());

            let sort_text = if is_deprecated(symbol, type_checker, &program) {
                deprecate_sort_text(&original_sort_text)
            } else {
                original_sort_text
            };
            let entry = self.create_completion_item(
                ctx,
                type_checker,
                symbol,
                &sort_text,
                replacement_token,
                data,
                position,
                file,
                name.clone(),
                needs_convert_property_access,
                origin,
                use_semicolons,
                compiler_options,
                is_member_completion,
            )?;
            let Some(entry) = entry else {
                continue;
            };

            // True for locals; false for globals, module exports from other files, `this.` completions.
            let should_shadow_later_symbols = (origin.is_none()
                || origin.is_some_and(|o| origin_is_type_only_alias(Some(o))))
                && !{
                    let symbols = program.symbols.clone();
                    let s = &symbols[symbol.index()];
                    s.parent.is_none()
                        && !tsc_core::core::some(&s.declarations, |d| {
                            tsc_ast::get_source_file_of_node(Some(*d), &program.arena_of(*d))
                                == Some(file)
                        })
                };
            uniques.insert(name, should_shadow_later_symbols);
            let sym = if include_symbols { Some(symbol) } else { None };
            sorted_entries.push(CompletionItem {
                item: entry,
                symbol: sym,
            });
        }

        for auto_import in &data.auto_imports {
            // !!! check for type-only in JS
            // !!! deprecation

            let mut replacement_span: Option<lsproto::Range> = None;
            let mut insert_text = String::new();
            let mut filter_text = String::new();
            let mut is_snippet = false;
            let mut sort_text = sort_text::AUTO_IMPORT_SUGGESTIONS.to_string();

            if let Some(import_statement_completion) = &data.import_statement_completion {
                is_snippet = client_supports_item_snippet(ctx);
                let (text, span) = get_insert_text_and_replacement_span_for_import_completion(
                    &auto_import.fix,
                    crate::autoimport::fix::get_import_kind_for_import_statement(
                        file,
                        &auto_import.export,
                        &program,
                    ),
                    import_statement_completion,
                    use_semicolons,
                    file,
                    preferences,
                    is_snippet,
                    &program,
                );
                insert_text = text;
                replacement_span = span;
                // The edit range covers the whole import statement typed so far, and clients match that text against the
                // filter text, so it has to be the statement being inserted (as in Strada), not just the bare name.
                filter_text = insert_text.clone();
                sort_text = sort_text::LOCATION_PRIORITY.to_string();
            }

            // Non-contextual keywords (e.g., `function`, `class`, `const`) cannot be used as identifiers,
            // so auto-imports with these names should not shadow keyword completions.
            if {
                let token =
                    tsc_scanner::scanner::string_to_token(&auto_import.fix.auto_import_fix.name);
                token != Kind::Unknown && ast::is_non_contextual_keyword(token)
            } {
                continue;
            }

            if !auto_import.export.is_unresolved_alias() {
                if data.is_type_only_location {
                    if !auto_import.export.flags.intersects(SymbolFlags::TYPE)
                        && !auto_import.export.flags.intersects(SymbolFlags::MODULE)
                    {
                        continue;
                    }
                } else if data.import_statement_completion.is_none()
                    && !auto_import.export.flags.intersects(SymbolFlags::VALUE)
                {
                    continue;
                }
            }

            let mut entry = self.create_lsp_completion_item(
                ctx,
                auto_import.fix.auto_import_fix.name.clone(),
                &insert_text,
                &filter_text,
                sort_text,
                auto_import.export.script_element_kind,
                auto_import.export.script_element_kind_modifiers,
                replacement_span.as_ref(),
                None, /*commitCharacters*/
                Some(lsproto::CompletionItemLabelDetails {
                    description: Some(auto_import.fix.auto_import_fix.module_specifier.clone()),
                    detail: None,
                }),
                file,
                position,
                false, /*isMemberCompletion*/
                is_snippet,
                data.import_statement_completion.is_none(), /*hasAction*/
                false,                                      /*preselect*/
                &auto_import.fix.auto_import_fix.module_specifier,
                Some(auto_import.fix.auto_import_fix.clone()),
                None, /*additionalTextEdits*/
                None, /*detail*/
            );

            if let Some(entry_data) = entry.data.as_mut() {
                entry_data.is_import_statement_completion =
                    data.import_statement_completion.is_some();
            }

            if uniques.get(&auto_import.fix.auto_import_fix.name) != Some(&true) {
                uniques.insert(auto_import.fix.auto_import_fix.name.clone(), false);
                sorted_entries.push(CompletionItem {
                    item: entry,
                    symbol: None,
                });
            }
        }

        let mut unique_set: Set<String> = Set::default();
        for name in uniques.keys() {
            unique_set.add(name.clone());
        }
        Ok((unique_set, sorted_entries))
    }

    /// `createCompletionItem`.
    #[allow(clippy::too_many_arguments)]
    fn create_completion_item(
        &self,
        ctx: &Context,
        type_checker: &mut Checker,
        symbol: SymbolId,
        sort_text: &str,
        replacement_token: Option<NodeId>,
        data: &CompletionDataData,
        position: TextPos,
        file: NodeId,
        mut name: String,
        needs_convert_property_access: bool,
        origin: Option<&SymbolOriginInfo>,
        use_semicolons: bool,
        compiler_options: &CompilerOptions,
        is_member_completion: bool,
    ) -> Result<Option<LspCompletionItem>, Error> {
        let program = self.get_program();
        let context_token = data.context_token;
        let mut insert_text = String::new();
        let mut filter_text = String::new();
        let mut replacement_span =
            self.get_replacement_range_for_context_token(file, replacement_token, position);
        let mut is_snippet = false;
        let mut has_action = false;
        let mut source: String = get_source_from_origin(origin).to_string();
        let mut label_details: Option<lsproto::CompletionItemLabelDetails> = None;
        let preferences = self.user_preferences();
        let insert_question_dot = origin_is_nullable_member(origin);
        let mut use_braces = origin_is_symbol_member(origin) || needs_convert_property_access;
        if origin_is_this_type_node(origin) {
            if needs_convert_property_access {
                insert_text = format!(
                    "this{}[{}]",
                    if insert_question_dot { "?." } else { "" },
                    quote_property_name(
                        &program.nodes(file.file_index()),
                        file,
                        preferences,
                        &name,
                    ),
                );
            } else {
                insert_text = format!(
                    "this{}{}",
                    if insert_question_dot { "?." } else { "." },
                    name,
                );
            }
        } else if data.property_access_to_convert.is_some() && (use_braces || insert_question_dot) {
            let property_access_to_convert = data.property_access_to_convert.unwrap();
            // We should only have needsConvertPropertyAccess if there's a property access to convert. But see microsoft/TypeScript#21790.
            // Somehow there was a global with a non-identifier name. Hopefully someone will complain about getting a "foo bar" global completion and provide a repro.
            if use_braces {
                if needs_convert_property_access {
                    insert_text = format!(
                        "[{}]",
                        quote_property_name(
                            &program.nodes(file.file_index()),
                            file,
                            preferences,
                            &name,
                        )
                    );
                } else {
                    insert_text = format!("[{name}]");
                }
            } else {
                insert_text = name.clone();
            }

            let has_question_dot_token = {
                let nodes = program.nodes(file.file_index());
                nodes[property_access_to_convert]
                    .as_property_access_expression()
                    .question_dot_token
                    .is_some()
            };
            if insert_question_dot || has_question_dot_token {
                insert_text = format!("?.{insert_text}");
            }

            let dot = {
                let nodes = program.nodes(file.file_index());
                tsc_astnav::tokens::find_child_of_kind(
                    &mut program.nodes_mut(file.file_index()),
                    file,
                    property_access_to_convert,
                    Kind::DotToken,
                )
                .or_else(|| {
                    tsc_astnav::tokens::find_child_of_kind(
                        &mut program.nodes_mut(file.file_index()),
                        file,
                        property_access_to_convert,
                        Kind::QuestionDotToken,
                    )
                })
            };
            let Some(dot) = dot else {
                return Ok(None);
            };

            // If the text after the '.' starts with this name, write over it. Else, add new text.
            let end = {
                let nodes = program.nodes(file.file_index());
                let property_access_name_text = nodes[property_access_to_convert]
                    .name()
                    .map(|n| nodes[n].text(&nodes).to_string())
                    .unwrap_or_default();
                if name.starts_with(&property_access_name_text) {
                    nodes[property_access_to_convert].end()
                } else {
                    nodes[dot].end()
                }
            };
            let dot_start = {
                let mut nodes = program.nodes_mut(file.file_index());
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes, file, dot, false, /*includeJSDoc*/
                )
            };
            let (lsp_range, fidelity) = self.create_lsp_range_from_bounds(dot_start, end, file);
            if !fidelity.is_exact() {
                return Ok(None);
            }
            replacement_span = Some(lsp_range);
        }

        if data.jsx_initializer.is_initializer {
            if insert_text.is_empty() {
                insert_text = name.clone();
            }
            insert_text = format!("{{{insert_text}}}");
            if let Some(initializer) = data.jsx_initializer.initializer {
                let (lsp_range, fidelity) = self.create_lsp_range_from_node(initializer, file);
                if !fidelity.is_exact() {
                    return Ok(None);
                }
                replacement_span = Some(lsp_range);
            }
        }

        if origin_is_promise(origin) && data.property_access_to_convert.is_some() {
            let property_access_to_convert = data.property_access_to_convert.unwrap();
            if insert_text.is_empty() {
                insert_text = name.clone();
            }
            let preceding_token = {
                let mut nodes = program.nodes_mut(file.file_index());
                let pos = nodes[property_access_to_convert].pos();
                tsc_astnav::tokens::find_preceding_token(&mut nodes, file, pos)
            };
            let mut await_text = String::new();
            if preceding_token.is_some_and(|pt| {
                let mut nodes = program.nodes_mut(file.file_index());
                let pt_end = nodes[pt].end();
                let pt_parent = nodes[pt].parent.expect("preceding token parent");
                tsc_lsutil::position_is_asi_candidate(&mut nodes, pt_end, pt_parent, file)
            }) {
                await_text = ";".to_string();
            }

            let expression_text = {
                let nodes = program.nodes(file.file_index());
                let expression = nodes[property_access_to_convert]
                    .expression()
                    .expect("property access expression");
                tsc_scanner::utilities::get_text_of_node(expression, &nodes)
            };
            await_text = format!("{await_text}(await {expression_text})");
            if needs_convert_property_access {
                insert_text = format!("{await_text}{insert_text}");
            } else {
                insert_text = format!(
                    "{await_text}{}{}",
                    if insert_question_dot { "?." } else { "." },
                    insert_text,
                );
            }
            let (is_in_await_expression, wrap_node) = {
                let nodes = program.nodes(file.file_index());
                let parent = nodes[property_access_to_convert].parent;
                let is_in_await = parent.is_some_and(|p| ast::is_await_expression(&nodes[p]));
                (
                    is_in_await,
                    if is_in_await {
                        parent.unwrap()
                    } else {
                        nodes[property_access_to_convert]
                            .expression()
                            .expect("property access expression")
                    },
                )
            };
            let wrap_start = {
                let mut nodes = program.nodes_mut(file.file_index());
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes, file, wrap_node, false, /*includeJSDoc*/
                )
            };
            let wrap_end = program.nodes(file.file_index())[property_access_to_convert].end();
            let (lsp_range, fidelity) =
                self.create_lsp_range_from_bounds(wrap_start, wrap_end, file);
            if !fidelity.is_exact() {
                return Ok(None);
            }
            replacement_span = Some(lsp_range);
        }

        if origin_is_type_only_alias(origin) {
            has_action = true;
        }

        // Provide object member completions when missing commas, and insert missing commas.
        // For example:
        //
        //    interface I {
        //        a: string;
        //        b: number
        //     }
        //
        //     const cc: I = { a: "red" | }
        //
        // Completion should add a comma after "red" and provide completions for b
        if data.completion_kind == CompletionKind::ObjectPropertyDeclaration
            && context_token.is_some()
            && !{
                let mut nodes = program.nodes_mut(file.file_index());
                let ct = context_token.unwrap();
                let ct_pos = nodes[ct].pos();
                let preceding = tsc_astnav::tokens::find_preceding_token_ex(
                    &mut nodes,
                    file,
                    ct_pos,
                    Some(ct),
                    false, /*excludeJSDoc*/
                );
                ast::node_has_kind(preceding, Kind::CommaToken, &nodes)
            }
        {
            let ct = context_token.unwrap();
            let (is_special, last_token_is_ct, is_shorthand_other_line) = {
                let mut nodes = program.nodes_mut(file.file_index());
                let parent = nodes[ct].parent;
                let grandparent = parent.and_then(|p| nodes[p].parent);
                let is_special = grandparent.is_some_and(|gp| {
                    ast::is_method_declaration(&nodes[gp])
                        || ast::is_get_accessor_declaration(&nodes[gp])
                        || ast::is_set_accessor_declaration(&nodes[gp])
                }) || parent.is_some_and(|p| ast::is_spread_assignment(&nodes[p]));
                let last_token_is_ct = {
                    let property_assignment = ast::find_ancestor(parent, &nodes, &mut |n, _| {
                        ast::is_property_assignment(n)
                    });
                    property_assignment.is_some_and(|pa| {
                        tsc_lsutil::children::get_last_token(&mut nodes, Some(pa), file) == Some(ct)
                    })
                };
                let is_shorthand_other_line =
                    parent.is_some_and(|p| ast::is_shorthand_property_assignment(&nodes[p])) && {
                        let nodes2 = program.nodes(file.file_index());
                        get_line_of_position(&nodes2, file, nodes[ct].end())
                            != get_line_of_position(&nodes2, file, position)
                    };
                (is_special, last_token_is_ct, is_shorthand_other_line)
            };
            if is_special || last_token_is_ct || is_shorthand_other_line {
                source = completion_source::OBJECT_LITERAL_MEMBER_WITH_COMMA.to_string();
                has_action = true;
            }
        }

        let mut additional_text_edits: Option<Vec<lsproto::TextEdit>> = None;
        if preferences
            .completion_preferences
            .include_completions_with_class_member_snippets
            .is_true()
            && data.completion_kind == CompletionKind::MemberLike
            && is_class_like_member_completion(&program, symbol, data.location, file)
        {
            let member_completion_entry = self.get_entry_for_member_completion(
                ctx,
                type_checker,
                symbol,
                &name,
                data.location,
                position,
                context_token,
                file,
            )?;
            let Some(member_completion_entry) = member_completion_entry else {
                return Ok(None);
            };
            insert_text = member_completion_entry.insert_text;
            filter_text = member_completion_entry.filter_text;
            is_snippet = member_completion_entry.is_snippet;
            if !member_completion_entry.additional_text_edits.is_empty() {
                additional_text_edits = Some(member_completion_entry.additional_text_edits);
                has_action = true;
                source = completion_source::CLASS_MEMBER_SNIPPET.to_string();
            }
        }

        let mut sort_text = sort_text.to_string();
        if origin_is_object_literal_method(origin) {
            let method = origin.unwrap().as_object_literal_method();
            insert_text = method.insert_text.clone();
            is_snippet = method.is_snippet;
            label_details = method.label_details.clone();
            if !client_supports_item_label_details(ctx) {
                if let Some(detail) = method
                    .label_details
                    .as_ref()
                    .and_then(|ld| ld.detail.clone())
                {
                    name = format!("{name}{detail}");
                }
                label_details = None;
            }
            source = completion_source::OBJECT_LITERAL_METHOD_SNIPPET.to_string();
            sort_text = sort_below(&sort_text);
        }

        if data.is_jsx_identifier_expected
            && !data.is_right_of_open_tag
            && client_supports_item_snippet(ctx)
            && preferences
                .completion_preferences
                .jsx_attribute_completion_style
                != tsc_lsutil::JsxAttributeCompletionStyle::NONE_VALUE
            && !{
                let nodes = program.nodes(file.file_index());
                data.location
                    .and_then(|l| nodes[l].parent)
                    .is_some_and(|p| {
                        ast::is_jsx_attribute(&nodes[p]) && nodes[p].initializer().is_some()
                    })
            }
        {
            let mut use_braces = preferences
                .completion_preferences
                .jsx_attribute_completion_style
                == tsc_lsutil::JsxAttributeCompletionStyle::BRACES;
            let location = data.location.expect("jsx attribute location");
            let t = type_checker.get_type_of_symbol_at_location(symbol, Some(location));

            // If is boolean like or undefined, don't return a snippet, we want to return just the completion.
            let (t_is_boolean_like, t_is_union, t_union_types) = {
                let t_ref = type_checker.types.get(t);
                (
                    t_ref.is_boolean_like(),
                    t_ref.is_union(),
                    t_ref.types().to_vec(),
                )
            };
            let any_union_member_is_boolean_like = t_is_union
                && t_union_types
                    .iter()
                    .any(|&u| type_checker.types.get(u).is_boolean_like());
            if preferences
                .completion_preferences
                .jsx_attribute_completion_style
                == tsc_lsutil::JsxAttributeCompletionStyle::AUTO
                && !t_is_boolean_like
                && !any_union_member_is_boolean_like
            {
                let t_is_string_like = type_checker.types.get(t).is_string_like();
                let all_union_members_string_like_or_undefined = t_is_union
                    && t_union_types.iter().all(|&u| {
                        let flags_ok = {
                            let t2 = type_checker.types.get(u);
                            t2.flags().intersects(
                                tsc_checker::types::TypeFlags::STRING_LIKE
                                    | tsc_checker::types::TypeFlags::UNDEFINED,
                            )
                        };
                        flags_ok
                            || is_string_and_empty_anonymous_object_intersection(type_checker, u)
                    });
                if t_is_string_like || all_union_members_string_like_or_undefined {
                    // If type is string-like or undefined, use quotes.
                    insert_text = format!(
                        "{}={}",
                        escape_snippet_text(&name),
                        crate::utilities::quote(
                            &program.nodes(file.file_index()),
                            file,
                            preferences,
                            "$1",
                        )
                    );
                    is_snippet = true;
                } else {
                    // Use braces for everything else.
                    use_braces = true;
                }
            }

            if use_braces {
                insert_text = format!("{}={{$1}}", escape_snippet_text(&name));
                is_snippet = true;
            }
        }

        let parent_named_import_or_export = {
            let nodes = program.nodes(file.file_index());
            ast::find_ancestor(data.location, &nodes, &mut |n, _| {
                is_named_imports_or_exports(n)
            })
        };
        if let Some(parent_named_import_or_export) = parent_named_import_or_export {
            if !tsc_scanner::utilities::is_identifier_text(
                &name,
                tsc_core::languagevariant::LanguageVariant::Standard,
            ) {
                insert_text = quote_property_name(
                    &program.nodes(file.file_index()),
                    file,
                    preferences,
                    &name,
                );

                if {
                    let nodes = program.nodes(file.file_index());
                    nodes[parent_named_import_or_export].kind == Kind::NamedImports
                } {
                    // Check if it is `import { ^here as name } from '...'``.
                    // We have to access the scanner here to check if it is `{ ^here as name }`` or `{ ^here, as, name }`.
                    let text = program.nodes(file.file_index())[file]
                        .as_source_file()
                        .text
                        .clone();
                    let mut scanner = tsc_scanner::scanner::Scanner::new();
                    scanner.set_text(&text);
                    scanner.reset_pos(position.max(0) as usize);
                    if !(scanner.scan() == Kind::AsKeyword && scanner.scan() == Kind::Identifier) {
                        insert_text = format!(
                            "{insert_text} as {}",
                            generate_identifier_for_arbitrary_string(&name)
                        );
                    }
                }
            } else if {
                let nodes = program.nodes(file.file_index());
                nodes[parent_named_import_or_export].kind == Kind::NamedImports
            } {
                let possible_token = tsc_scanner::scanner::string_to_token(&name);
                if possible_token != Kind::Unknown
                    && (possible_token == Kind::AwaitKeyword
                        || ast::is_non_contextual_keyword(possible_token))
                {
                    insert_text = format!("{name} as {name}_");
                }
            }
        }

        // Commit characters
        let element_kind = {
            let location = data.location.expect("completion location");
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_lsutil::get_symbol_kind(
                Some(&mut *type_checker),
                symbol,
                location,
                &nodes,
                &program.symbols,
            )
        };
        let mut commit_characters: Option<Vec<String>> = None;
        if client_supports_item_commit_characters(ctx) {
            if element_kind == tsc_lsutil::ScriptElementKind::Warning
                || element_kind == tsc_lsutil::ScriptElementKind::String
            {
                commit_characters = Some(Vec::new());
            } else if !client_supports_default_commit_characters(ctx) {
                commit_characters = Some(data.default_commit_characters.clone());
            }
            // Otherwise use the completion list default.
        }

        let preselect = is_recommended_completion_match(
            symbol,
            data.recommended_completion,
            type_checker,
            &program,
        );
        let kind_modifiers = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_lsutil::get_symbol_modifiers(
                Some(&mut *type_checker),
                Some(symbol),
                &mut nodes,
                &program.symbols,
            )
        };

        Ok(Some(self.create_lsp_completion_item(
            ctx,
            name,
            &insert_text,
            &filter_text,
            sort_text,
            element_kind,
            kind_modifiers,
            replacement_span.as_ref(),
            commit_characters,
            label_details,
            file,
            position,
            is_member_completion,
            is_snippet,
            has_action,
            preselect,
            &source,
            None, /*autoImportFix*/
            additional_text_edits,
            None, /*detail*/
        )))
    }
}

impl CompletionDataBuilder<'_, '_> {
    /// `collectObjectLiteralMethodSymbols`.
    fn collect_object_literal_method_symbols(
        &mut self,
        members: &[SymbolId],
        enclosing_declaration: Option<NodeId>,
    ) -> Vec<ObjectLiteralMethodSymbol> {
        let is_js = {
            let nodes = self.nodes();
            ast::is_source_file_js(nodes[self.file].as_source_file())
        };
        if is_js {
            return Vec::new();
        }

        let mut methods = Vec::new();
        for &member in members {
            if !is_object_literal_method_symbol(&self.program.symbols, member) {
                continue;
            }
            let (display_name, _) = {
                let mut nodes = self.nodes_mut();
                get_completion_entry_display_name_for_symbol(
                    &mut nodes,
                    self.file,
                    self.preferences,
                    member,
                    None, /*origin*/
                    CompletionKind::ObjectPropertyDeclaration,
                    false, /*isJsxIdentifierExpected*/
                    &self.checker.borrow(),
                    &self.program,
                )
            };
            if display_name.is_empty() {
                continue;
            }
            let entry = self.l.get_entry_for_object_literal_method_completion(
                self.ctx,
                &mut self.checker.borrow_mut(),
                member,
                enclosing_declaration,
                self.file,
            );
            let Some(entry) = entry else {
                continue;
            };
            methods.push(ObjectLiteralMethodSymbol {
                symbol: member,
                origin: SymbolOriginInfo {
                    kind: SymbolOriginInfoKind::OBJECT_LITERAL_METHOD,
                    is_default_export: false,
                    is_from_package_json: false,
                    data: Some(SymbolOriginInfoData::ObjectLiteralMethod(Box::new(entry))),
                },
            });
        }
        methods
    }
}
