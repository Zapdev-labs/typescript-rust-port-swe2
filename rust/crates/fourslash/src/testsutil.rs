// Ported from tsc/internal/fourslash/tests/util/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Shared helpers for the generated fourslash tests: expected completion-item
// lists (globals, keywords, class elements, function members, ...), the
// `Ignored` sentinel, and small builders such as `insert_replace_text_edit`.
//
// Go's `var X = []fourslash.CompletionsExpectedItem{...}` lists are exposed as
// zero-arg accessors returning a fresh `Vec` on each call (the underlying
// `CompletionsExpectedItem` is not `Clone`), and Go's `...Plus` combinators
// take/return owned `Vec`s so generated call sites can pass `vec![...]`
// literals directly.

use tsc_lsproto::{self as lsproto, CompletionItemKind, CompletionItemTag};
use tsc_stringutil::compare_strings_case_insensitive_then_sensitive;

pub use crate::verify::{
    CompletionsExpectedItem, ExpectedCompletionEditRange, Ignored,
};

/// `Ignored` — Go's `var Ignored = struct{}{}` sentinel value, typed for
/// direct assignment to `CompletionsExpectedItemDefaults::edit_range`
/// (`ExpectedCompletionEditRange = *EditRange | Ignored | nil`).
#[allow(non_upper_case_globals)]
pub const ignored: ExpectedCompletionEditRange = ExpectedCompletionEditRange::Ignored;

/// Go's `ExpectedCompletionEditRange` is `any`, so the `Ignored` sentinel
/// assigns into it implicitly; mirror that with `From` for `.into()` sites.
///
/// PORT: if `verify.rs` grows this impl upstream, drop this one.
impl From<Ignored> for ExpectedCompletionEditRange {
    fn from(_: Ignored) -> Self {
        ExpectedCompletionEditRange::Ignored
    }
}

/// `var DefaultCommitCharacters`.
pub fn default_commit_characters() -> Vec<String> {
    vec![".".to_string(), ",".to_string(), ";".to_string()]
}

/// `InsertReplaceTextEdit`.
pub fn insert_replace_text_edit(
    new_text: impl Into<String>,
    edit_range: lsproto::Range,
) -> lsproto::TextEditOrInsertReplaceEdit {
    lsproto::TextEditOrInsertReplaceEdit {
        insert_replace_edit: Some(lsproto::InsertReplaceEdit {
            new_text: new_text.into(),
            insert: edit_range.clone(),
            replace: edit_range,
        }),
        ..Default::default()
    }
}

// PORT: `ls.SortTextGlobalsOrKeywords` (`"15"`),
// `ls.SortTextLocationPriority` (`"11"`) and `ls.DeprecateSortText` are
// `pub(crate)` inside `tsc-ls` (`ls/src/completions.rs` `sort_text` module);
// mirrored here until that crate exposes them publicly.
const SORT_TEXT_GLOBALS_OR_KEYWORDS: &str = "15";
const SORT_TEXT_LOCATION_PRIORITY: &str = "11";

/// `ls.DeprecateSortText`.
fn deprecate_sort_text(original: &str) -> String {
    format!("z{original}")
}

fn item(
    label: &str,
    kind: CompletionItemKind,
    sort_text: &str,
) -> CompletionsExpectedItem {
    lsproto::CompletionItem {
        label: label.to_string(),
        kind: Some(kind),
        sort_text: Some(sort_text.to_string()),
        ..Default::default()
    }
    .into()
}

/// A completion item with no explicit `SortText` (`nil` in Go — the
/// `SortTextLocationPriority` default kicks in when sorting).
fn unsorted_item(label: &str, kind: CompletionItemKind) -> CompletionsExpectedItem {
    lsproto::CompletionItem {
        label: label.to_string(),
        kind: Some(kind),
        ..Default::default()
    }
    .into()
}

/// `&lsproto.CompletionItem{ ..., Tags: {Deprecated}, SortText: DeprecateSortText(sort) }`.
fn deprecated_item(
    label: &str,
    kind: CompletionItemKind,
    sort_text: &str,
) -> CompletionsExpectedItem {
    lsproto::CompletionItem {
        label: label.to_string(),
        kind: Some(kind),
        tags: Some(vec![CompletionItemTag::Deprecated]),
        sort_text: Some(deprecate_sort_text(sort_text)),
        ..Default::default()
    }
    .into()
}

/// A globals/keywords entry: `SortText: ls.SortTextGlobalsOrKeywords`.
fn globals_item(label: &str, kind: CompletionItemKind) -> CompletionsExpectedItem {
    item(label, kind, SORT_TEXT_GLOBALS_OR_KEYWORDS)
}

/// `var CompletionGlobalThisItem`.
pub fn completion_global_this_item() -> CompletionsExpectedItem {
    globals_item("globalThis", CompletionItemKind::Module)
}

/// `var CompletionUndefinedVarItem`.
pub fn completion_undefined_var_item() -> CompletionsExpectedItem {
    globals_item("undefined", CompletionItemKind::Variable)
}

/// `var CompletionGlobalVars`.
pub fn completion_global_vars() -> Vec<CompletionsExpectedItem> {
    vec![
        globals_item("Array", CompletionItemKind::Variable),
        globals_item("ArrayBuffer", CompletionItemKind::Variable),
        globals_item("Boolean", CompletionItemKind::Variable),
        globals_item("DataView", CompletionItemKind::Variable),
        globals_item("Date", CompletionItemKind::Variable),
        globals_item("Error", CompletionItemKind::Variable),
        globals_item("EvalError", CompletionItemKind::Variable),
        globals_item("Float32Array", CompletionItemKind::Variable),
        globals_item("Float64Array", CompletionItemKind::Variable),
        globals_item("Function", CompletionItemKind::Variable),
        globals_item("Infinity", CompletionItemKind::Variable),
        globals_item("Int16Array", CompletionItemKind::Variable),
        globals_item("Int32Array", CompletionItemKind::Variable),
        globals_item("Int8Array", CompletionItemKind::Variable),
        globals_item("Intl", CompletionItemKind::Module),
        globals_item("JSON", CompletionItemKind::Variable),
        globals_item("Math", CompletionItemKind::Variable),
        globals_item("NaN", CompletionItemKind::Variable),
        globals_item("Number", CompletionItemKind::Variable),
        globals_item("Object", CompletionItemKind::Variable),
        globals_item("RangeError", CompletionItemKind::Variable),
        globals_item("ReferenceError", CompletionItemKind::Variable),
        globals_item("RegExp", CompletionItemKind::Variable),
        globals_item("String", CompletionItemKind::Variable),
        globals_item("SyntaxError", CompletionItemKind::Variable),
        globals_item("TypeError", CompletionItemKind::Variable),
        globals_item("URIError", CompletionItemKind::Variable),
        globals_item("Uint16Array", CompletionItemKind::Variable),
        globals_item("Uint32Array", CompletionItemKind::Variable),
        globals_item("Uint8Array", CompletionItemKind::Variable),
        globals_item("Uint8ClampedArray", CompletionItemKind::Variable),
        globals_item("decodeURI", CompletionItemKind::Function),
        globals_item("decodeURIComponent", CompletionItemKind::Function),
        globals_item("encodeURI", CompletionItemKind::Function),
        globals_item("encodeURIComponent", CompletionItemKind::Function),
        globals_item("eval", CompletionItemKind::Function),
        globals_item("isFinite", CompletionItemKind::Function),
        globals_item("isNaN", CompletionItemKind::Function),
        globals_item("parseFloat", CompletionItemKind::Function),
        globals_item("parseInt", CompletionItemKind::Function),
        deprecated_item("escape", CompletionItemKind::Function, SORT_TEXT_GLOBALS_OR_KEYWORDS),
        deprecated_item("unescape", CompletionItemKind::Function, SORT_TEXT_GLOBALS_OR_KEYWORDS),
    ]
}

/// `var CompletionGlobalKeywords`.
pub fn completion_global_keywords() -> Vec<CompletionsExpectedItem> {
    [
        "abstract", "any", "as", "asserts", "async", "await", "bigint", "boolean", "break", "case",
        "catch", "class", "const", "continue", "debugger", "declare", "default", "delete", "do",
        "else", "enum", "export", "extends", "false", "finally", "for", "function", "if",
        "implements", "import", "in", "infer", "instanceof", "interface", "keyof", "let", "module",
        "namespace", "never", "new", "null", "number", "object", "package", "readonly", "return",
        "satisfies", "string", "super", "switch", "symbol", "this", "throw", "true", "try", "type",
        "typeof", "unique", "unknown", "using", "var", "void", "while", "with", "yield",
    ]
    .into_iter()
    .map(|label| globals_item(label, CompletionItemKind::Keyword))
    .collect()
}

/// `var CompletionGlobalTypeDecls`.
pub fn completion_global_type_decls() -> Vec<CompletionsExpectedItem> {
    vec![
        globals_item("Symbol", CompletionItemKind::Interface),
        globals_item("PropertyKey", CompletionItemKind::Class),
        globals_item("PropertyDescriptor", CompletionItemKind::Interface),
        globals_item("PropertyDescriptorMap", CompletionItemKind::Interface),
        globals_item("Object", CompletionItemKind::Variable),
        globals_item("ObjectConstructor", CompletionItemKind::Interface),
        globals_item("Function", CompletionItemKind::Variable),
        globals_item("FunctionConstructor", CompletionItemKind::Interface),
        globals_item("ThisParameterType", CompletionItemKind::Class),
        globals_item("OmitThisParameter", CompletionItemKind::Class),
        globals_item("CallableFunction", CompletionItemKind::Interface),
        globals_item("NewableFunction", CompletionItemKind::Interface),
        globals_item("IArguments", CompletionItemKind::Interface),
        globals_item("String", CompletionItemKind::Variable),
        globals_item("StringConstructor", CompletionItemKind::Interface),
        globals_item("Boolean", CompletionItemKind::Variable),
        globals_item("BooleanConstructor", CompletionItemKind::Interface),
        globals_item("Number", CompletionItemKind::Variable),
        globals_item("NumberConstructor", CompletionItemKind::Interface),
        globals_item("TemplateStringsArray", CompletionItemKind::Interface),
        globals_item("ImportMeta", CompletionItemKind::Interface),
        globals_item("ImportCallOptions", CompletionItemKind::Interface),
        deprecated_item(
            "ImportAssertions",
            CompletionItemKind::Interface,
            SORT_TEXT_GLOBALS_OR_KEYWORDS,
        ),
        globals_item("ImportAttributes", CompletionItemKind::Interface),
        globals_item("Math", CompletionItemKind::Variable),
        globals_item("Date", CompletionItemKind::Variable),
        globals_item("DateConstructor", CompletionItemKind::Interface),
        globals_item("RegExpMatchArray", CompletionItemKind::Interface),
        globals_item("RegExpExecArray", CompletionItemKind::Interface),
        globals_item("RegExp", CompletionItemKind::Variable),
        globals_item("RegExpConstructor", CompletionItemKind::Interface),
        globals_item("Error", CompletionItemKind::Variable),
        globals_item("ErrorConstructor", CompletionItemKind::Interface),
        globals_item("EvalError", CompletionItemKind::Variable),
        globals_item("EvalErrorConstructor", CompletionItemKind::Interface),
        globals_item("RangeError", CompletionItemKind::Variable),
        globals_item("RangeErrorConstructor", CompletionItemKind::Interface),
        globals_item("ReferenceError", CompletionItemKind::Variable),
        globals_item("ReferenceErrorConstructor", CompletionItemKind::Interface),
        globals_item("SyntaxError", CompletionItemKind::Variable),
        globals_item("SyntaxErrorConstructor", CompletionItemKind::Interface),
        globals_item("TypeError", CompletionItemKind::Variable),
        globals_item("TypeErrorConstructor", CompletionItemKind::Interface),
        globals_item("URIError", CompletionItemKind::Variable),
        globals_item("URIErrorConstructor", CompletionItemKind::Interface),
        globals_item("JSON", CompletionItemKind::Variable),
        globals_item("ReadonlyArray", CompletionItemKind::Interface),
        globals_item("ConcatArray", CompletionItemKind::Interface),
        globals_item("Array", CompletionItemKind::Variable),
        globals_item("ArrayConstructor", CompletionItemKind::Interface),
        globals_item("TypedPropertyDescriptor", CompletionItemKind::Interface),
        globals_item("ClassDecorator", CompletionItemKind::Class),
        globals_item("PropertyDecorator", CompletionItemKind::Class),
        globals_item("MethodDecorator", CompletionItemKind::Class),
        globals_item("ParameterDecorator", CompletionItemKind::Class),
        globals_item("ClassMemberDecoratorContext", CompletionItemKind::Class),
        globals_item("DecoratorContext", CompletionItemKind::Class),
        globals_item("DecoratorMetadata", CompletionItemKind::Class),
        globals_item("DecoratorMetadataObject", CompletionItemKind::Class),
        globals_item("ClassDecoratorContext", CompletionItemKind::Interface),
        globals_item("ClassMethodDecoratorContext", CompletionItemKind::Interface),
        globals_item("ClassGetterDecoratorContext", CompletionItemKind::Interface),
        globals_item("ClassSetterDecoratorContext", CompletionItemKind::Interface),
        globals_item("ClassAccessorDecoratorContext", CompletionItemKind::Interface),
        globals_item("ClassAccessorDecoratorTarget", CompletionItemKind::Interface),
        globals_item("ClassAccessorDecoratorResult", CompletionItemKind::Interface),
        globals_item("ClassFieldDecoratorContext", CompletionItemKind::Interface),
        globals_item("PromiseConstructorLike", CompletionItemKind::Class),
        globals_item("PromiseLike", CompletionItemKind::Interface),
        globals_item("Promise", CompletionItemKind::Interface),
        globals_item("Awaited", CompletionItemKind::Class),
        globals_item("ArrayLike", CompletionItemKind::Interface),
        globals_item("Partial", CompletionItemKind::Class),
        globals_item("Required", CompletionItemKind::Class),
        globals_item("Readonly", CompletionItemKind::Class),
        globals_item("Pick", CompletionItemKind::Class),
        globals_item("Record", CompletionItemKind::Class),
        globals_item("Exclude", CompletionItemKind::Class),
        globals_item("Extract", CompletionItemKind::Class),
        globals_item("Omit", CompletionItemKind::Class),
        globals_item("NonNullable", CompletionItemKind::Class),
        globals_item("Parameters", CompletionItemKind::Class),
        globals_item("ConstructorParameters", CompletionItemKind::Class),
        globals_item("ReturnType", CompletionItemKind::Class),
        globals_item("InstanceType", CompletionItemKind::Class),
        globals_item("Uppercase", CompletionItemKind::Class),
        globals_item("Lowercase", CompletionItemKind::Class),
        globals_item("Capitalize", CompletionItemKind::Class),
        globals_item("Uncapitalize", CompletionItemKind::Class),
        globals_item("NoInfer", CompletionItemKind::Class),
        globals_item("ThisType", CompletionItemKind::Interface),
        globals_item("ArrayBuffer", CompletionItemKind::Variable),
        globals_item("ArrayBufferTypes", CompletionItemKind::Interface),
        globals_item("ArrayBufferLike", CompletionItemKind::Class),
        globals_item("ArrayBufferConstructor", CompletionItemKind::Interface),
        globals_item("ArrayBufferView", CompletionItemKind::Interface),
        globals_item("DataView", CompletionItemKind::Variable),
        globals_item("DataViewConstructor", CompletionItemKind::Interface),
        globals_item("Int8Array", CompletionItemKind::Variable),
        globals_item("Int8ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Uint8Array", CompletionItemKind::Variable),
        globals_item("Uint8ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Uint8ClampedArray", CompletionItemKind::Variable),
        globals_item("Uint8ClampedArrayConstructor", CompletionItemKind::Interface),
        globals_item("Int16Array", CompletionItemKind::Variable),
        globals_item("Int16ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Uint16Array", CompletionItemKind::Variable),
        globals_item("Uint16ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Int32Array", CompletionItemKind::Variable),
        globals_item("Int32ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Uint32Array", CompletionItemKind::Variable),
        globals_item("Uint32ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Float32Array", CompletionItemKind::Variable),
        globals_item("Float32ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Float64Array", CompletionItemKind::Variable),
        globals_item("Float64ArrayConstructor", CompletionItemKind::Interface),
        globals_item("Intl", CompletionItemKind::Module),
        globals_item("WeakKey", CompletionItemKind::Class),
        globals_item("WeakKeyTypes", CompletionItemKind::Interface),
    ]
}

/// `var CompletionTypeKeywords`.
pub fn completion_type_keywords() -> Vec<CompletionsExpectedItem> {
    [
        "any", "asserts", "bigint", "boolean", "false", "infer", "keyof", "never", "null", "number",
        "object", "readonly", "string", "symbol", "true", "typeof", "undefined", "unique",
        "unknown", "void",
    ]
    .into_iter()
    .map(|label| globals_item(label, CompletionItemKind::Keyword))
    .collect()
}

/// `var CompletionClassElementKeywords`.
pub fn completion_class_element_keywords() -> Vec<CompletionsExpectedItem> {
    [
        "abstract",
        "accessor",
        "async",
        "constructor",
        "declare",
        "get",
        "override",
        "private",
        "protected",
        "public",
        "readonly",
        "set",
        "static",
    ]
    .into_iter()
    .map(|label| globals_item(label, CompletionItemKind::Keyword))
    .collect()
}

/// `var CompletionClassElementInJSKeywords`.
pub fn completion_class_element_in_js_keywords() -> Vec<CompletionsExpectedItem> {
    get_in_js_keywords(completion_class_element_keywords())
}

/// `var CompletionGlobals`.
pub fn completion_globals() -> Vec<CompletionsExpectedItem> {
    let mut all = completion_global_vars();
    all.extend(completion_global_keywords());
    all.push(completion_global_this_item());
    all.push(completion_undefined_var_item());
    sort_completion_items(all)
}

/// `sortCompletionItems` — stable sort by `SortText` (defaulting to
/// `ls.SortTextLocationPriority`), then by label, using
/// `CompareStringsCaseInsensitiveThenSensitive`.
fn sort_completion_items(mut items: Vec<CompletionsExpectedItem>) -> Vec<CompletionsExpectedItem> {
    items.sort_by(|a, b| {
        let a_sort_text = item_sort_text(a).unwrap_or(SORT_TEXT_LOCATION_PRIORITY);
        let b_sort_text = item_sort_text(b).unwrap_or(SORT_TEXT_LOCATION_PRIORITY);
        let by_sort_text = compare_strings_case_insensitive_then_sensitive(
            a_sort_text.as_bytes(),
            b_sort_text.as_bytes(),
        );
        if by_sort_text != 0 {
            return by_sort_text.cmp(&0);
        }
        compare_strings_case_insensitive_then_sensitive(
            item_label(a).as_bytes(),
            item_label(b).as_bytes(),
        )
        .cmp(&0)
    });
    items
}

/// `item.Label` / `item` — the label the expected item is matched against.
fn item_label(item: &CompletionsExpectedItem) -> &str {
    match item {
        CompletionsExpectedItem::Label(label) => label,
        CompletionsExpectedItem::Item(item) => &item.item.label,
    }
}

/// `item.SortText`, if this is a full completion item.
fn item_sort_text(item: &CompletionsExpectedItem) -> Option<&str> {
    match item {
        CompletionsExpectedItem::Item(item) => item.item.sort_text.as_deref(),
        CompletionsExpectedItem::Label(_) => None,
    }
}

/// `CompletionGlobalsPlus`.
pub fn completion_globals_plus(
    items: impl IntoIterator<Item = CompletionsExpectedItem>,
    no_lib: bool,
) -> Vec<CompletionsExpectedItem> {
    let mut all: Vec<CompletionsExpectedItem> = items.into_iter().collect();
    if no_lib {
        all.push(completion_global_this_item());
        all.push(completion_undefined_var_item());
        all.extend(completion_global_keywords());
    } else {
        all.extend(completion_globals());
    }
    sort_completion_items(all)
}

/// `CompletionGlobalTypesPlus`.
pub fn completion_global_types_plus(
    items: impl IntoIterator<Item = CompletionsExpectedItem>,
) -> Vec<CompletionsExpectedItem> {
    let mut all = completion_global_type_decls();
    all.push(completion_global_this_item());
    all.extend(completion_type_keywords());
    all.extend(items);
    sort_completion_items(all)
}

/// `var CompletionGlobalTypes`.
pub fn completion_global_types() -> Vec<CompletionsExpectedItem> {
    completion_global_types_plus(Vec::new())
}

/// `getInJSKeywords` — drops keywords that are not valid in JS files.
fn get_in_js_keywords(
    keywords: impl IntoIterator<Item = CompletionsExpectedItem>,
) -> Vec<CompletionsExpectedItem> {
    keywords
        .into_iter()
        .filter(|item| {
            !matches!(
                item_label(item),
                "enum"
                    | "interface"
                    | "implements"
                    | "private"
                    | "protected"
                    | "public"
                    | "abstract"
                    | "any"
                    | "boolean"
                    | "declare"
                    | "infer"
                    | "is"
                    | "keyof"
                    | "module"
                    | "namespace"
                    | "never"
                    | "readonly"
                    | "number"
                    | "object"
                    | "string"
                    | "symbol"
                    | "type"
                    | "unique"
                    | "override"
                    | "unknown"
                    | "global"
                    | "bigint"
            )
        })
        .collect()
}

/// `var CompletionGlobalInJSKeywords`.
pub fn completion_global_in_js_keywords() -> Vec<CompletionsExpectedItem> {
    get_in_js_keywords(completion_global_keywords())
}

/// `CompletionGlobalsInJSPlus`.
pub fn completion_globals_in_js_plus(
    items: impl IntoIterator<Item = CompletionsExpectedItem>,
    no_lib: bool,
) -> Vec<CompletionsExpectedItem> {
    let mut all: Vec<CompletionsExpectedItem> = items.into_iter().collect();
    all.push(completion_global_this_item());
    all.push(completion_undefined_var_item());
    all.extend(completion_global_in_js_keywords());
    if !no_lib {
        all.extend(completion_global_vars());
    }
    sort_completion_items(all)
}

/// `var CompletionConstructorParameterKeywords`.
pub fn completion_constructor_parameter_keywords() -> Vec<CompletionsExpectedItem> {
    ["override", "private", "protected", "public", "readonly"]
        .into_iter()
        .map(|label| globals_item(label, CompletionItemKind::Keyword))
        .collect()
}

/// `var CompletionFunctionMembers`.
pub fn completion_function_members() -> Vec<CompletionsExpectedItem> {
    vec![
        unsorted_item("apply", CompletionItemKind::Method),
        unsorted_item("arguments", CompletionItemKind::Field),
        unsorted_item("bind", CompletionItemKind::Method),
        unsorted_item("call", CompletionItemKind::Method),
        unsorted_item("caller", CompletionItemKind::Field),
        unsorted_item("length", CompletionItemKind::Field),
        unsorted_item("toString", CompletionItemKind::Method),
    ]
}

/// `CompletionFunctionMembersPlus`.
pub fn completion_function_members_plus(
    items: impl IntoIterator<Item = CompletionsExpectedItem>,
) -> Vec<CompletionsExpectedItem> {
    let mut all = completion_function_members();
    all.extend(items);
    sort_completion_items(all)
}

/// `var CompletionFunctionMembersWithPrototype`.
pub fn completion_function_members_with_prototype() -> Vec<CompletionsExpectedItem> {
    let mut all = completion_function_members();
    all.push(unsorted_item("prototype", CompletionItemKind::Field));
    sort_completion_items(all)
}

/// `CompletionFunctionMembersWithPrototypePlus`.
pub fn completion_function_members_with_prototype_plus(
    items: impl IntoIterator<Item = CompletionsExpectedItem>,
) -> Vec<CompletionsExpectedItem> {
    let mut all = completion_function_members_with_prototype();
    all.extend(items);
    sort_completion_items(all)
}

/// `CompletionTypeKeywordsPlus`.
pub fn completion_type_keywords_plus(
    items: impl IntoIterator<Item = CompletionsExpectedItem>,
) -> Vec<CompletionsExpectedItem> {
    let mut all = completion_type_keywords();
    all.extend(items);
    sort_completion_items(all)
}

/// `var CompletionTypeAssertionKeywords`.
pub fn completion_type_assertion_keywords() -> Vec<CompletionsExpectedItem> {
    completion_global_types_plus(vec![globals_item("const", CompletionItemKind::Keyword)])
}

/// `ToAny` — Go's `[]T → []any` widening has no Rust equivalent; this is an
/// identity `collect` so generated call sites keep the same shape (the `any`
/// side is carried by the receiving parameter's `Into`/enum type).
pub fn to_any<T>(items: impl IntoIterator<Item = T>) -> Vec<T> {
    items.into_iter().collect()
}
