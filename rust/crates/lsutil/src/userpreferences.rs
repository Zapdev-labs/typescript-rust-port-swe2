// Ported from tsc/internal/ls/lsutil/userpreferences.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.
//
// PORT(global): `type X string` preference enums are `Cow<'static, str>`
// newtypes (unknown values survive exactly like Go strings);
// `type OrganizeImportsCollation bool` and the `type X int` enums are
// tuple newtypes; `map[string]any` is `serde_json::Map<String, Value>`.

use std::borrow::Cow;
use std::io::Read;

use serde::{Deserialize, Deserializer, Serialize};
use serde::de::{self, Visitor};
use serde_json::{Map, Value};
use tsc_core::tristate::{bool_to_tristate, Tristate, TS_FALSE, TS_TRUE, TS_UNKNOWN};
use tsc_modulespecifiers::util::is_excluded_by_regex;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath};
use tsc_vfs::vfsmatch::{self, SpecMatcher, USAGE_EXCLUDE};

use crate::formatcodeoptions::get_default_format_code_settings;
use crate::userpreferences_generated::UserPreferences;

/// `NewDefaultUserPreferences`
pub fn new_default_user_preferences() -> UserPreferences {
    UserPreferences {
        format_code_settings: get_default_format_code_settings(),

        auto_closing_tags: TS_TRUE,
        complete_jsdocs: TS_TRUE,
        generate_return_in_doc_template: TS_TRUE,

        allow_rename_of_import_path: TS_TRUE,
        provide_refactor_not_applicable_reason: TS_TRUE,
        format_enabled: TS_TRUE,
        validate_enabled: TS_TRUE,
        display_parts_for_jsdoc: TS_TRUE,
        disable_line_text_in_references: TS_TRUE,
        report_style_checks_as_warnings: TS_TRUE,

        exclude_library_symbols_in_nav_to: TS_TRUE,
        workspace_symbols_scope: WorkspaceSymbolsScope::ALL_OPEN_PROJECTS,

        completion_preferences: crate::userpreferences_generated::CompletionPreferences {
            include_completions_for_module_exports: TS_TRUE,
            include_completions_for_import_statements: TS_TRUE,
            ..Default::default()
        },
        ..Default::default()
    }
}

/// `type QuotePreference string`
#[derive(Clone, Default, PartialEq, Eq, Debug, Serialize)]
#[serde(transparent)]
pub struct QuotePreference(pub Cow<'static, str>);

impl QuotePreference {
    /// `QuotePreferenceUnknown`
    pub const UNKNOWN: Self = Self(Cow::Borrowed(""));
    /// `QuotePreferenceAuto`
    pub const AUTO: Self = Self(Cow::Borrowed("auto"));
    /// `QuotePreferenceDouble`
    pub const DOUBLE: Self = Self(Cow::Borrowed("double"));
    /// `QuotePreferenceSingle`
    pub const SINGLE: Self = Self(Cow::Borrowed("single"));

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// `type WorkspaceSymbolsScope string`
#[derive(Clone, Default, PartialEq, Eq, Debug, Serialize)]
#[serde(transparent)]
pub struct WorkspaceSymbolsScope(pub Cow<'static, str>);

impl WorkspaceSymbolsScope {
    /// `WorkspaceSymbolsScopeAllOpenProjects`
    pub const ALL_OPEN_PROJECTS: Self = Self(Cow::Borrowed("allOpenProjects"));
    /// `WorkspaceSymbolsScopeCurrentProject`
    pub const CURRENT_PROJECT: Self = Self(Cow::Borrowed("currentProject"));

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// `type JsxAttributeCompletionStyle string`
#[derive(Clone, Default, PartialEq, Eq, Debug, Serialize)]
#[serde(transparent)]
pub struct JsxAttributeCompletionStyle(pub Cow<'static, str>);

impl JsxAttributeCompletionStyle {
    /// `JsxAttributeCompletionStyleUnknown`
    pub const UNKNOWN: Self = Self(Cow::Borrowed(""));
    /// `JsxAttributeCompletionStyleAuto`
    pub const AUTO: Self = Self(Cow::Borrowed("auto"));
    /// `JsxAttributeCompletionStyleBraces`
    pub const BRACES: Self = Self(Cow::Borrowed("braces"));
    /// `JsxAttributeCompletionStyleNone`
    pub const NONE_VALUE: Self = Self(Cow::Borrowed("none"));

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// `type IncludeInlayParameterNameHints string`
#[derive(Clone, Default, PartialEq, Eq, Debug, Serialize)]
#[serde(transparent)]
pub struct IncludeInlayParameterNameHints(pub Cow<'static, str>);

impl IncludeInlayParameterNameHints {
    /// `IncludeInlayParameterNameHintsNone`
    pub const NONE: Self = Self(Cow::Borrowed(""));
    /// `IncludeInlayParameterNameHintsAll`
    pub const ALL: Self = Self(Cow::Borrowed("all"));
    /// `IncludeInlayParameterNameHintsLiterals`
    pub const LITERALS: Self = Self(Cow::Borrowed("literals"));

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// `Deserialize` for the string newtypes: arbitrary strings are kept verbatim
// like Go's `type X string` (the switch-based parsers only produce consts).
macro_rules! str_newtype_deserialize {
    ($t:ty) => {
        impl<'de> Deserialize<'de> for $t {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                struct V;
                impl<'de> Visitor<'de> for V {
                    type Value = $t;

                    fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                        f.write_str("a string")
                    }

                    fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
                        Ok(<$t>::from_str_value(v))
                    }

                    // `null` decodes to the zero value, like Go leaving a
                    // `string` field untouched on `null`.
                    fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
                        Ok(<$t>::default())
                    }
                }
                deserializer.deserialize_any(V)
            }
        }
    };
}

impl QuotePreference {
    fn from_str_value(s: &str) -> Self {
        Self(Cow::Owned(s.to_string()))
    }
}
impl WorkspaceSymbolsScope {
    fn from_str_value(s: &str) -> Self {
        Self(Cow::Owned(s.to_string()))
    }
}
impl JsxAttributeCompletionStyle {
    fn from_str_value(s: &str) -> Self {
        Self(Cow::Owned(s.to_string()))
    }
}
impl IncludeInlayParameterNameHints {
    fn from_str_value(s: &str) -> Self {
        Self(Cow::Owned(s.to_string()))
    }
}

str_newtype_deserialize!(QuotePreference);
str_newtype_deserialize!(WorkspaceSymbolsScope);
str_newtype_deserialize!(JsxAttributeCompletionStyle);
str_newtype_deserialize!(IncludeInlayParameterNameHints);

/// `type OrganizeImportsSort int`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct OrganizeImportsSort(pub i32);

impl OrganizeImportsSort {
    /// `OrganizeImportsSortAuto`
    pub const AUTO: Self = Self(0);
    /// `OrganizeImportsSortOrdinal`
    pub const ORDINAL: Self = Self(1);
    /// `OrganizeImportsSortOrdinalIgnoreCase`
    pub const ORDINAL_IGNORE_CASE: Self = Self(2);
    /// `OrganizeImportsSortNatural`
    pub const NATURAL: Self = Self(3);
    /// `OrganizeImportsSortNaturalIgnoreCase`
    pub const NATURAL_IGNORE_CASE: Self = Self(4);
}

/// `type OrganizeImportsCollation bool`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct OrganizeImportsCollation(pub bool);

impl OrganizeImportsCollation {
    /// `OrganizeImportsCollationOrdinal`
    pub const ORDINAL: Self = Self(false);
    /// `OrganizeImportsCollationUnicode`
    pub const UNICODE: Self = Self(true);
}

/// `type OrganizeImportsCaseFirst int`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct OrganizeImportsCaseFirst(pub i32);

impl OrganizeImportsCaseFirst {
    /// `OrganizeImportsCaseFirstDefault`
    pub const DEFAULT: Self = Self(0);
    /// `OrganizeImportsCaseFirstLower`
    pub const LOWER: Self = Self(1);
    /// `OrganizeImportsCaseFirstUpper`
    pub const UPPER: Self = Self(2);
}

/// `type OrganizeImportsTypeOrder int`
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct OrganizeImportsTypeOrder(pub i32);

impl OrganizeImportsTypeOrder {
    /// `OrganizeImportsTypeOrderAuto`
    pub const AUTO: Self = Self(0);
    /// `OrganizeImportsTypeOrderLast`
    pub const LAST: Self = Self(1);
    /// `OrganizeImportsTypeOrderInline`
    pub const INLINE: Self = Self(2);
    /// `OrganizeImportsTypeOrderFirst`
    pub const FIRST: Self = Self(3);
}

/// `value.(bool)` in Go `any` terms.
pub(crate) fn value_as_bool(value: &Value) -> Option<bool> {
    value.as_bool()
}

/// `case int:` / `case float64:` — Go `int(value)` truncates floats toward 0;
/// serde_json `Value` numbers map to i64/u64/f64.
pub(crate) fn value_as_int(value: &Value) -> Option<i64> {
    value
        .as_i64()
        .or_else(|| value.as_u64().map(|u| u as i64))
        .or_else(|| value.as_f64().map(|f| f as i64))
}

/// `parsePreferenceTristate`
pub(crate) fn parse_preference_tristate(value: &Value) -> Tristate {
    if let Some(v) = value_as_bool(value) {
        return bool_to_tristate(v);
    }
    TS_UNKNOWN
}

/// `parseOrganizeImportsCaseSensitivity`
pub(crate) fn parse_organize_imports_case_sensitivity(value: &Value) -> Tristate {
    if let Some(v) = value.as_str() {
        match &*v.to_lowercase() {
            "caseinsensitive" => return TS_TRUE,
            "casesensitive" => return TS_FALSE,
            _ => {}
        }
    }
    parse_preference_tristate(value)
}

/// `invertPreferenceValue`
fn invert_preference_value(value: Value) -> Value {
    if let Value::Bool(b) = value {
        return Value::from(!b);
    }
    value
}

/// `getPreferenceConfigValue` — each tag may carry a `,invert` modifier
/// (`strings.Cut(tag, ",")`); the returned `Value` is the stored value with
/// `invert` applied, matching Go's `(any, bool)` result where `Some(null)`
/// means "present but nil".
pub(crate) fn get_preference_config_value(
    config: &Map<String, Value>,
    paths: &[&str],
) -> Option<Value> {
    for tag in paths {
        let (path, modifier) = tag.split_once(',').unwrap_or((tag, ""));
        if let Some(value) = get_nested_value(config, path) {
            if modifier == "invert" {
                return Some(invert_preference_value(value.clone()));
            }
            return Some(value.clone());
        }
    }
    None
}

/// `getNestedValue` — `map[string]any` traversal; a non-object intermediate
/// or a missing key returns `None`.
fn get_nested_value<'a>(config: &'a Map<String, Value>, path: &str) -> Option<&'a Value> {
    let mut current: Option<&Map<String, Value>> = Some(config);
    let mut parts = path.split('.').peekable();
    while let Some(part) = parts.next() {
        let m = current?;
        let v = m.get(part)?;
        if parts.peek().is_none() {
            return Some(v);
        }
        current = v.as_object();
    }
    None
}

/// `setNestedValue`
pub(crate) fn set_nested_value(config: &mut Map<String, Value>, path: &str, value: Value) {
    let parts: Vec<&str> = path.split('.').collect();
    let mut current = config;
    for part in &parts[..parts.len() - 1] {
        let entry = current
            .entry(part.to_string())
            .or_insert_with(|| Value::Object(Map::new()));
        // `next, ok := current[part].(map[string]any)` — a non-object entry is
        // replaced by a fresh map.
        if !entry.is_object() {
            *entry = Value::Object(Map::new());
        }
        current = entry.as_object_mut().unwrap();
    }
    current.insert(parts[parts.len() - 1].to_string(), value);
}

/// `normalizeCustomConfigFileName`
pub(crate) fn normalize_custom_config_file_name(name: &str) -> String {
    let name = name.trim();
    if name.contains(['/', '\\']) || name == ".." || name == "." {
        return String::new();
    }
    name.to_string()
}

impl tsc_json::UnmarshalerFrom for UserPreferences {
    /// `(*UserPreferences).UnmarshalJSONFrom`
    fn unmarshal_json_from<R: Read>(
        &mut self,
        dec: &mut tsc_json::Decoder<R>,
    ) -> Result<(), serde_json::Error> {
        let config: Map<String, Value> = tsc_json::unmarshal_decode(dec, &[])?;
        *self = new_default_user_preferences().with_config(&config);
        Ok(())
    }
}

impl UserPreferences {
    /// `(p UserPreferences) IsATADisabled` returns whether Automatic Type
    /// Acquisition is disabled based on user preferences. It checks the
    /// unified setting (tsserver.automaticTypeAcquisition.enabled) first,
    /// then falls back to the deprecated setting (disableAutomaticTypeAcquisition).
    pub fn is_ata_disabled(&self) -> bool {
        if !self.automatic_type_acquisition_enabled.is_unknown() {
            return !self.automatic_type_acquisition_enabled.is_true();
        }
        self.disable_automatic_type_acquisition.is_true()
    }

    /// `(p UserPreferences) ModuleSpecifierPreferences`
    pub fn module_specifier_preferences(&self) -> tsc_modulespecifiers::UserPreferences {
        tsc_modulespecifiers::UserPreferences {
            import_module_specifier_preference: self.import_module_specifier_preference,
            import_module_specifier_ending: self.import_module_specifier_ending,
            auto_import_specifier_exclude_regexes: self
                .auto_import_specifier_exclude_regexes
                .clone(),
        }
    }

    /// `(p UserPreferences) ParsedAutoImportFileExcludePatterns`
    pub fn parsed_auto_import_file_exclude_patterns(
        &self,
        case_sensitivity: CaseSensitivity,
    ) -> Option<SpecMatcher> {
        vfsmatch::new_spec_matcher(
            &self.auto_import_file_exclude_patterns,
            &RootedDirectoryPath::default(),
            USAGE_EXCLUDE,
            case_sensitivity,
        )
    }

    /// `(p UserPreferences) IsModuleSpecifierExcluded`
    pub fn is_module_specifier_excluded(&self, module_specifier: &str) -> bool {
        is_excluded_by_regex(module_specifier, &self.auto_import_specifier_exclude_regexes)
    }
}

/// `ParseUserPreferences` — applies editor settings first (tabSize,
/// indentSize, etc.) as raw-name defaults, then overlays language-specific
/// settings with increasing precedence: editor < javascript < typescript < js/ts.
pub fn parse_user_preferences(items: &Map<String, Value>) -> UserPreferences {
    let mut prefs = new_default_user_preferences();
    // Apply editor settings first (tabSize, indentSize, etc.) as raw-name defaults,
    // then overlay language-specific settings with increasing precedence:
    // editor < javascript < typescript < js/ts
    if let Some(editor_item) = items.get("editor") {
        if !editor_item.is_null() {
            if let Some(editor_settings) = editor_item.as_object() {
                let mut normalized_settings = editor_settings.clone();
                if let Some(tab_size) = normalized_settings.get("tabSize") {
                    if !normalized_settings.contains_key("indentSize") {
                        normalized_settings.insert("indentSize".to_string(), tab_size.clone());
                    }
                }
                if let Some(insert_spaces) = normalized_settings.get("insertSpaces") {
                    if !normalized_settings.contains_key("convertTabsToSpaces") {
                        normalized_settings
                            .insert("convertTabsToSpaces".to_string(), insert_spaces.clone());
                    }
                }
                let mut wrapped = Map::new();
                wrapped.insert("unstable".to_string(), Value::Object(normalized_settings));
                prefs = prefs.with_config(&wrapped);
            }
        }
    }
    // Apply javascript, then typescript, then js/ts (highest precedence).
    for section in ["javascript", "typescript", "js/ts"] {
        if let Some(item) = items.get(section) {
            if !item.is_null() {
                if let Some(settings) = item.as_object() {
                    prefs = prefs.with_config(settings);
                }
            }
        }
    }
    prefs
}
