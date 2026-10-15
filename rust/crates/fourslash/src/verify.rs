// Ported from tsc/internal/fourslash/fourslash.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `verify.*` assertion helpers — completions, code fixes, organize imports,
// import fixes, signature help, quick info, rename, diagnostics/errors, and
// the `MarkerInput`/expected-item input types they consume. See the PORT
// notes in fourslash.rs for the `testing.T` and sibling-API conventions.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::rc::Rc;

use serde::Serialize;
use tsc_collections::MultiMap;
use tsc_core::text::TextRange;
use tsc_core::textchange::TextChange;
use tsc_core::core::{
    filter, find, find_index, first_non_nil, map, map_filtered, must, or_else, stringify_json,
};
use tsc_core::tristate::{TS_TRUE, TS_UNKNOWN, bool_to_tristate};
use tsc_json as json;
use tsc_lsconv::{self as lsconv};
use tsc_lsproto::*;
use tsc_lsutil::{self as lsutil, UserPreferences};
use tsc_spanmap::Feature;
use tsc_stringutil::compare_strings_case_insensitive_then_sensitive;
use tsc_tspath::{self as tspath, RootedFilePath, RootedPath};

use crate::baselineutil;
use crate::fourslash::{
    FourslashTest, assert_valid_text_range, compare_positions, get_language_kind,
    remove_whitespace, select_code_fix_diagnostic, update_position_for_text_edit,
};
use crate::test_parser::{Marker, MarkerOrRange, RangeMarker};

/// `assertDeepEqual` — `cmp.Diff` has no Rust analog; Debug-dump both sides.
pub(crate) fn assert_deep_equal<T: PartialEq + std::fmt::Debug>(
    actual: &T,
    expected: &T,
    prefix: &str,
) {
    if actual != expected {
        panic!("{prefix}:\nactual:   {actual:#?}\nexpected: {expected:#?}");
    }
}

// --- completions -----------------------------------------------------------

/// `type CompletionsExpectedList struct`
#[derive(Default)]
pub struct CompletionsExpectedList {
    pub is_incomplete: bool,
    pub item_defaults: Option<CompletionsExpectedItemDefaults>,
    pub items: Option<CompletionsExpectedItems>,
    pub user_preferences: Option<UserPreferences>,
}

/// `type Ignored = struct{}` — see [ExpectedCompletionEditRange::Ignored].
pub struct Ignored;

/// `type ExpectedCompletionEditRange = any` — `*EditRange | Ignored | nil`.
#[derive(Default)]
pub enum ExpectedCompletionEditRange {
    /// Go `nil` — asserts `actual.EditRange` is also nil.
    #[default]
    None,
    /// Go `Ignored{}` — the edit range is intentionally not checked.
    Ignored,
    /// Go `*EditRange`.
    EditRange(EditRange),
}

/// `type EditRange struct`
pub struct EditRange {
    pub insert: Rc<RangeMarker>,
    pub replace: Rc<RangeMarker>,
}

/// `type CompletionsExpectedItemDefaults struct`
#[derive(Default)]
pub struct CompletionsExpectedItemDefaults {
    pub commit_characters: Option<Vec<String>>,
    pub edit_range: ExpectedCompletionEditRange,
}

/// `type CompletionsExpectedItem = any` — `string | *lsproto.CompletionItem`.
#[derive(Debug)]
pub enum CompletionsExpectedItem {
    Label(String),
    Item(ExpectedCompletionItem),
}

impl From<&str> for CompletionsExpectedItem {
    fn from(label: &str) -> Self {
        CompletionsExpectedItem::Label(label.to_string())
    }
}

impl From<String> for CompletionsExpectedItem {
    fn from(label: String) -> Self {
        CompletionsExpectedItem::Label(label)
    }
}

impl From<CompletionItem> for CompletionsExpectedItem {
    fn from(item: CompletionItem) -> Self {
        CompletionsExpectedItem::Item(ExpectedCompletionItem::from(item))
    }
}

/// PORT: Go places the `AnyTextEdits`/`NoTextEdits` sentinel pointers in
/// `CompletionItem.AdditionalTextEdits`; Rust has no pointer-identity
/// sentinels, so expected items wrap [CompletionItem] with an explicit
/// expectation for the additional text edits.
#[derive(Debug)]
pub struct ExpectedCompletionItem {
    pub item: CompletionItem,
    pub additional_text_edits: ExpectedTextEdits,
}

impl From<CompletionItem> for ExpectedCompletionItem {
    fn from(item: CompletionItem) -> Self {
        ExpectedCompletionItem {
            additional_text_edits: ExpectedTextEdits::Edits(item.additional_text_edits.clone()),
            item,
        }
    }
}

/// `ExpectedCompletionItem.AdditionalTextEdits` expectation.
#[derive(Debug)]
pub enum ExpectedTextEdits {
    /// Go `AnyTextEdits` — asserts non-empty `actual.AdditionalTextEdits`.
    Any,
    /// Go `NoTextEdits` — asserts `actual.AdditionalTextEdits` is empty.
    None,
    /// Compare with `cmp.Diff` equality.
    Edits(Option<Vec<TextEdit>>),
}

/// Go's `AnyTextEdits` sentinel.
pub const ANY_TEXT_EDITS: ExpectedTextEdits = ExpectedTextEdits::Any;
/// Go's `NoTextEdits` sentinel.
pub const NO_TEXT_EDITS: ExpectedTextEdits = ExpectedTextEdits::None;

/// `type CompletionsExpectedItems struct`
#[derive(Default)]
pub struct CompletionsExpectedItems {
    pub includes: Option<Vec<CompletionsExpectedItem>>,
    pub excludes: Option<Vec<String>>,
    pub exact: Option<Vec<CompletionsExpectedItem>>,
    pub unsorted: Option<Vec<CompletionsExpectedItem>>,
}

/// `type CompletionsExpectedCodeAction struct`
pub struct CompletionsExpectedCodeAction {
    pub name: String,
    pub source: String,
    pub description: String,
    pub new_file_content: String,
}

/// `type VerifyCompletionsResult struct` — Go returns closures bound to `f`;
/// the port returns the completion list and the methods take `f` back.
pub struct VerifyCompletionsResult {
    pub list: Option<CompletionList>,
}

impl VerifyCompletionsResult {
    /// `AndApplyCodeAction`
    pub fn and_apply_code_action(
        &self,
        f: &mut FourslashTest,
        expected_action: &CompletionsExpectedCodeAction,
    ) {
        let items: &[CompletionItem] = self
            .list
            .as_ref()
            .and_then(|l| l.items.as_deref())
            .unwrap_or(&[]);
        let item = items.iter().find(|item| {
            if item.label != expected_action.name {
                return false;
            }
            let Some(data) = &item.data else { return false };
            data.auto_import
                .as_ref()
                .is_some_and(|ai| ai.module_specifier == expected_action.source)
        });
        let Some(item) = item else {
            panic!(
                "Code action '{}' from source '{}' not found in completions.",
                expected_action.name, expected_action.source
            );
        };
        // Detail and AdditionalTextEdits for auto-import items are populated by
        // completionItem/resolve, not in the initial completion list.
        let item = f.resolve_completion_item(item);
        assert!(
            item.detail
                .as_deref()
                .is_some_and(|d| d.contains(&expected_action.description)),
            "Completion item detail does not contain expected description."
        );
        let edits = item.additional_text_edits.clone().unwrap_or_default();
        f.apply_text_edits(&edits);
        assert_eq!(
            f.get_script_info_or_panic(&f.active_filename.clone()).content,
            expected_action.new_file_content,
            "File content after applying code action '{}' did not match expected content.",
            expected_action.name
        );
    }

    /// `AndHasNoCodeAction`
    pub fn and_has_no_code_action(&self, unexpected_action: &CompletionsExpectedCodeAction) {
        let items: &[CompletionItem] = self
            .list
            .as_ref()
            .and_then(|l| l.items.as_deref())
            .unwrap_or(&[]);
        let item = items.iter().find(|item| {
            if item.label != unexpected_action.name {
                return false;
            }
            let Some(data) = &item.data else { return false };
            data.auto_import
                .as_ref()
                .is_some_and(|ai| ai.module_specifier == unexpected_action.source)
        });
        if item.is_some() {
            panic!(
                "Unexpected code action '{}' from source '{}' found in completions.",
                unexpected_action.name, unexpected_action.source
            );
        }
    }
}

/// `type MarkerInput = any` — `string | *Marker | []string | []*Marker`.
#[derive(Debug)]
pub enum MarkerInput {
    Name(String),
    Marker(Rc<Marker>),
    Names(Vec<String>),
    Markers(Vec<Rc<Marker>>),
}

impl From<&str> for MarkerInput {
    fn from(name: &str) -> Self {
        MarkerInput::Name(name.to_string())
    }
}

impl From<String> for MarkerInput {
    fn from(name: String) -> Self {
        MarkerInput::Name(name)
    }
}

impl From<Rc<Marker>> for MarkerInput {
    fn from(marker: Rc<Marker>) -> Self {
        MarkerInput::Marker(marker)
    }
}

impl From<&[&str]> for MarkerInput {
    fn from(names: &[&str]) -> Self {
        MarkerInput::Names(names.iter().map(|s| s.to_string()).collect())
    }
}

impl From<Vec<String>> for MarkerInput {
    fn from(names: Vec<String>) -> Self {
        MarkerInput::Names(names)
    }
}

impl From<Vec<Rc<Marker>>> for MarkerInput {
    fn from(markers: Vec<Rc<Marker>>) -> Self {
        MarkerInput::Markers(markers)
    }
}

impl FourslashTest {
    /// `VerifyCompletions`
    // !!! user preferences param
    // !!! completion context param
    pub fn verify_completions(
        &mut self,
        marker_input: impl Into<MarkerInput>,
        expected: Option<&CompletionsExpectedList>,
    ) -> VerifyCompletionsResult {
        let mut list = None;
        match marker_input.into() {
            MarkerInput::Name(marker) => {
                self.go_to_marker(&marker);
                list = self.verify_completions_worker(expected);
            }
            MarkerInput::Marker(marker) => {
                self.go_to_marker_impl(&(marker as Rc<dyn MarkerOrRange>));
                list = self.verify_completions_worker(expected);
            }
            MarkerInput::Names(names) => {
                for marker_name in names {
                    self.go_to_marker(&marker_name);
                    self.verify_completions_worker(expected);
                }
            }
            MarkerInput::Markers(markers) => {
                for marker in markers {
                    self.go_to_marker_impl(&(marker as Rc<dyn MarkerOrRange>));
                    self.verify_completions_worker(expected);
                }
            }
        }
        VerifyCompletionsResult { list }
    }

    /// `verifyCompletionsWorker`
    fn verify_completions_worker(
        &mut self,
        expected: Option<&CompletionsExpectedList>,
    ) -> Option<CompletionList> {
        let prefix = self.get_current_position_prefix();
        let list = self.get_completions(expected.and_then(|e| e.user_preferences.as_ref()));
        self.verify_completions_result(list.as_ref(), expected, &prefix);
        list
    }

    /// `GetCompletions`
    pub fn get_completions_public(
        &mut self,
        user_preferences: Option<&UserPreferences>,
    ) -> Option<CompletionList> {
        self.get_completions(user_preferences)
    }

    /// `VerifyJSDocCompletion`
    pub fn verify_js_doc_completion(
        &mut self,
        marker_input: impl Into<MarkerInput>,
        expected_offset: i32,
        expected_text: &str,
        generate_return_in_doc_template: Option<bool>,
    ) {
        self.go_to_marker_input(marker_input.into());

        let user_preferences = generate_return_in_doc_template.map(|b| {
            let mut prefs = lsutil::new_default_user_preferences();
            prefs.generate_return_in_doc_template = bool_to_tristate(b);
            prefs
        });

        let mut list = self.get_completions(user_preferences.as_ref());
        let mut item = find_js_doc_completion_item(list.as_ref());
        if item.is_none() {
            let insert_start = self.caret_offset();
            self.insert("/**");
            list = self.get_completions(user_preferences.as_ref());
            item = find_js_doc_completion_item(list.as_ref());
            self.edit_script_and_update_markers(
                self.active_filename.clone(),
                insert_start,
                insert_start + 3,
                "",
            );
            self.current_caret_position = {
                let script = self.get_script_info_or_panic(&self.active_filename);
                self.test_converters()
                    .position_to_line_and_character(script, insert_start)
            };
        }
        let Some(list) = &list else {
            panic!("{}Expected JSDoc completion, got nil completion list.", self.get_current_position_prefix());
        };
        let Some(item) = item else {
            panic!("{}Expected JSDoc completion item, got {:?}.", self.get_current_position_prefix(), list.items);
        };
        let Some(text_edit) = &item.text_edit else {
            panic!("{}Expected JSDoc completion to have insert/replace edit, got {:?}.", self.get_current_position_prefix(), item.text_edit);
        };
        let Some(insert_replace) = &text_edit.insert_replace_edit else {
            panic!("{}Expected JSDoc completion to have insert/replace edit, got {:?}.", self.get_current_position_prefix(), item.text_edit);
        };
        assert_eq!(
            insert_replace.new_text, expected_text,
            "{}", self.get_current_position_prefix()
        );
        let _ = expected_offset; // The completion path uses snippet placeholders for caret placement.
    }

    /// `VerifyNoJSDocCompletion`
    pub fn verify_no_js_doc_completion(&mut self, marker_input: impl Into<MarkerInput>) {
        self.go_to_marker_input(marker_input.into());

        let mut list = self.get_completions(None);
        if find_js_doc_completion_item(list.as_ref()).is_some() {
            panic!("{}Did not expect JSDoc completion item.", self.get_current_position_prefix());
        }

        let insert_start = self.caret_offset();
        self.insert("/**");
        list = self.get_completions(None);
        let item = find_js_doc_completion_item(list.as_ref());
        self.edit_script_and_update_markers(
            self.active_filename.clone(),
            insert_start,
            insert_start + 3,
            "",
        );
        self.current_caret_position = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            self.test_converters()
                .position_to_line_and_character(script, insert_start)
        };
        if item.is_some() {
            panic!("{}Did not expect JSDoc completion item.", self.get_current_position_prefix());
        }
    }

    /// `goToMarkerInput`
    fn go_to_marker_input(&mut self, marker_input: MarkerInput) {
        match marker_input {
            MarkerInput::Name(marker) => self.go_to_marker(&marker),
            MarkerInput::Marker(marker) => {
                self.go_to_marker_impl(&(marker as Rc<dyn MarkerOrRange>))
            }
            _ => panic!("Invalid marker input type. Expected string or *Marker."),
        }
    }

    /// `getCompletions`
    pub(crate) fn get_completions(
        &mut self,
        user_preferences: Option<&UserPreferences>,
    ) -> Option<CompletionList> {
        let params = CompletionParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            context: Some(CompletionContext::default()),
            ..Default::default()
        };
        let mut result;
        if let Some(user_preferences) = user_preferences {
            let mut preferences = user_preferences.clone();
            preferences.format_code_settings =
                self.user_preferences.as_ref().format_code_settings.clone();
            let original = self.configure_with_reset(preferences);
            result = self.send_request(&TEXT_DOCUMENT_COMPLETION_INFO, params);
            self.configure(original);
        } else {
            result = self.send_request(&TEXT_DOCUMENT_COMPLETION_INFO, params);
        }
        // For performance, the server may return unsorted completion lists.
        // The client is expected to sort them by SortText and then by Label.
        // We are the client here.
        if let Some(list) = &mut result.list {
            // PORT: `ls.CompareCompletionEntries` is pub(crate) in tsc-ls;
            // this is its comparator verbatim.
            if let Some(items) = &mut list.items {
                items.sort_by(|a, b| {
                let ord = compare_strings_case_insensitive_then_sensitive(
                    a.sort_text.as_deref().unwrap_or("").as_bytes(),
                    b.sort_text.as_deref().unwrap_or("").as_bytes(),
                );
                if ord == tsc_stringutil::COMPARISON_EQUAL {
                    compare_strings_case_insensitive_then_sensitive(
                        a.label.as_bytes(),
                        b.label.as_bytes(),
                    )
                    .cmp(&0)
                } else {
                    ord.cmp(&0)
                }
                });
            }
        }
        result.list
    }

    /// `verifyCompletionsResult`
    fn verify_completions_result(
        &mut self,
        actual: Option<&CompletionList>,
        expected: Option<&CompletionsExpectedList>,
        prefix: &str,
    ) {
        let Some(actual) = actual else {
            if !is_empty_expected_list(expected) {
                panic!("{prefix}Expected completion list but got nil.");
            }
            return;
        };
        let Some(expected) = expected else {
            if actual.items.as_ref().is_none_or(|i| i.is_empty()) {
                return;
            }
            panic!("{prefix}Expected nil completion list but got non-nil: {actual:?}");
        };
        assert_eq!(
            actual.is_incomplete, expected.is_incomplete,
            "{prefix}IsIncomplete mismatch"
        );
        verify_completions_item_defaults(
            actual.item_defaults.as_ref(),
            expected.item_defaults.as_ref(),
            &format!("{prefix}ItemDefaults mismatch: "),
        );
        self.verify_completions_items(
            prefix,
            actual.items.as_deref().unwrap_or(&[]),
            expected.items.as_ref(),
        );
    }

    /// `verifyCompletionsItems`
    fn verify_completions_items(
        &mut self,
        prefix: &str,
        actual: &[CompletionItem],
        expected: Option<&CompletionsExpectedItems>,
    ) {
        let Some(expected) = expected else {
            return;
        };
        if let Some(exact) = &expected.exact {
            if expected.includes.is_some() {
                panic!("{prefix}Expected exact completion list but also specified 'includes'.");
            }
            if expected.excludes.is_some() {
                panic!("{prefix}Expected exact completion list but also specified 'excludes'.");
            }
            if expected.unsorted.is_some() {
                panic!("{prefix}Expected exact completion list but also specified 'unsorted'.");
            }
            if actual.len() != exact.len() {
                panic!(
                    "{prefix}Expected {} exact completion items but got {}.",
                    exact.len(),
                    actual.len()
                );
            }
            if !actual.is_empty() {
                self.verify_completions_are_exactly(prefix, actual, exact);
            }
            return;
        }
        let mut name_to_actual_items: BTreeMap<String, Vec<&CompletionItem>> = BTreeMap::new();
        for item in actual {
            name_to_actual_items
                .entry(item.label.clone())
                .or_default()
                .push(item);
        }
        if let Some(unsorted) = &expected.unsorted {
            if expected.includes.is_some() {
                panic!("{prefix}Expected unsorted completion list but also specified 'includes'.");
            }
            if expected.excludes.is_some() {
                panic!("{prefix}Expected unsorted completion list but also specified 'excludes'.");
            }
            for item in unsorted {
                match item {
                    CompletionsExpectedItem::Label(label) => {
                        if name_to_actual_items.remove(label).is_none() {
                            panic!("{prefix}Label '{label}' not found in actual items.");
                        }
                    }
                    CompletionsExpectedItem::Item(item) => {
                        let Some(actual_items) = name_to_actual_items.get(&item.item.label) else {
                            panic!("{prefix}Label '{}' not found in actual items.", item.item.label);
                        };
                        let mut mismatch_prefix = if actual_items.len() > 1 {
                            format!("{prefix}No completion item match for label {} (multiple candidates found): ", item.item.label)
                        } else {
                            format!("{prefix}Includes completion item mismatch for label {}: ", item.item.label)
                        };
                        let item_index = actual_items.iter().position(|actual_item| {
                            match self.verify_completion_item(prefix, actual_item, item) {
                                Ok(()) => true,
                                Err(err) => {
                                    mismatch_prefix += &format!("\n    {err}");
                                    false
                                }
                            }
                        });
                        let Some(item_index) = item_index else {
                            panic!("{mismatch_prefix}");
                        };
                        let actual_items = name_to_actual_items.get_mut(&item.item.label).unwrap();
                        if actual_items.len() == 1 {
                            name_to_actual_items.remove(&item.item.label);
                        } else {
                            actual_items.remove(item_index);
                        }
                    }
                }
            }
            if unsorted.len() != actual.len() {
                let unmatched: Vec<&String> = name_to_actual_items.keys().collect();
                panic!(
                    "{prefix}Additional completions found but not included in 'unsorted': {}",
                    unmatched
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                );
            }
            return;
        }
        if let Some(includes) = &expected.includes {
            for item in includes {
                match item {
                    CompletionsExpectedItem::Label(label) => {
                        if !name_to_actual_items.contains_key(label) {
                            panic!("{prefix}Label '{label}' not found in actual items.");
                        }
                    }
                    CompletionsExpectedItem::Item(item) => {
                        let Some(actual_items) = name_to_actual_items.get(&item.item.label) else {
                            panic!("{prefix}Label '{}' not found in actual items.", item.item.label);
                        };
                        let mut mismatch_prefix = if actual_items.len() > 1 {
                            format!("{prefix}No completion item match for label {} (multiple candidates found): ", item.item.label)
                        } else {
                            format!("{prefix}Includes completion item mismatch for label {}: ", item.item.label)
                        };
                        let item_index = actual_items.iter().position(|actual_item| {
                            match self.verify_completion_item(prefix, actual_item, item) {
                                Ok(()) => true,
                                Err(err) => {
                                    mismatch_prefix += &format!("\n    {err}");
                                    false
                                }
                            }
                        });
                        let Some(item_index) = item_index else {
                            panic!("{mismatch_prefix}");
                        };
                        // delete previous entries since we verify entries in order
                        let actual_items = name_to_actual_items.get_mut(&item.item.label).unwrap();
                        if actual_items.len() == 1 || item_index == actual_items.len() - 1 {
                            name_to_actual_items.remove(&item.item.label);
                        } else {
                            actual_items.drain(..item_index);
                        }
                    }
                }
            }
        }
        if let Some(excludes) = &expected.excludes {
            for exclude in excludes {
                if name_to_actual_items.contains_key(exclude) {
                    panic!("{prefix}Label '{exclude}' should not be in actual items but was found.");
                }
            }
        }
    }

    /// `verifyCompletionsAreExactly`
    fn verify_completions_are_exactly(
        &mut self,
        prefix: &str,
        actual: &[CompletionItem],
        expected: &[CompletionsExpectedItem],
    ) {
        let label_mismatch_prefix = format!("{prefix}Label mismatch");
        for (i, actual_item) in actual.iter().enumerate() {
            match &expected[i] {
                CompletionsExpectedItem::Label(label) => {
                    assert_deep_equal(&actual_item.label, label, &label_mismatch_prefix);
                }
                CompletionsExpectedItem::Item(expected_item) => {
                    assert_deep_equal(&actual_item.label, &expected_item.item.label, &label_mismatch_prefix);
                    if let Err(err) = self.verify_completion_item(
                        &format!("{prefix}Completion item mismatch for label {}", actual_item.label),
                        actual_item,
                        expected_item,
                    ) {
                        panic!("{}:\n{err}", format!("{prefix}Completion item mismatch for label {}", actual_item.label));
                    }
                }
            }
        }
    }

    /// `verifyCompletionItem` — returns Err(message) if not matched.
    fn verify_completion_item(
        &mut self,
        prefix: &str,
        actual: &CompletionItem,
        expected: &ExpectedCompletionItem,
    ) -> Result<(), String> {
        let _ = prefix;
        let actual_auto_import_fix = actual.data.as_ref().and_then(|d| d.auto_import.as_ref());
        let expected_auto_import_fix = expected
            .item
            .data
            .as_ref()
            .and_then(|d| d.auto_import.as_ref());
        if actual_auto_import_fix.is_some() != expected_auto_import_fix.is_some() {
            return Err("Mismatch in auto-import data presence".to_string());
        }

        let mut actual_owned;
        let mut actual = actual;
        if expected.item.detail.is_some()
            || expected.item.documentation.is_some()
            || actual_auto_import_fix.is_some()
        {
            actual_owned = self.resolve_completion_item(actual);
            actual = &actual_owned;
        }

        if let Some(actual_fix) = actual_auto_import_fix {
            if let Err(diff) = completion_item_diff(actual, &expected.item, true) {
                return Err(diff);
            }
            match &expected.additional_text_edits {
                ExpectedTextEdits::Any => {
                    if !actual
                        .additional_text_edits
                        .as_ref()
                        .is_some_and(|e| !e.is_empty())
                    {
                        return Err(
                            "Expected non-nil AdditionalTextEdits for auto-import completion item"
                                .to_string(),
                        );
                    }
                }
                ExpectedTextEdits::None => {
                    if actual
                        .additional_text_edits
                        .as_ref()
                        .is_some_and(|e| !e.is_empty())
                    {
                        return Err(
                            "Expected no AdditionalTextEdits for auto-import completion item"
                                .to_string(),
                        );
                    }
                }
                ExpectedTextEdits::Edits(_) => {}
            }
            if let Some(expected_label_details) = &expected.item.label_details {
                if actual.label_details.as_ref() != Some(expected_label_details) {
                    return Err(format!(
                        "LabelDetailsMismatch:\nactual:   {:?}\nexpected: {:?}",
                        actual.label_details, expected_label_details
                    ));
                }
            }
            let expected_fix = expected_auto_import_fix.unwrap();
            if actual_fix.module_specifier != expected_fix.module_specifier {
                return Err("ModuleSpecifier mismatch".to_string());
            }
        } else {
            if let Err(diff) = completion_item_diff(actual, &expected.item, false) {
                return Err(diff);
            }
            match &expected.additional_text_edits {
                ExpectedTextEdits::Any => {
                    if !actual
                        .additional_text_edits
                        .as_ref()
                        .is_some_and(|e| !e.is_empty())
                    {
                        return Err(
                            "Expected non-empty AdditionalTextEdits for completion item".to_string(),
                        );
                    }
                }
                ExpectedTextEdits::Edits(edits) => {
                    if actual.additional_text_edits.as_ref() != edits.as_ref() {
                        return Err(format!(
                            "AdditionalTextEdits mismatch:\nactual:   {:?}\nexpected: {:?}",
                            actual.additional_text_edits, edits
                        ));
                    }
                }
                ExpectedTextEdits::None => {
                    if actual
                        .additional_text_edits
                        .as_ref()
                        .is_some_and(|e| !e.is_empty())
                    {
                        return Err(
                            "Expected no AdditionalTextEdits for completion item".to_string()
                        );
                    }
                }
            }
        }

        if let Some(filter_text) = &expected.item.filter_text {
            if actual.filter_text.as_ref() != Some(filter_text) {
                return Err(format!(
                    "FilterText mismatch:\nactual:   {:?}\nexpected: {:?}",
                    actual.filter_text, filter_text
                ));
            }
        }
        if let Some(kind) = &expected.item.kind {
            if actual.kind.as_ref() != Some(kind) {
                return Err(format!(
                    "Kind mismatch:\nactual:   {:?}\nexpected: {:?}",
                    actual.kind, kind
                ));
            }
        }
        // `core.OrElse(expected.SortText, new(string(ls.SortTextLocationPriority)))`
        let expected_sort_text = expected
            .item
            .sort_text
            .clone()
            .unwrap_or_else(|| SORT_TEXT_LOCATION_PRIORITY.to_string());
        if actual.sort_text.as_deref() != Some(expected_sort_text.as_str()) {
            return Err(format!(
                "SortText mismatch:\nactual:   {:?}\nexpected: {:?}",
                actual.sort_text, expected_sort_text
            ));
        }

        Ok(())
    }

    /// `ResolveCompletionItem` — Go returns the (nil-able) resolve response;
    /// callers dereference it unconditionally, so nil becomes a panic.
    pub fn resolve_completion_item(&mut self, item: &CompletionItem) -> CompletionItem {
        self.send_request(&COMPLETION_ITEM_RESOLVE_INFO, item.clone())
            .unwrap_or_else(|| panic!("completionItem/resolve returned nil"))
    }
}

/// `isEmptyExpectedList`
fn is_empty_expected_list(expected: Option<&CompletionsExpectedList>) -> bool {
    let Some(expected) = expected else {
        return true;
    };
    match &expected.items {
        None => true,
        Some(items) => {
            items.exact.as_ref().is_none_or(|v| v.is_empty())
                && items.includes.as_ref().is_none_or(|v| v.is_empty())
                && items.excludes.as_ref().is_none_or(|v| v.is_empty())
                && items.unsorted.as_ref().is_none_or(|v| v.is_empty())
        }
    }
}

/// `verifyCompletionsItemDefaults`
fn verify_completions_item_defaults(
    actual: Option<&CompletionItemDefaults>,
    expected: Option<&CompletionsExpectedItemDefaults>,
    prefix: &str,
) {
    let Some(actual) = actual else {
        if expected.is_none() {
            return;
        }
        panic!("{prefix}Expected non-nil completion item defaults but got nil");
    };
    let Some(expected) = expected else {
        panic!("{prefix}Expected nil completion item defaults but got non-nil: {actual:?}");
    };
    assert_deep_equal(
        &actual.commit_characters,
        &expected.commit_characters,
        &format!("{prefix}CommitCharacters mismatch:"),
    );
    match &expected.edit_range {
        ExpectedCompletionEditRange::EditRange(edit_range) => {
            let Some(actual_edit_range) = &actual.edit_range else {
                panic!("{prefix}Expected non-nil EditRange but got nil");
            };
            let expected_insert = edit_range.insert.ls_range.clone();
            let expected_replace = edit_range.replace.ls_range.clone();
            let expected_union = RangeOrEditRangeWithInsertReplace {
                edit_range_with_insert_replace: Some(EditRangeWithInsertReplace {
                    insert: expected_insert,
                    replace: expected_replace,
                }),
                ..Default::default()
            };
            assert_deep_equal(actual_edit_range, &expected_union, &format!("{prefix}EditRange mismatch:"));
        }
        ExpectedCompletionEditRange::None => {
            if actual.edit_range.is_some() {
                panic!("{prefix}Expected nil EditRange but got non-nil: {:?}", actual.edit_range);
            }
        }
        ExpectedCompletionEditRange::Ignored => {
            // The edit range is intentionally ignored.
        }
    }
}

/// `findJSDocCompletionItem`
fn find_js_doc_completion_item(list: Option<&CompletionList>) -> Option<CompletionItem> {
    list.and_then(|list| {
        find(list.items.as_deref().unwrap_or(&[]), |item| {
            item.label == "/** */"
        })
    })
}

/// `SORT_TEXT_LOCATION_PRIORITY` — `ls.SortTextLocationPriority` (pub(crate)
/// in tsc-ls).
pub(crate) const SORT_TEXT_LOCATION_PRIORITY: &str = "11";
/// `ls.SortTextAutoImportSuggestions` (pub(crate) in tsc-ls).
pub(crate) const SORT_TEXT_AUTO_IMPORT_SUGGESTIONS: &str = "16";

/// `completion_item_diff` — `cmp.Diff(actual, expected, completionIgnoreOpts)`
/// (or `autoImportIgnoreOpts` when `auto_import` is set).
fn completion_item_diff(
    actual: &CompletionItem,
    expected: &CompletionItem,
    auto_import: bool,
) -> Result<(), String> {
    // Compare every field except the ignored ones.
    // completionIgnoreOpts: ".Kind", ".SortText", ".FilterText", ".Data", ".AdditionalTextEdits"
    // autoImportIgnoreOpts: + ".LabelDetails", ".Detail"
    macro_rules! check {
        ($name:literal, $a:expr, $e:expr) => {
            if $a != $e {
                return Err(format!(
                    "{} mismatch:\nactual:   {:?}\nexpected: {:?}",
                    $name, $a, $e
                ));
            }
        };
    }
    check!("Label", &actual.label, &expected.label);
    check!("Documentation", &actual.documentation, &expected.documentation);
    check!("Deprecated", &actual.deprecated, &expected.deprecated);
    check!("Preselect", &actual.preselect, &expected.preselect);
    check!("InsertText", &actual.insert_text, &expected.insert_text);
    check!("InsertTextFormat", &actual.insert_text_format, &expected.insert_text_format);
    check!("InsertTextMode", &actual.insert_text_mode, &expected.insert_text_mode);
    check!("TextEdit", &actual.text_edit, &expected.text_edit);
    check!("CommitCharacters", &actual.commit_characters, &expected.commit_characters);
    check!("Command", &actual.command, &expected.command);
    check!("Tags", &actual.tags, &expected.tags);
    if !auto_import {
        check!("LabelDetails", &actual.label_details, &expected.label_details);
        check!("Detail", &actual.detail, &expected.detail);
    }
    Ok(())
}

// --- code fixes ------------------------------------------------------------

/// `VerifyCodeFixOptions` are the options for [FourslashTest::verify_code_fix].
#[derive(Default)]
pub struct VerifyCodeFixOptions {
    pub description: String,
    pub new_file_content: String,
    pub new_range_content: String,
    pub index: usize,
    pub apply_changes: bool,
    pub user_preferences: Option<UserPreferences>,
}

/// `VerifyCodeFixAllOptions` are the options for [FourslashTest::verify_code_fix_all].
#[derive(Default)]
pub struct VerifyCodeFixAllOptions {
    pub fix_id: String,
    pub new_file_content: String,
}

impl FourslashTest {
    /// `VerifyCodeFix` verifies that applying a code fix produces the expected file content.
    pub fn verify_code_fix(&mut self, options: &VerifyCodeFixOptions) {
        if let Some(prefs) = &options.user_preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_code_fix_impl(options);
            self.configure(original);
            return;
        }
        self.verify_code_fix_impl(options);
    }

    fn verify_code_fix_impl(&mut self, options: &VerifyCodeFixOptions) {
        let actions = self.get_code_fix_actions(&[]);
        if actions.is_empty() {
            panic!("No code fixes returned.");
        }
        if options.index >= actions.len() {
            panic!("Code fix index {} out of range (got {} fixes)", options.index, actions.len());
        }

        let mut matching_action = &actions[options.index];
        if matching_action.title != options.description {
            match actions.iter().find(|a| a.title == options.description) {
                Some(a) => matching_action = a,
                None => {
                    let titles: Vec<&str> = actions.iter().map(|a| a.title.as_str()).collect();
                    panic!(
                        "No code fix with description {:?} at index {} found. Available fixes: {:?}",
                        options.description, options.index, titles
                    );
                }
            }
        }

        let original_content = self
            .get_script_info_or_panic(&self.active_filename.clone())
            .content
            .clone();
        let mut expected_content = options.new_file_content.clone();
        if !options.new_range_content.is_empty() {
            let mut selection = self.get_selection();
            if selection.pos() == selection.end() {
                let ranges = self.get_ranges_in_file(&self.active_filename);
                if ranges.is_empty() {
                    panic!("Expected a selected range or fourslash range for NewRangeContent verification.");
                }
                selection = ranges[0].as_ref().range;
            }
            expected_content = format!(
                "{}{}{}",
                &original_content[..selection.pos() as usize],
                options.new_range_content,
                &original_content[selection.end() as usize..]
            );
        }

        if options.apply_changes {
            if let Some(changes) = matching_action
                .edit
                .as_ref()
                .and_then(|e| e.changes.as_ref())
            {
                let expected_uri = lsconv::file_name_to_document_uri(&self.active_filename);
                for (uri, edits) in changes {
                    if *uri != expected_uri {
                        panic!("Code fix returned edits for unexpected URI {uri:?} (expected {expected_uri:?})");
                    }
                    self.apply_text_edits(edits);
                }
            }
            let actual = &self
                .get_script_info_or_panic(&self.active_filename.clone())
                .content;
            assert_eq!(
                expected_content, *actual,
                "File content after applying code fix did not match expected content."
            );
        } else {
            let mut actual = self
                .get_script_info_or_panic(&self.active_filename.clone())
                .content
                .clone();
            if let Some(changes) = matching_action
                .edit
                .as_ref()
                .and_then(|e| e.changes.as_ref())
            {
                let expected_uri = lsconv::file_name_to_document_uri(&self.active_filename);
                for (uri, edits) in changes {
                    if *uri != expected_uri {
                        panic!("Code fix returned edits for unexpected URI {uri:?} (expected {expected_uri:?})");
                    }
                    actual = self.apply_edits_to_content(&actual, edits);
                }
            }
            assert_eq!(
                expected_content, actual,
                "File content after applying code fix did not match expected content."
            );
        }
    }

    /// `VerifyRangeAfterCodeFix`
    pub fn verify_range_after_code_fix(
        &mut self,
        expected_text: &str,
        include_whitespace: bool,
        error_code: i32,
        index: usize,
    ) {
        let actions = self.get_code_fix_actions(&[error_code]);
        if actions.is_empty() {
            panic!("No code fixes returned.");
        }
        if index >= actions.len() {
            panic!("Code fix index {index} out of range (got {} fixes)", actions.len());
        }

        let action = actions[index].clone();
        let ranges = self.get_ranges_in_file(&self.active_filename);
        if ranges.len() != 1 {
            panic!("Expected exactly one range in {:?}, got {}.", self.active_filename, ranges.len());
        }

        let edits = self.get_code_action_edits_for_active_file(&action);
        let updated_range = self.update_text_range_for_text_edits(ranges[0].as_ref().range, &edits);
        assert_valid_text_range(
            updated_range,
            &format!(
                "Code fix {:?} replaced part of the expected range; unable to compute rangeAfterCodeFix result.",
                action.title
            ),
        );

        self.apply_text_edits(&edits);
        let actual_content = &self
            .get_script_info_or_panic(&self.active_filename.clone())
            .content;
        let actual_text = &actual_content[updated_range.pos() as usize..updated_range.end() as usize];

        if include_whitespace {
            assert_eq!(
                expected_text, actual_text,
                "Range content after applying code fix did not match expected content."
            );
            return;
        }

        assert_eq!(
            remove_whitespace(expected_text),
            remove_whitespace(actual_text),
            "Range content after applying code fix did not match expected content."
        );
    }

    /// `getCodeActionEditsForActiveFile`
    fn get_code_action_edits_for_active_file(&self, action: &CodeAction) -> Vec<TextEdit> {
        let Some(changes) = action.edit.as_ref().and_then(|e| e.changes.as_ref()) else {
            panic!("Code fix {:?} did not return text edits.", action.title);
        };
        if changes.len() != 1 {
            panic!(
                "Code fix {:?} returned edits for multiple files; rangeAfterCodeFix expects only the active file.",
                action.title
            );
        }
        let uri = lsconv::file_name_to_document_uri(&self.active_filename);
        match changes.get(&uri) {
            Some(edits) => edits.clone(),
            None => panic!("Code fix {:?} did not return edits for active file {}.", action.title, self.active_filename.as_string()),
        }
    }

    /// `VerifyCodeFixAvailable` verifies that code fixes with the given descriptions are available.
    pub fn verify_code_fix_available(&mut self, expected_descriptions: Option<&[String]>) {
        let actions = self.get_code_fix_actions(&[]);
        let Some(expected_descriptions) = expected_descriptions else {
            if actions.is_empty() {
                panic!("Expected code fixes to be available, but got none.");
            }
            return;
        };

        if expected_descriptions.is_empty() {
            self.verify_code_fix_not_available(&[]);
            return;
        }

        for expected in expected_descriptions {
            if !actions.iter().any(|a| a.title == *expected) {
                let titles: Vec<&str> = actions.iter().map(|a| a.title.as_str()).collect();
                panic!(
                    "Expected code fix with description {expected:?} not found. Available fixes: {titles:?}"
                );
            }
        }
    }

    /// `VerifyCodeFixNotAvailable`
    pub fn verify_code_fix_not_available(&mut self, expected: &[String]) {
        let actions = self.get_code_fix_actions(&[]);
        if expected.is_empty() {
            if actions.is_empty() {
                return;
            }
            let titles: Vec<&str> = actions.iter().map(|a| a.title.as_str()).collect();
            panic!("Expected no code fixes, but got: {titles:?}");
        }
        for title in expected {
            if actions.iter().any(|a| a.title == *title) {
                panic!("Expected code fix with description {title:?} not to be available.");
            }
        }
    }

    /// `VerifyCodeFixAvailableExact` verifies that the exact set of code fix
    /// descriptions matches (exact count match, no additional fixes).
    pub fn verify_code_fix_available_exact(&mut self, expected_descriptions: &[String]) {
        let actions = self.get_code_fix_actions(&[]);
        if actions.len() != expected_descriptions.len() {
            let titles: Vec<&str> = actions.iter().map(|a| a.title.as_str()).collect();
            panic!(
                "Expected exactly {} code fixes, but got {}. Available fixes: {:?}",
                expected_descriptions.len(),
                actions.len(),
                titles
            );
        }
        for expected in expected_descriptions {
            if !actions.iter().any(|a| a.title == *expected) {
                let titles: Vec<&str> = actions.iter().map(|a| a.title.as_str()).collect();
                panic!(
                    "Expected code fix with description {expected:?} not found. Available fixes: {titles:?}"
                );
            }
        }
    }

    /// `VerifyCodeFixAll` verifies that applying all code fixes with the given
    /// fixId produces the expected file content.
    pub fn verify_code_fix_all(&mut self, options: &VerifyCodeFixAllOptions) {
        let actions = self.get_all_quick_fix_actions(&[]);
        if actions.is_empty() {
            panic!("No code fixes available for fixId {:?}", options.fix_id);
        }

        // Find fix-all actions. The server returns these as quickfix entries with titles like
        // "Add all missing imports" when multiple diagnostics match the same provider.
        // We look for actions that are NOT single-diagnostic fixes (i.e., have no Diagnostics attached).
        let fix_all_candidates: Vec<&CodeAction> = actions
            .iter()
            .filter(|a| a.diagnostics.as_ref().is_none_or(|d| d.is_empty()))
            .collect();

        let fix_all_action = if fix_all_candidates.len() == 1 {
            Some(fix_all_candidates[0])
        } else {
            // If there are multiple fix-all candidates, match by FixID in the title.
            fix_all_candidates
                .iter()
                .find(|a| {
                    a.title
                        .to_lowercase()
                        .contains(&options.fix_id.to_lowercase())
                })
                .copied()
        };

        let Some(fix_all_action) = fix_all_action else {
            let titles: Vec<&str> = actions.iter().map(|a| a.title.as_str()).collect();
            panic!(
                "No fix-all code action found for fixId {:?}. Available fixes: {:?}",
                options.fix_id, titles
            );
        };

        if let Some(changes) = fix_all_action.edit.as_ref().and_then(|e| e.changes.as_ref()) {
            let expected_uri = lsconv::file_name_to_document_uri(&self.active_filename);
            for (uri, edits) in changes {
                if *uri != expected_uri {
                    panic!("Fix-all code action returned edits for unexpected URI {uri:?} (expected {expected_uri:?})");
                }
                self.apply_text_edits(edits);
            }
        }

        let actual = &self
            .get_script_info_or_panic(&self.active_filename.clone())
            .content;
        assert_eq!(
            options.new_file_content, *actual,
            "File content after applying all code fixes did not match expected content."
        );
    }

    /// `VerifySourceFixAll` verifies that requesting a source.fixAll code
    /// action produces the expected file content.
    pub fn verify_source_fix_all(&mut self, expected_content: &str) {
        let only = vec![CodeActionKind::SourceFixAll];
        let params = CodeActionParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            range: Range {
                start: self.current_caret_position,
                end: self.current_caret_position,
            },
            context: Some(CodeActionContext {
                diagnostics: Some(vec![]),
                only: Some(only),
                ..Default::default()
            }),
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_CODE_ACTION_INFO, params);

        let Some(items) = &result.command_or_code_action_array else {
            panic!("No source.fixAll code actions returned");
        };

        let selected = items.iter().find_map(|item| {
            item.code_action.as_ref().filter(|ca| {
                ca.kind.as_ref() == Some(&CodeActionKind::SOURCE_FIX_ALL_TS)
            })
        });
        let Some(selected) = selected else {
            panic!("No source.fixAll code action found");
        };
        if let Some(changes) = selected.edit.as_ref().and_then(|e| e.changes.as_ref()) {
            let expected_uri = lsconv::file_name_to_document_uri(&self.active_filename);
            for (uri, edits) in changes {
                if *uri != expected_uri {
                    panic!("source.fixAll returned edits for unexpected URI {uri:?} (expected {expected_uri:?})");
                }
                self.apply_text_edits(edits);
            }
        }

        let actual = &self
            .get_script_info_or_panic(&self.active_filename.clone())
            .content;
        assert_eq!(
            expected_content, *actual,
            "File content after source.fixAll did not match expected content."
        );
    }

    /// `getCodeFixActions` — per-diagnostic quick fix code actions, excluding fix-all entries.
    fn get_code_fix_actions(&mut self, error_code: &[i32]) -> Vec<CodeAction> {
        let all = self.get_all_quick_fix_actions(error_code);
        // Filter to only per-diagnostic fixes (those with diagnostics attached)
        all.into_iter()
            .filter(|a| a.diagnostics.as_ref().is_some_and(|d| !d.is_empty()))
            .collect()
    }

    /// `getAllQuickFixActions` — all quick fix code actions including fix-all entries.
    fn get_all_quick_fix_actions(&mut self, error_code: &[i32]) -> Vec<CodeAction> {
        let diag_params = DocumentDiagnosticParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };
        let diag_result = self.send_request(&TEXT_DOCUMENT_DIAGNOSTIC_INFO, diag_params);

        let diagnostics: Vec<Diagnostic> = diag_result
            .full_document_diagnostic_report
            .and_then(|r| r.items)
            .unwrap_or_default();

        if diagnostics.is_empty() {
            return vec![];
        }

        let Some(diagnostic) = select_code_fix_diagnostic(
            &diagnostics,
            error_code.first().copied().unwrap_or(0),
        ) else {
            return vec![];
        };

        let params = CodeActionParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            range: diagnostic.range.clone(),
            context: Some(CodeActionContext {
                diagnostics: Some(diagnostics),
                ..Default::default()
            }),
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_CODE_ACTION_INFO, params);

        result
            .command_or_code_action_array
            .unwrap_or_default()
            .into_iter()
            .filter_map(|item| {
                item.code_action
                    .filter(|ca| ca.kind.as_ref() == Some(&CodeActionKind::QuickFix))
            })
            .collect()
    }

    /// `updateTextRangeForTextEdits`
    fn update_text_range_for_text_edits(&self, text_range: TextRange, edits: &[TextEdit]) -> TextRange {
        let script = self.get_script_info_or_panic(&self.active_filename.clone());
        let converters = self.test_converters();
        let mut spans: Vec<crate::fourslash::TextEditSpan> = edits
            .iter()
            .map(|edit| crate::fourslash::TextEditSpan {
                start: converters.line_and_character_to_position(script, edit.range.start),
                end: converters.line_and_character_to_position(script, edit.range.end),
                length: edit.new_text.len() as i32,
            })
            .collect();
        spans.sort_by(|a, b| a.start.cmp(&b.start));

        let mut pos = text_range.pos();
        let mut end = text_range.end();
        for i in 0..spans.len() {
            let edit = spans[i].clone();
            pos = update_position_for_text_edit(pos, edit.start, edit.end, edit.length);
            end = update_position_for_text_edit(end, edit.start, edit.end, edit.length);

            let delta = edit.length - (edit.end - edit.start);
            for j in i + 1..spans.len() {
                if spans[j].start >= edit.start {
                    spans[j].start += delta;
                    spans[j].end += delta;
                }
            }
        }
        TextRange::new(pos, end)
    }

    /// `applyEditsToContent` applies text edits to a content string without mutating the file.
    fn apply_edits_to_content(&self, content: &str, edits: &[TextEdit]) -> String {
        let script = self.get_script_info_or_panic(&self.active_filename.clone());
        let converters = self.test_converters();
        let mut edits = edits.to_vec();
        edits.sort_by(|a, b| {
            let a_start = converters.line_and_character_to_position(script, a.range.start);
            let b_start = converters.line_and_character_to_position(script, b.range.start);
            a_start.cmp(&b_start)
        });
        let mut content = content.to_string();
        for edit in edits.iter().rev() {
            let start = converters.line_and_character_to_position(script, edit.range.start) as usize;
            let end = converters.line_and_character_to_position(script, edit.range.end) as usize;
            content = format!("{}{}{}", &content[..start], edit.new_text, &content[end..]);
        }
        content
    }

    /// `VerifyOrganizeImports`
    pub fn verify_organize_imports(
        &mut self,
        expected_content: &str,
        code_action_kind: CodeActionKind,
        preferences: Option<&UserPreferences>,
    ) {
        self.verify_organize_imports_impl(
            expected_content,
            code_action_kind.clone(),
            code_action_kind,
            preferences,
        );
    }

    /// `VerifyOrganizeImportsWithRequestKind`
    pub fn verify_organize_imports_with_request_kind(
        &mut self,
        expected_content: &str,
        requested_kind: CodeActionKind,
        expected_kind: CodeActionKind,
        preferences: Option<&UserPreferences>,
    ) {
        self.verify_organize_imports_impl(
            expected_content,
            requested_kind,
            expected_kind,
            preferences,
        );
    }

    /// `verifyOrganizeImports`
    fn verify_organize_imports_impl(
        &mut self,
        expected_content: &str,
        requested_kind: CodeActionKind,
        expected_kind: CodeActionKind,
        preferences: Option<&UserPreferences>,
    ) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_organize_imports_worker(expected_content, requested_kind, expected_kind);
            self.configure(original);
            return;
        }
        self.verify_organize_imports_worker(expected_content, requested_kind, expected_kind);
    }

    fn verify_organize_imports_worker(
        &mut self,
        expected_content: &str,
        requested_kind: CodeActionKind,
        expected_kind: CodeActionKind,
    ) {
        let file_name = self.active_filename.clone();
        let end_position = {
            let script = self.get_script_info_or_panic(&file_name);
            self.test_converters()
                .position_to_line_and_character(script, script.content.len() as i32)
        };
        let params = CodeActionParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&file_name),
            },
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: end_position,
            },
            context: Some(CodeActionContext {
                only: Some(vec![requested_kind]),
                ..Default::default()
            }),
            ..Default::default()
        };

        let result = self.send_request(&TEXT_DOCUMENT_CODE_ACTION_INFO, params);

        let Some(items) = &result.command_or_code_action_array else {
            panic!("No organize imports code action found");
        };
        if items.is_empty() {
            panic!("No organize imports code action found");
        }

        let organize_action = items.iter().find_map(|item| {
            item.code_action
                .as_ref()
                .filter(|ca| ca.kind.as_ref() == Some(&expected_kind))
        });
        let Some(organize_action) = organize_action else {
            panic!("No organize imports code action found");
        };

        let expected_uri = lsconv::file_name_to_document_uri(&file_name);
        if let Some(changes) = organize_action.edit.as_ref().and_then(|e| e.changes.as_ref()) {
            for (uri, edits) in changes {
                if *uri != expected_uri {
                    panic!("Organize imports changed unexpected file: {uri} (expected {expected_uri})");
                }
                self.apply_text_edits(edits);
            }
        }

        let actual_content = &self.get_script_info_or_panic(&file_name).content;
        if *actual_content != expected_content {
            panic!(
                "Organize imports result doesn't match.\nExpected:\n{expected_content}\n\nActual:\n{actual_content}"
            );
        }
    }

    /// `findCompletionForCodeAction`
    fn find_completion_for_code_action(
        &mut self,
        items: &[CompletionItem],
        description: &str,
    ) -> Option<CompletionItem> {
        if let Some(item) = find(items, |item| {
            item.additional_text_edits
                .as_ref()
                .is_some_and(|e| !e.is_empty())
        }) {
            return Some(item.clone());
        }
        first_non_nil(items, |item| {
            let resolved_item = self.resolve_completion_item(item);
            let Some(additional) = &resolved_item.additional_text_edits else {
                return None;
            };
            if additional.is_empty() {
                return None;
            }
            if !description.is_empty()
                && !resolved_item
                    .detail
                    .as_deref()
                    .is_some_and(|d| d.contains(description))
            {
                return None;
            }
            Some(resolved_item)
        })
    }

    /// `VerifyApplyCodeActionFromCompletion`
    pub fn verify_apply_code_action_from_completion(
        &mut self,
        marker_name: &str,
        options: &ApplyCodeActionFromCompletionOptions,
    ) {
        self.go_to_marker(marker_name);
        let user_preferences = options
            .user_preferences
            .clone()
            // Default preferences: enables auto-imports
            .unwrap_or_else(lsutil::new_default_user_preferences);

        let original = self.configure_with_reset(user_preferences);
        let completions_list = self.get_completions(None); // Already configured, so we do not need to pass it in again
        let items: Vec<CompletionItem> = filter(
            completions_list
                .as_ref()
                .and_then(|l| l.items.as_deref())
                .unwrap_or(&[]),
            |item| {
                if item.label != options.name || item.data.is_none() {
                    return false;
                }
                let data = item.data.as_ref().unwrap();
                if let Some(auto_import_fix) = &options.auto_import_fix {
                    let mut module_specifier = auto_import_fix.module_specifier.as_str();
                    if module_specifier.is_empty() {
                        module_specifier = options.source.as_str();
                    }
                    return data
                        .auto_import
                        .as_ref()
                        .is_some_and(|ai| ai.module_specifier == module_specifier);
                }
                if data.auto_import.is_none()
                    && !data.source.as_str().is_empty()
                    && data.source.as_str() == options.source
                {
                    return true;
                }
                if data
                    .auto_import
                    .as_ref()
                    .is_some_and(|ai| ai.module_specifier == options.source)
                {
                    return true;
                }
                false
            },
        )
        .into_owned();

        let item = self.find_completion_for_code_action(&items, &options.description);
        let Some(item) = item else {
            panic!(
                "Code action '{}' from source '{}' not found.",
                options.name, options.source
            );
        };

        // apply the item to the test files
        let edits = item.additional_text_edits.clone().unwrap_or_default();
        self.apply_text_edits(&edits);
        if let Some(new_file_content) = &options.new_file_content {
            assert_eq!(
                self.get_script_info_or_panic(&self.active_filename.clone()).content,
                *new_file_content,
                "File content after applying code action did not match expected content."
            );
        } else if options.new_range_content.is_some() {
            panic!("!!! TODO");
        }
        self.configure(original);
    }

    /// `VerifyImportFixAtPosition`
    pub fn verify_import_fix_at_position(
        &mut self,
        expected_texts: &[String],
        preferences: Option<&UserPreferences>,
    ) {
        let file_name = self.active_filename.clone();
        let filtered_ranges = self.get_ranges_in_file(&file_name);
        if filtered_ranges.len() > 1 {
            panic!("Exactly one range should be specified in the testfile.");
        }
        let range_marker = filtered_ranges.into_iter().next();

        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_import_fix_at_position_worker(expected_texts, range_marker);
            self.configure(original);
            return;
        }
        self.verify_import_fix_at_position_worker(expected_texts, range_marker);
    }

    fn verify_import_fix_at_position_worker(
        &mut self,
        expected_texts: &[String],
        range_marker: Option<Rc<RangeMarker>>,
    ) {
        // Get diagnostics at the current position to find errors that need import fixes
        let diag_params = DocumentDiagnosticParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };
        let diag_result = self.send_request(&TEXT_DOCUMENT_DIAGNOSTIC_INFO, diag_params);
        let diagnostics: Vec<Diagnostic> = diag_result
            .full_document_diagnostic_report
            .and_then(|r| r.items)
            .unwrap_or_default();

        let current_caret_position = self.current_caret_position;
        let params = CodeActionParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            range: Range {
                end: current_caret_position,
                start: current_caret_position,
            },
            context: Some(CodeActionContext {
                diagnostics: Some(diagnostics),
                ..Default::default()
            }),
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_CODE_ACTION_INFO, params);

        // Find all auto-import code actions (fixes with fixId/fixName related to imports)
        // Skip fix-all entries (those without diagnostics attached)
        let import_actions: Vec<CodeAction> = result
            .command_or_code_action_array
            .unwrap_or_default()
            .into_iter()
            .filter_map(|item| {
                item.code_action.filter(|ca| {
                    ca.kind.as_ref() == Some(&CodeActionKind::QuickFix)
                        && ca.diagnostics.as_ref().is_some_and(|d| !d.is_empty())
                })
            })
            .collect();

        if import_actions.is_empty() {
            if !expected_texts.is_empty() {
                panic!("No codefixes returned.");
            }
            return;
        }

        // Save the original content before any edits
        let original_content = self
            .get_script_info_or_panic(&self.active_filename.clone())
            .content
            .clone();
        // For each import action, apply it and check the result
        let mut actual_text_array = Vec::with_capacity(import_actions.len());
        for action in &import_actions {
            // Apply the code action
            if let Some(changes) = action.edit.as_ref().and_then(|e| e.changes.as_ref()) {
                if changes.len() != 1 {
                    panic!("Expected exactly 1 change, got {}", changes.len());
                }
                for (uri, change_edits) in changes {
                    if *uri != lsconv::file_name_to_document_uri(&self.active_filename) {
                        panic!(
                            "Expected change to file {}, got {uri}",
                            self.active_filename.as_string()
                        );
                    }
                    self.apply_text_edits(change_edits);
                }
            }

            // Get the result text
            let text = match &range_marker {
                Some(r) => self.get_range_text(r),
                None => self
                    .get_script_info_or_panic(&self.active_filename.clone())
                    .content
                    .clone(),
            };
            actual_text_array.push(text);

            // Restore original content for next fix
            let end = self
                .get_script_info_or_panic(&self.active_filename.clone())
                .content
                .len() as i32;
            self.edit_script_and_update_markers(
                self.active_filename.clone(),
                0,
                end,
                &original_content,
            );
            self.current_caret_position = current_caret_position;
        }

        // Compare results
        if expected_texts.len() != actual_text_array.len() {
            let mut actual_joined = String::new();
            for (i, actual) in actual_text_array.iter().enumerate() {
                if i > 0 {
                    actual_joined.push_str("\n\n");
                    actual_joined.push_str(&"-".repeat(20));
                    actual_joined.push_str("\n\n");
                }
                actual_joined.push_str(actual);
            }
            panic!(
                "Expected {} import fixes, got {}:\n\n{actual_joined}",
                expected_texts.len(),
                actual_text_array.len()
            );
        }
        for (i, expected) in expected_texts.iter().enumerate() {
            let actual = &actual_text_array[i];
            assert_eq!(expected, actual, "Import fix at index {i} doesn't match.\n");
        }
    }

    /// `VerifyImportFixModuleSpecifiers`
    pub fn verify_import_fix_module_specifiers(
        &mut self,
        marker_name: &str,
        expected_module_specifiers: &[String],
        preferences: Option<&UserPreferences>,
    ) {
        self.go_to_marker(marker_name);

        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_import_fix_module_specifiers_worker(expected_module_specifiers);
            self.configure(original);
            return;
        }
        self.verify_import_fix_module_specifiers_worker(expected_module_specifiers);
    }

    fn verify_import_fix_module_specifiers_worker(&mut self, expected_module_specifiers: &[String]) {
        // Get diagnostics at the current position to find errors that need import fixes
        let diag_params = DocumentDiagnosticParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };
        let diag_result = self.send_request(&TEXT_DOCUMENT_DIAGNOSTIC_INFO, diag_params);
        let diagnostics: Vec<Diagnostic> = diag_result
            .full_document_diagnostic_report
            .and_then(|r| r.items)
            .unwrap_or_default();

        let params = CodeActionParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            range: Range {
                start: self.current_caret_position,
                end: self.current_caret_position,
            },
            context: Some(CodeActionContext {
                diagnostics: Some(diagnostics),
                ..Default::default()
            }),
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_CODE_ACTION_INFO, params);

        // Extract module specifiers from import fix code actions
        let mut actual_module_specifiers: Vec<String> = vec![];
        if let Some(items) = &result.command_or_code_action_array {
            for item in items {
                if let Some(code_action) = &item.code_action {
                    if code_action.kind.as_ref() == Some(&CodeActionKind::QuickFix) {
                        if let Some(changes) =
                            code_action.edit.as_ref().and_then(|e| e.changes.as_ref())
                        {
                            for change_edits in changes.values() {
                                for edit in change_edits {
                                    let module_spec = extract_module_specifier(&edit.new_text);
                                    if !module_spec.is_empty()
                                        && !actual_module_specifiers.contains(&module_spec)
                                    {
                                        actual_module_specifiers.push(module_spec);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Compare results
        if actual_module_specifiers.len() != expected_module_specifiers.len() {
            panic!(
                "Expected {} module specifiers, got {}.\nExpected: {:?}\nActual: {:?}",
                expected_module_specifiers.len(),
                actual_module_specifiers.len(),
                expected_module_specifiers,
                actual_module_specifiers
            );
        }

        for (i, expected) in expected_module_specifiers.iter().enumerate() {
            if i >= actual_module_specifiers.len() || actual_module_specifiers[i] != *expected {
                panic!(
                    "Module specifier mismatch at index {i}.\nExpected: {expected_module_specifiers:?}\nActual: {actual_module_specifiers:?}"
                );
            }
        }
    }
}

/// `type ApplyCodeActionFromCompletionOptions struct`
#[derive(Default)]
pub struct ApplyCodeActionFromCompletionOptions {
    pub name: String,
    pub source: String,
    pub auto_import_fix: Option<AutoImportFix>,
    pub description: String,
    pub new_file_content: Option<String>,
    pub new_range_content: Option<String>,
    pub user_preferences: Option<UserPreferences>,
}

/// `extractModuleSpecifier`
fn extract_module_specifier(text: &str) -> String {
    // Try to match: from "..." or from '...'
    if let Some(idx) = text.find("from \"") {
        let start = idx + 6; // len("from \"")
        if let Some(end) = text[start..].find('"') {
            return text[start..start + end].to_string();
        }
    }
    if let Some(idx) = text.find("from '") {
        let start = idx + 6; // len("from '")
        if let Some(end) = text[start..].find('\'') {
            return text[start..start + end].to_string();
        }
    }

    // Try to match: require("...") or require('...')
    if let Some(idx) = text.find("require(\"") {
        let start = idx + 9; // len("require(\"")
        if let Some(end) = text[start..].find('"') {
            return text[start..start + end].to_string();
        }
    }
    if let Some(idx) = text.find("require('") {
        let start = idx + 9; // len("require('")
        if let Some(end) = text[start..].find('\'') {
            return text[start..start + end].to_string();
        }
    }

    String::new()
}

// --- signature help ---------------------------------------------------------

/// `VerifySignatureHelpOptions` — all fields are optional; only specified
/// fields will be verified.
#[derive(Default)]
pub struct VerifySignatureHelpOptions {
    /// `Text` is the full signature text (e.g., "fn(x: string, y: number): void")
    pub text: String,
    /// `DocComment` is the documentation comment for the signature
    pub doc_comment: String,
    /// `ParameterCount` is the expected number of parameters
    pub parameter_count: usize,
    /// `ParameterName` is the expected name of the active parameter
    pub parameter_name: String,
    /// `ParameterSpan` is the expected label of the active parameter (e.g., "x: string")
    pub parameter_span: String,
    /// `ParameterDocComment` is the documentation for the active parameter
    pub parameter_doc_comment: String,
    /// `OverloadsCount` is the expected number of overloads (signatures)
    pub overloads_count: usize,
    /// `OverrideSelectedItemIndex` overrides which signature to check (default: ActiveSignature)
    pub override_selected_item_index: usize,
    /// `IsVariadic` indicates if the signature has a rest parameter
    pub is_variadic: bool,
    /// `IsVariadicSet` is true when IsVariadic was explicitly set (to distinguish from default false)
    pub is_variadic_set: bool,
}

impl FourslashTest {
    /// `VerifySignatureHelp` verifies signature help at the current position
    /// matches the expected options.
    pub fn verify_signature_help(&mut self, expected: &VerifySignatureHelpOptions) {
        let prefix = self.get_current_position_prefix();
        let params = SignatureHelpParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_SIGNATURE_HELP_INFO, params);
        let Some(help) = &result.signature_help else {
            panic!("{prefix}Could not get signature help");
        };

        // Determine which signature to check
        let mut selected_index = 0usize;
        if expected.override_selected_item_index > 0 {
            selected_index = expected.override_selected_item_index;
        } else if let Some(active) = help.active_signature {
            selected_index = active as usize;
        }

        if selected_index >= help.signatures.as_deref().unwrap_or(&[]).len() {
            panic!(
                "{prefix}Selected signature index {selected_index} out of range (have {} signatures)",
                help.signatures.as_deref().unwrap_or(&[]).len()
            );
        }

        let selected_sig = &help.signatures.as_deref().unwrap_or(&[])[selected_index];

        // Verify overloads count
        if expected.overloads_count > 0 && help.signatures.as_deref().unwrap_or(&[]).len() != expected.overloads_count {
            panic!("{prefix}Expected {} overloads, got {}", expected.overloads_count, help.signatures.as_deref().unwrap_or(&[]).len());
        }

        // Verify signature text
        if !expected.text.is_empty() && selected_sig.label != expected.text {
            panic!("{prefix}Expected signature text {:?}, got {:?}", expected.text, selected_sig.label);
        }

        // Verify doc comment
        if !expected.doc_comment.is_empty() {
            let mut actual_doc = String::new();
            if let Some(doc) = &selected_sig.documentation {
                if let Some(markup) = &doc.markup_content {
                    actual_doc = markup.value.clone();
                } else if let Some(s) = &doc.string {
                    actual_doc = s.clone();
                }
            }
            if actual_doc != expected.doc_comment {
                panic!("{prefix}Expected doc comment {:?}, got {actual_doc:?}", expected.doc_comment);
            }
        }

        // Verify parameter count
        if expected.parameter_count > 0 {
            let param_count = selected_sig
                .parameters
                .as_ref()
                .map_or(0, |p| p.len());
            if param_count != expected.parameter_count {
                panic!("{prefix}Expected {} parameters, got {param_count}", expected.parameter_count);
            }
        }

        // Get active parameter
        let mut active_param_index = 0usize;
        if let Some(active) = selected_sig
            .active_parameter
            .as_ref()
            .and_then(|a| a.uinteger)
        {
            active_param_index = active as usize;
        } else if let Some(active) = help.active_parameter.as_ref().and_then(|a| a.uinteger) {
            active_param_index = active as usize;
        }

        let active_param = selected_sig
            .parameters
            .as_ref()
            .and_then(|p| p.get(active_param_index));

        // Verify parameter name
        if !expected.parameter_name.is_empty() {
            let Some(active_param) = active_param else {
                panic!("{prefix}Expected parameter name {:?}, but no active parameter", expected.parameter_name);
            };
            // Parameter name is extracted from the label
            let mut actual_name = String::new();
            if let Some(label) = &active_param.label.string {
                // Extract name from label like "x: string" -> "x" or "T extends Foo" -> "T" or "...x: any[]" -> "x"
                let label = label.trim_start_matches("...");
                // Strip leading "..." for rest parameters
                if let Some((name, _)) = label.split_once(':') {
                    actual_name = name.trim().to_string();
                } else if let Some((name, _)) = label.split_once(" extends ") {
                    actual_name = name.trim().to_string();
                } else {
                    actual_name = label.to_string();
                }
            }
            if actual_name != expected.parameter_name {
                panic!("{prefix}Expected parameter name {:?}, got {actual_name:?}", expected.parameter_name);
            }
        }

        // Verify parameter span (label)
        if !expected.parameter_span.is_empty() {
            let Some(active_param) = active_param else {
                panic!("{prefix}Expected parameter span {:?}, but no active parameter", expected.parameter_span);
            };
            let actual_span = active_param.label.string.clone().unwrap_or_default();
            if actual_span != expected.parameter_span {
                panic!("{prefix}Expected parameter span {:?}, got {actual_span:?}", expected.parameter_span);
            }
        }

        // Verify parameter doc comment
        if !expected.parameter_doc_comment.is_empty() {
            let Some(active_param) = active_param else {
                panic!("{prefix}Expected parameter doc comment {:?}, but no active parameter", expected.parameter_doc_comment);
            };
            let mut actual_doc = String::new();
            if let Some(doc) = &active_param.documentation {
                if let Some(markup) = &doc.markup_content {
                    actual_doc = markup.value.clone();
                } else if let Some(s) = &doc.string {
                    actual_doc = s.clone();
                }
            }
            if actual_doc != expected.parameter_doc_comment {
                panic!("{prefix}Expected parameter doc comment {:?}, got {actual_doc:?}", expected.parameter_doc_comment);
            }
        }

        // Verify isVariadic (check if any parameter starts with "...")
        if expected.is_variadic_set {
            let actual_is_variadic = selected_sig
                .parameters
                .as_ref()
                .is_some_and(|params| {
                    params.iter().any(|p| {
                        p.label
                            .string
                            .as_deref()
                            .is_some_and(|l| l.starts_with("..."))
                    })
                });
            if actual_is_variadic != expected.is_variadic {
                panic!(
                    "{prefix}Expected isVariadic={}, got {actual_is_variadic}",
                    expected.is_variadic
                );
            }
        }
    }

    /// `VerifyNoSignatureHelp` verifies that no signature help is available at
    /// the current position.
    pub fn verify_no_signature_help(&mut self) {
        self.verify_no_signature_help_with_context(None);
    }

    /// `VerifyNoSignatureHelpWithContext`
    pub fn verify_no_signature_help_with_context(
        &mut self,
        context: Option<SignatureHelpContext>,
    ) {
        let prefix = self.get_current_position_prefix();
        let params = SignatureHelpParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            context,
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_SIGNATURE_HELP_INFO, params);
        if let Some(help) = &result.signature_help {
            if !help.signatures.as_deref().unwrap_or(&[]).is_empty() {
                panic!(
                    "{prefix}Expected no signature help, but got {} signatures",
                    help.signatures.as_deref().unwrap_or(&[]).len()
                );
            }
        }
    }

    /// `VerifyNoSignatureHelpForMarkersWithContext`
    pub fn verify_no_signature_help_for_markers_with_context(
        &mut self,
        context: Option<SignatureHelpContext>,
        markers: &[String],
    ) {
        for marker in markers {
            self.go_to_marker(marker);
            self.verify_no_signature_help_with_context(context.clone());
        }
    }

    /// `VerifySignatureHelpPresent` verifies that signature help is available
    /// at the current position with a given context.
    pub fn verify_signature_help_present(&mut self, context: Option<SignatureHelpContext>) {
        let prefix = self.get_current_position_prefix();
        let params = SignatureHelpParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            context,
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_SIGNATURE_HELP_INFO, params);
        if result
            .signature_help
            .as_ref()
            .is_none_or(|h| h.signatures.as_deref().is_none_or(|s| s.is_empty()))
        {
            panic!("{prefix}Expected signature help to be present, but got none");
        }
    }

    /// `VerifySignatureHelpPresentForMarkers`
    pub fn verify_signature_help_present_for_markers(
        &mut self,
        context: Option<SignatureHelpContext>,
        markers: &[String],
    ) {
        for marker in markers {
            self.go_to_marker(marker);
            self.verify_signature_help_present(context.clone());
        }
    }

    /// `VerifyNoSignatureHelpForMarkers`
    pub fn verify_no_signature_help_for_markers(&mut self, markers: &[String]) {
        for marker in markers {
            self.go_to_marker(marker);
            self.verify_no_signature_help();
        }
    }

    /// `VerifySignatureHelpWithCases`
    pub fn verify_signature_help_with_cases(&mut self, signature_help_cases: &[SignatureHelpCase]) {
        for option in signature_help_cases {
            match &option.marker_input {
                Some(MarkerInput::Name(marker)) => {
                    self.go_to_marker(marker);
                    self.verify_signature_help_expected(&option.context, option.expected.as_ref());
                }
                Some(MarkerInput::Marker(marker)) => {
                    self.go_to_marker_impl(&(marker.clone() as Rc<dyn MarkerOrRange>));
                    self.verify_signature_help_expected(&option.context, option.expected.as_ref());
                }
                Some(MarkerInput::Names(names)) => {
                    for marker_name in names {
                        self.go_to_marker(marker_name);
                        self.verify_signature_help_expected(&option.context, option.expected.as_ref());
                    }
                }
                Some(MarkerInput::Markers(markers)) => {
                    for marker in markers {
                        self.go_to_marker_impl(&(marker.clone() as Rc<dyn MarkerOrRange>));
                        self.verify_signature_help_expected(&option.context, option.expected.as_ref());
                    }
                }
                None => {
                    self.verify_signature_help_expected(&option.context, option.expected.as_ref());
                }
            }
        }
    }

    /// `verifySignatureHelp`
    fn verify_signature_help_expected(
        &mut self,
        context: &Option<SignatureHelpContext>,
        expected: Option<&SignatureHelp>,
    ) {
        let prefix = self.get_current_position_prefix();
        let params = SignatureHelpParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            context: context.clone(),
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_SIGNATURE_HELP_INFO, params);
        self.verify_signature_help_result(result.signature_help.as_ref(), expected, &prefix);
    }

    /// `verifySignatureHelpResult`
    fn verify_signature_help_result(
        &self,
        actual: Option<&SignatureHelp>,
        expected: Option<&SignatureHelp>,
        prefix: &str,
    ) {
        assert_deep_equal(&actual, &expected, &format!("{prefix} SignatureHelp mismatch"));
    }
}

/// `type SignatureHelpCase struct`
pub struct SignatureHelpCase {
    pub context: Option<SignatureHelpContext>,
    /// `MarkerInput` — `None` is Go's `nil` (verify at current position).
    pub marker_input: Option<MarkerInput>,
    pub expected: Option<SignatureHelp>,
}

// --- quick info / hover -----------------------------------------------------

impl FourslashTest {
    /// `VerifyQuickInfoAt`
    // !!! expected tags
    pub fn verify_quick_info_at(
        &mut self,
        marker: &str,
        expected_text: &str,
        expected_documentation: &str,
    ) {
        self.go_to_marker(marker);
        let hover = self.get_quick_info_at_current_position();
        let Some(hover) = hover else {
            panic!(
                "Expected hover result at marker '{}' but got nil",
                self.last_known_marker_name.as_deref().unwrap_or("")
            );
        };
        let prefix = self.get_current_position_prefix();
        self.verify_hover_content(&hover.contents, expected_text, expected_documentation, &prefix);
    }

    /// `getQuickInfoAtCurrentPosition`
    fn get_quick_info_at_current_position(&mut self) -> Option<Hover> {
        let params = HoverParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_HOVER_INFO, params);
        result.hover
    }

    /// `verifyHoverContent`
    fn verify_hover_content(
        &self,
        actual: &MarkupContentOrStringOrMarkedStringWithLanguageOrMarkedStrings,
        expected_text: &str,
        expected_documentation: &str,
        prefix: &str,
    ) {
        if let Some(markup) = &actual.markup_content {
            self.verify_hover_markdown(&markup.value, expected_text, expected_documentation, prefix);
        } else {
            panic!("{prefix}Expected markup content, got: {actual:?}");
        }
    }

    /// `verifyHoverMarkdown`
    fn verify_hover_markdown(
        &self,
        actual: &str,
        expected_text: &str,
        expected_documentation: &str,
        prefix: &str,
    ) {
        let expected = format!("```typescript\n{expected_text}\n```\n{expected_documentation}");
        assert_deep_equal(&actual.to_string(), &expected, &format!("{prefix}Hover markdown content mismatch"));
    }

    /// `VerifyQuickInfoExists`
    pub fn verify_quick_info_exists(&mut self) {
        if self.quick_info_is_empty() {
            panic!(
                "Expected non-nil hover content at marker '{}'",
                self.last_known_marker_name.as_deref().unwrap_or("")
            );
        }
    }

    /// `VerifyNotQuickInfoExists`
    pub fn verify_not_quick_info_exists(&mut self) {
        if let Some(hover) = self.quick_info_nonempty() {
            panic!(
                "Expected empty hover content at marker '{}', got '{:?}'",
                self.last_known_marker_name.as_deref().unwrap_or(""),
                hover
            );
        }
    }

    fn quick_info_is_empty(&mut self) -> bool {
        self.quick_info_nonempty().is_none()
    }

    /// `quickInfoIsEmpty` — returns `Some(hover)` when non-empty.
    fn quick_info_nonempty(&mut self) -> Option<Hover> {
        let hover = self.get_quick_info_at_current_position()?;
        if hover.contents.markup_content.is_none()
            && hover.contents.marked_strings.is_none()
            && hover.contents.string.is_none()
        {
            return None;
        }
        Some(hover)
    }

    /// `VerifyQuickInfoIs`
    pub fn verify_quick_info_is(&mut self, expected_text: &str, expected_documentation: &str) {
        let hover = self.get_quick_info_at_current_position();
        let contents = hover.expect("hover").contents;
        let prefix = self.get_current_position_prefix();
        self.verify_hover_content(&contents, expected_text, expected_documentation, &prefix);
    }

    /// `VerifyJsxClosingTag`
    pub fn verify_jsx_closing_tag(&mut self, markers_to_new_text: &BTreeMap<String, Option<String>>) {
        for (marker, expected_text) in markers_to_new_text {
            self.go_to_marker(marker);
            let params = VSOnAutoInsertParams {
                vs_text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                vs_position: self.current_caret_position,
                vs_ch: ">".to_string(),
            };

            let request_result = self.send_request(&TEXT_DOCUMENT_VS_ON_AUTO_INSERT_INFO, params);

            let mut actual_text: Option<String> = None;
            if let Some(item) = &request_result.vs_on_auto_insert_response_item {
                if let Some(vs_text_edit) = &item.vs_text_edit {
                    let mut new_text = vs_text_edit.new_text.clone();
                    if item.vs_text_edit_format == InsertTextFormat::Snippet {
                        let Some(stripped) = new_text.strip_prefix("$0") else {
                            panic!(
                                "{}expected JSX closing tag snippet to begin with $0, got {:?}",
                                self.get_current_position_prefix(),
                                vs_text_edit.new_text
                            );
                        };
                        new_text = stripped.to_string();
                    }
                    actual_text = Some(new_text);
                }
            }
            let prefix = self.get_current_position_prefix();
            assert_deep_equal(&actual_text, expected_text, &format!("{prefix}JSX closing tag text mismatch"));
        }
    }
}

// --- diagnostics / errors ----------------------------------------------------

impl FourslashTest {
    /// `VerifyDiagnostics`
    pub fn verify_diagnostics(&mut self, expected: &[Diagnostic]) {
        self.verify_diagnostics_impl(expected, |_| true);
    }

    /// `VerifyNonSuggestionDiagnostics` — like `verify_diagnostics` but
    /// excludes suggestion diagnostics returned from server.
    pub fn verify_non_suggestion_diagnostics(&mut self, expected: &[Diagnostic]) {
        self.verify_diagnostics_impl(expected, |d| !is_suggestion_diagnostic(d));
    }

    /// `VerifySuggestionDiagnostics` — includes only suggestion diagnostics.
    pub fn verify_suggestion_diagnostics(&mut self, expected: &[Diagnostic]) {
        self.verify_diagnostics_impl(expected, is_suggestion_diagnostic);
    }

    fn verify_diagnostics_impl(
        &mut self,
        expected: &[Diagnostic],
        filter_diagnostics: impl Fn(&Diagnostic) -> bool,
    ) {
        let file_name = self.active_filename.clone();
        let actual_diagnostics = self.get_diagnostics(&file_name);
        let actual_diagnostics = filter(&actual_diagnostics, |d| filter_diagnostics(d)).into_owned();
        let empty_range = Range::default();
        let mut expected_with_ranges = Vec::with_capacity(expected.len());
        for diag in expected {
            if diag.range == empty_range {
                let ranges_in_file = self.get_ranges_in_file(&file_name);
                if ranges_in_file.is_empty() {
                    panic!("No ranges found in file {} to assign to diagnostic with empty range", file_name.as_string());
                }
                let mut diag_with_range = diag.clone();
                diag_with_range.range = ranges_in_file[0].ls_range.clone();
                expected_with_ranges.push(diag_with_range);
            } else {
                expected_with_ranges.push(diag.clone());
            }
        }
        if actual_diagnostics.is_empty() && expected_with_ranges.is_empty() {
            return;
        }
        // PORT: `diagnosticsIgnoreOpts` ignores ".Severity", ".Source",
        // ".RelatedInformation" — compare field-wise instead of cmp.Diff.
        assert_eq!(
            actual_diagnostics.len(),
            expected_with_ranges.len(),
            "Diagnostics do not match expected"
        );
        for (actual, expected) in actual_diagnostics.iter().zip(&expected_with_ranges) {
            diagnostic_eq_ignoring(actual, expected, "Diagnostics do not match expected");
        }
    }

    /// `getDiagnostics`
    pub(crate) fn get_diagnostics(&mut self, file_name: &RootedFilePath) -> Vec<Diagnostic> {
        let params = DocumentDiagnosticParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(file_name),
            },
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_DIAGNOSTIC_INFO, params);
        result
            .full_document_diagnostic_report
            .and_then(|r| r.items)
            .unwrap_or_default()
    }

    /// `VerifyNumberOfErrorsInCurrentFile` verifies that the current file has
    /// the expected number of errors.
    pub fn verify_number_of_errors_in_current_file(&mut self, expected_count: usize) {
        let file_name = self.active_filename.clone();
        let diagnostics = self.get_diagnostics(&file_name);
        // Filter to only include errors (not suggestions/hints)
        let errors = filter(&diagnostics, |d| !is_suggestion_diagnostic(d));
        if errors.len() != expected_count {
            panic!("Expected {expected_count} errors in current file, but got {}", errors.len());
        }
    }

    /// `VerifyNoErrors` verifies that no errors exist in any open files.
    pub fn verify_no_errors(&mut self) {
        for file_name in self.open_files.clone() {
            let diagnostics = self.get_diagnostics(&file_name);
            // Filter to only include errors (not suggestions/hints)
            let errors = filter(&diagnostics, |d| !is_suggestion_diagnostic(d));
            if !errors.is_empty() {
                let messages: Vec<String> = errors
                    .iter()
                    .map(|e| e.message.string.clone().unwrap_or_default())
                    .collect();
                panic!(
                    "Expected no errors but found {} in {}: {messages:?}",
                    errors.len(),
                    file_name.as_string()
                );
            }
        }
    }

    /// `VerifyErrorExistsAtRange` verifies that an error with the given code
    /// exists at the given range.
    pub fn verify_error_exists_at_range(
        &mut self,
        range_marker: &Rc<RangeMarker>,
        code: i32,
        message: &str,
    ) {
        let (file_name, ls_range) = {
            let r = range_marker.as_ref();
            (r.file_name().clone(), r.ls_range.clone())
        };
        let diagnostics = self.get_diagnostics(&file_name);
        for diag in &diagnostics {
            if diag
                .code
                .as_ref()
                .and_then(|c| c.integer)
                == Some(code)
            {
                // Check if the range matches
                if diag.range.start.line == ls_range.start.line
                    && diag.range.start.character == ls_range.start.character
                    && diag.range.end.line == ls_range.end.line
                    && diag.range.end.character == ls_range.end.character
                {
                    // If message is provided, verify it matches
                    if !message.is_empty() && diag.message.string.clone().unwrap_or_default() != message {
                        panic!(
                            "Error at range has code {code} but message mismatch. Expected: {message:?}, Got: {:?}",
                            diag.message.string.clone().unwrap_or_default()
                        );
                    }
                    return;
                }
            }
        }
        panic!("Expected error with code {code} at range {ls_range:?} but it was not found");
    }

    /// `VerifyErrorExistsBetweenMarkers` verifies that an error exists between
    /// the two markers.
    pub fn verify_error_exists_between_markers(
        &mut self,
        start_marker_name: &str,
        end_marker_name: &str,
    ) {
        let start_marker = match self.test_data.marker_positions.get(start_marker_name) {
            Some(m) => m.clone(),
            None => panic!("Start marker '{start_marker_name}' not found"),
        };
        let end_marker = match self.test_data.marker_positions.get(end_marker_name) {
            Some(m) => m.clone(),
            None => panic!("End marker '{end_marker_name}' not found"),
        };
        let (file_name, start_pos) = {
            let m = start_marker.as_ref();
            (m.file_name().clone(), m.position)
        };
        let (end_file, end_pos) = {
            let m = end_marker.as_ref();
            (m.file_name().clone(), m.position)
        };
        if file_name != end_file {
            panic!("Markers '{start_marker_name}' and '{end_marker_name}' are in different files");
        }

        let diagnostics = self.get_diagnostics(&file_name);

        for diag in &diagnostics {
            if !is_suggestion_diagnostic(diag) {
                let (diag_start, diag_end) = {
                    let script = self.get_script_info_or_panic(&file_name);
                    let converters = self.test_converters();
                    (
                        converters.line_and_character_to_position(script, diag.range.start),
                        converters.line_and_character_to_position(script, diag.range.end),
                    )
                };
                if diag_start >= start_pos && diag_end <= end_pos {
                    return; // Found an error in the range
                }
            }
        }
        panic!("Expected error between markers '{start_marker_name}' and '{end_marker_name}' but none was found");
    }

    /// `VerifyErrorExistsAfterMarker` verifies that an error exists after the
    /// given marker. An empty `marker_name` uses the current position.
    pub fn verify_error_exists_after_marker(&mut self, marker_name: &str) {
        let (file_name, marker_pos) = if marker_name.is_empty() {
            // Use current position
            (self.active_filename.clone(), self.caret_offset())
        } else {
            let marker = match self.test_data.marker_positions.get(marker_name) {
                Some(m) => m.clone(),
                None => panic!("Marker '{marker_name}' not found"),
            };
            let m = marker.as_ref();
            (m.file_name().clone(), m.position)
        };

        let diagnostics = self.get_diagnostics(&file_name);

        for diag in &diagnostics {
            if !is_suggestion_diagnostic(diag) {
                let diag_start = {
                    let script = self.get_script_info_or_panic(&file_name);
                    self.test_converters()
                        .line_and_character_to_position(script, diag.range.start)
                };
                if diag_start >= marker_pos {
                    return; // Found an error after the marker
                }
            }
        }
        panic!("Expected error after marker '{marker_name}' but none was found");
    }

    /// `VerifyErrorExistsBeforeMarker` verifies that an error exists before
    /// the given marker. An empty `marker_name` uses the current position.
    pub fn verify_error_exists_before_marker(&mut self, marker_name: &str) {
        let (file_name, marker_pos) = if marker_name.is_empty() {
            // Use current position
            (self.active_filename.clone(), self.caret_offset())
        } else {
            let marker = match self.test_data.marker_positions.get(marker_name) {
                Some(m) => m.clone(),
                None => panic!("Marker '{marker_name}' not found"),
            };
            let m = marker.as_ref();
            (m.file_name().clone(), m.position)
        };

        let diagnostics = self.get_diagnostics(&file_name);

        for diag in &diagnostics {
            if !is_suggestion_diagnostic(diag) {
                let diag_end = {
                    let script = self.get_script_info_or_panic(&file_name);
                    self.test_converters()
                        .line_and_character_to_position(script, diag.range.end)
                };
                if diag_end <= marker_pos {
                    return; // Found an error before the marker
                }
            }
        }
        panic!("Expected error before marker '{marker_name}' but none was found");
    }
}

/// `isSuggestionDiagnostic`
pub(crate) fn is_suggestion_diagnostic(diag: &Diagnostic) -> bool {
    diag.severity == Some(DiagnosticSeverity::Hint)
}

/// `diagnostic_eq_ignoring` — `cmp.Diff` with `diagnosticsIgnoreOpts`
/// (ignores `.Severity`, `.Source`, `.RelatedInformation`).
fn diagnostic_eq_ignoring(actual: &Diagnostic, expected: &Diagnostic, prefix: &str) {
    macro_rules! check {
        ($name:literal, $a:expr, $e:expr) => {
            assert_eq!($a, $e, "{prefix}: {} mismatch", $name);
        };
    }
    check!("Range", &actual.range, &expected.range);
    check!("Code", &actual.code, &expected.code);
    check!("CodeDescription", &actual.code_description, &expected.code_description);
    check!("Message", &actual.message, &expected.message);
    check!("Tags", &actual.tags, &expected.tags);
    check!("Data", &actual.data, &expected.data);
}

// --- outlining / folding ------------------------------------------------------

impl FourslashTest {
    /// `VerifyOutliningSpans`
    pub fn verify_outlining_spans(&mut self, folding_range_kind: Option<FoldingRangeKind>) {
        let params = FoldingRangeParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_FOLDING_RANGE_INFO, params);
        let Some(folding_ranges) = result.folding_ranges else {
            panic!("Nil response received for folding range request");
        };

        // Extract actual folding ranges from the result and filter by kind if specified
        let mut actual_ranges = folding_ranges;
        if let Some(target_kind) = folding_range_kind {
            actual_ranges.retain(|r| r.kind.as_ref() == Some(&target_kind));
        }

        if actual_ranges.len() != self.ranges().len() {
            panic!(
                "verifyOutliningSpans failed - expected total spans to be {}, but was {}",
                self.ranges().len(),
                actual_ranges.len()
            );
        }

        let mut expected_ranges = self.ranges();
        expected_ranges.sort_by(|a, b| {
            let (a, b) = (a.as_ref(), b.as_ref());
            compare_positions(&a.ls_range.start, &b.ls_range.start).cmp(&0)
        });

        for (i, expected_range) in expected_ranges.iter().enumerate() {
            let actual_range = &actual_ranges[i];
            let expected = expected_range.as_ref();
            let start_pos = Position {
                line: actual_range.start_line,
                character: actual_range.start_character.unwrap_or(0),
            };
            let end_pos = Position {
                line: actual_range.end_line,
                character: actual_range.end_character.unwrap_or(0),
            };

            if compare_positions(&start_pos, &expected.ls_range.start) != 0
                || compare_positions(&end_pos, &expected.ls_range.end) != 0
            {
                panic!(
                    "verifyOutliningSpans failed - span {} has invalid positions:\n  actual: start ({},{}), end ({},{})\n  expected: start ({},{}), end ({},{})",
                    i + 1,
                    actual_range.start_line,
                    actual_range.start_character.unwrap_or(0),
                    actual_range.end_line,
                    actual_range.end_character.unwrap_or(0),
                    expected.ls_range.start.line,
                    expected.ls_range.start.character,
                    expected.ls_range.end.line,
                    expected.ls_range.end.character
                );
            }
        }
    }

    /// `VerifyFoldingRangeLines` verifies folding ranges by comparing only
    /// start and end lines (for lineFoldingOnly where chars are ignored).
    pub fn verify_folding_range_lines(&mut self, expected: &[FoldingRangeLineExpected]) {
        let params = FoldingRangeParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_FOLDING_RANGE_INFO, params);
        let Some(actual_ranges) = result.folding_ranges else {
            panic!("Nil response received for folding range request");
        };

        if actual_ranges.len() != expected.len() {
            panic!(
                "verifyFoldingRangeLines failed - expected {} ranges, got {}",
                expected.len(),
                actual_ranges.len()
            );
        }

        for (i, exp) in expected.iter().enumerate() {
            let got = &actual_ranges[i];
            if got.start_line != exp.start_line || got.end_line != exp.end_line {
                panic!(
                    "verifyFoldingRangeLines failed - range {i}: expected (startLine={}, endLine={}), got (startLine={}, endLine={})",
                    exp.start_line, exp.end_line, got.start_line, got.end_line
                );
            }
        }
    }
}

/// `FoldingRangeLineExpected` represents expected start and end lines for a folding range.
pub struct FoldingRangeLineExpected {
    pub start_line: u32,
    pub end_line: u32,
}

// --- workspace symbols ---------------------------------------------------------

/// `type VerifyWorkspaceSymbolCase struct`
pub struct VerifyWorkspaceSymbolCase {
    pub pattern: String,
    pub includes: Option<Vec<SymbolInformation>>,
    pub exact: Option<Vec<SymbolInformation>>,
    pub preferences: Option<UserPreferences>,
}

impl FourslashTest {
    /// `VerifyWorkspaceSymbol` — `verify.navigateTo` in Strada.
    pub fn verify_workspace_symbol(&mut self, cases: &[VerifyWorkspaceSymbolCase]) {
        let original_preferences = self.user_preferences.as_ref().clone();
        for test_case in cases {
            let preferences = test_case
                .preferences
                .clone()
                .unwrap_or_else(lsutil::new_default_user_preferences);
            self.configure(preferences);
            let result = self.send_request(
                &WORKSPACE_SYMBOL_INFO,
                WorkspaceSymbolParams {
                    query: test_case.pattern.clone(),
                    text_document: Some(TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&self.active_filename),
                    }),
                    ..Default::default()
                },
            );
            let Some(symbol_informations) = &result.symbol_informations else {
                panic!("Expected non-nil symbol information array from workspace symbol request");
            };
            if let Some(includes) = &test_case.includes {
                if test_case.exact.is_some() {
                    panic!("Test case cannot have both 'Includes' and 'Exact' fields set");
                }
                verify_includes_symbols(
                    symbol_informations,
                    includes,
                    &format!("Workspace symbols mismatch with pattern '{}'", test_case.pattern),
                );
            } else {
                let Some(exact) = &test_case.exact else {
                    panic!("Test case must have either 'Includes' or 'Exact' field set");
                };
                verify_exact_symbols(
                    symbol_informations,
                    exact,
                    &format!("Workspace symbols mismatch with pattern '{}'", test_case.pattern),
                );
            }
        }
        self.configure(original_preferences);
    }
}

/// `verifyExactSymbols`
fn verify_exact_symbols(
    actual: &[SymbolInformation],
    expected: &[SymbolInformation],
    prefix: &str,
) {
    if actual.len() != expected.len() {
        panic!(
            "{prefix}: Expected {} symbols, but got {}:\nactual:   {actual:?}\nexpected: {expected:?}",
            expected.len(),
            actual.len()
        );
    }
    for i in 0..actual.len() {
        assert_deep_equal(&actual[i], &expected[i], prefix);
    }
}

/// `verifyIncludesSymbols`
fn verify_includes_symbols(
    actual: &[SymbolInformation],
    includes: &[SymbolInformation],
    prefix: &str,
) {
    // PORT: `Location` is `PartialEq` only; key on its component fields.
    #[derive(PartialEq, Eq, Hash)]
    struct Key<'a> {
        name: &'a str,
        uri: &'a DocumentUri,
        start: (u32, u32),
        end: (u32, u32),
    }
    fn key_of(sym: &SymbolInformation) -> Key<'_> {
        Key {
            name: &sym.name,
            uri: &sym.location.uri,
            start: (
                sym.location.range.start.line,
                sym.location.range.start.character,
            ),
            end: (sym.location.range.end.line, sym.location.range.end.character),
        }
    }
    let mut name_and_loc_to_actual_symbol: HashMap<Key<'_>, &SymbolInformation> =
        HashMap::with_capacity(actual.len());
    for sym in actual {
        name_and_loc_to_actual_symbol.insert(key_of(sym), sym);
    }

    for sym in includes {
        let Some(actual_sym) = name_and_loc_to_actual_symbol.get(&key_of(sym)) else {
            panic!(
                "{prefix}: Expected symbol '{}' at location '{:?}' not found",
                sym.name, sym.location
            );
        };
        assert_deep_equal(
            *actual_sym,
            sym,
            &format!("{prefix}: Symbol '{}' at location '{:?}' mismatch", sym.name, sym.location),
        );
    }
}

use std::collections::HashMap;

// --- linked editing ------------------------------------------------------------

impl FourslashTest {
    /// `VerifyLinkedEditing`
    pub fn verify_linked_editing(&mut self, marker_names_to_expected: &BTreeMap<String, Vec<Range>>) {
        for (marker_name, expected_ranges) in marker_names_to_expected {
            self.go_to_marker(marker_name);
            let params = LinkedEditingRangeParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                ..Default::default()
            };
            let result = self.send_request(&TEXT_DOCUMENT_LINKED_EDITING_RANGE_INFO, params);
            let actual_ranges = result.linked_editing_ranges;
            if expected_ranges.is_empty() {
                if let Some(actual) = &actual_ranges {
                    if !actual.ranges.as_deref().unwrap_or(&[]).is_empty() {
                        panic!(
                            "Expected no linked editing ranges for marker '{marker_name}', but found {:?}",
                            actual_ranges
                        );
                    }
                }
                continue;
            }
            let Some(actual_ranges) = actual_ranges else {
                panic!("Expected linked editing ranges for marker '{marker_name}', but found none");
            };
            if actual_ranges.ranges.as_deref().unwrap_or(&[]).is_empty() {
                panic!("Expected linked editing ranges for marker '{marker_name}', but found none");
            }

            assert_deep_equal(
                &actual_ranges.ranges.as_deref().unwrap_or(&[])[0],
                &expected_ranges[0],
                &format!("Linked editing ranges for opening element do not match expected for marker '{marker_name}'"),
            );
            assert_deep_equal(
                &actual_ranges.ranges.as_deref().unwrap_or(&[])[1],
                &expected_ranges[1],
                &format!("Linked editing ranges for closing element do not match expected for marker '{marker_name}'"),
            );
        }
    }
}

// --- rename ---------------------------------------------------------------------

impl FourslashTest {
    /// `VerifyBaselineRenameAtRangesWithText` lives in verify_baseline.rs; the
    /// non-baseline rename verifiers are here.
    /// `VerifyRenameSucceeded`
    pub fn verify_rename_succeeded(&mut self, preferences: Option<&UserPreferences>) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_rename_succeeded_impl();
            self.configure(original);
            return;
        }
        self.verify_rename_succeeded_impl();
    }

    fn verify_rename_succeeded_impl(&mut self) {
        let params = PrepareRenameParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            ..Default::default()
        };

        let prefix = self.get_current_position_prefix();
        let result = self.send_request(&TEXT_DOCUMENT_PREPARE_RENAME_INFO, params);
        if result.range.is_none()
            && result.prepare_rename_placeholder.is_none()
            && result.prepare_rename_default_behavior.is_none()
        {
            panic!("{prefix}Expected rename to succeed, but prepareRename returned null");
        }

        // Also verify that textDocument/rename produces edits, since prepareRename is optional.
        let rename_result = self.send_request(
            &TEXT_DOCUMENT_RENAME_INFO,
            RenameParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                new_name: "RENAME_SUCCEEDED_TEST".to_string(),
                ..Default::default()
            },
        );
        if rename_result
            .workspace_edit
            .as_ref()
            .and_then(|e| e.changes.as_ref())
            .is_none_or(|c| c.is_empty())
        {
            panic!("{prefix}prepareRename succeeded but textDocument/rename returned no changes");
        }
    }

    /// `VerifyRenameRange`
    pub fn verify_rename_range(
        &mut self,
        expected_range: Range,
        expected_placeholder: &str,
        preferences: Option<&UserPreferences>,
    ) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_rename_range_impl(expected_range, expected_placeholder);
            self.configure(original);
            return;
        }
        self.verify_rename_range_impl(expected_range, expected_placeholder);
    }

    fn verify_rename_range_impl(&mut self, expected_range: Range, expected_placeholder: &str) {
        let params = PrepareRenameParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            ..Default::default()
        };

        let result = self.send_request(&TEXT_DOCUMENT_PREPARE_RENAME_INFO, params);
        let Some(placeholder) = &result.prepare_rename_placeholder else {
            panic!("{}Expected prepareRename to return a range and placeholder", self.get_current_position_prefix());
        };
        assert_deep_equal(&placeholder.range, &expected_range, "rename range mismatch");
        assert_eq!(placeholder.placeholder, expected_placeholder);
    }

    /// `RenameAtCaret`
    pub fn rename_at_caret(&mut self, new_name: &str) -> RenameResponse {
        let result = self.send_request(
            &TEXT_DOCUMENT_RENAME_INFO,
            RenameParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                new_name: new_name.to_string(),
                ..Default::default()
            },
        );

        let Some(workspace_edit) = &result.workspace_edit else {
            return result;
        };

        if let Some(changes) = &workspace_edit.changes {
            for (uri, edits) in changes {
                let file_name = uri.file_name();
                if self.get_or_load_script_info(&file_name).is_none() {
                    panic!("No script info for {}", file_name.as_string());
                }
                let changes_vec = map(edits, |edit| TextChange {
                    text_range: self.from_lsp_range(
                        self.get_script_info_or_panic(&file_name),
                        edit.range.clone(),
                    ),
                    new_text: edit.new_text.clone(),
                });
                self.edit_script_and_update_markers_worker(file_name.clone(), changes_vec);
            }
        }

        let mut rename_files: Vec<RenameFile> = vec![];
        if let Some(document_changes) = &workspace_edit.document_changes {
            for doc_change in document_changes {
                if let Some(text_document_edit) = &doc_change.text_document_edit {
                    let file_name = text_document_edit.text_document.uri.file_name();
                    if self.get_or_load_script_info(&file_name).is_none() {
                        panic!("No script info for {}", file_name.as_string());
                    }
                    let changes_vec = map(
                        text_document_edit.edits.as_deref().unwrap_or(&[]),
                        |edit| TextChange {
                            text_range: self.from_lsp_range(
                                self.get_script_info_or_panic(&file_name),
                                edit.text_edit
                                    .as_ref()
                                    .map(|t| t.range.clone())
                                    .unwrap_or_default(),
                            ),
                            new_text: edit
                                .text_edit
                                .as_ref()
                                .map(|t| t.new_text.clone())
                                .unwrap_or_default(),
                        },
                    );
                    self.edit_script_and_update_markers_worker(file_name.clone(), changes_vec);
                } else if let Some(rename_file) = &doc_change.rename_file {
                    rename_files.push(rename_file.clone());
                }
            }
        }

        if !rename_files.is_empty() {
            let file_renames: Vec<FileRename> = rename_files
                .iter()
                .map(|rename_file| FileRename {
                    old_uri: rename_file.old_uri.clone(),
                    new_uri: rename_file.new_uri.clone(),
                })
                .collect();
            if self
                .capabilities
                .as_ref()
                .and_then(|c| c.workspace.as_ref())
                .and_then(|w| w.file_operations.as_ref())
                .and_then(|f| f.will_rename)
                == Some(true)
            {
                self.will_rename_files_worker(&file_renames);
            } else {
                for rename_file in &rename_files {
                    let old_path = rename_file.old_uri.file_name().as_path();
                    let new_path = rename_file.new_uri.file_name().as_path();
                    self.rename_file_or_directory(&old_path, &new_path);
                }
            }
        }

        result
    }

    /// `WillRenameFiles`
    pub fn will_rename_files(&mut self, files: &[FileRename]) -> WillRenameFilesResponse {
        self.send_request(
            &WORKSPACE_WILL_RENAME_FILES_INFO,
            RenameFilesParams {
                files: Some(files.to_vec()),
            },
        )
    }

    /// `willRenameFilesWorker` — emulates a file rename by sending a
    /// workspace/willRenameFiles request and applying the resulting edits and
    /// file renames.
    fn will_rename_files_worker(&mut self, files: &[FileRename]) {
        let result = self.will_rename_files(files);

        let Some(workspace_edit) = &result.workspace_edit else {
            for file in files {
                let old_path = file.old_uri.file_name().as_path();
                let new_path = file.new_uri.file_name().as_path();
                self.rename_file_or_directory(&old_path, &new_path);
            }
            return;
        };

        if let Some(changes) = &workspace_edit.changes {
            for (uri, edits) in changes {
                let file_name = uri.file_name();
                if self.get_or_load_script_info(&file_name).is_none() {
                    panic!("No script info for {}", file_name.as_string());
                }
                let changes_vec = map(edits, |edit| TextChange {
                    text_range: self.from_lsp_range(
                        self.get_script_info_or_panic(&file_name),
                        edit.range.clone(),
                    ),
                    new_text: edit.new_text.clone(),
                });
                self.edit_script_and_update_markers_worker(file_name.clone(), changes_vec);
            }
        }

        let mut rename_files: Vec<RenameFile> = vec![];
        if let Some(document_changes) = &workspace_edit.document_changes {
            for doc_change in document_changes {
                if let Some(text_document_edit) = &doc_change.text_document_edit {
                    let file_name = text_document_edit.text_document.uri.file_name();
                    if self.get_or_load_script_info(&file_name).is_none() {
                        panic!("No script info for {}", file_name.as_string());
                    }
                    let changes_vec = map(
                        text_document_edit.edits.as_deref().unwrap_or(&[]),
                        |edit| TextChange {
                            text_range: self.from_lsp_range(
                                self.get_script_info_or_panic(&file_name),
                                edit.text_edit
                                    .as_ref()
                                    .map(|t| t.range.clone())
                                    .unwrap_or_default(),
                            ),
                            new_text: edit
                                .text_edit
                                .as_ref()
                                .map(|t| t.new_text.clone())
                                .unwrap_or_default(),
                        },
                    );
                    self.edit_script_and_update_markers_worker(file_name.clone(), changes_vec);
                } else if let Some(rename_file) = &doc_change.rename_file {
                    rename_files.push(rename_file.clone());
                }
            }
        }

        let file_renames: Vec<FileRename> = rename_files
            .iter()
            .map(|rename_file| FileRename {
                old_uri: rename_file.old_uri.clone(),
                new_uri: rename_file.new_uri.clone(),
            })
            .collect();
        self.will_rename_files_worker(&file_renames);

        for file in files {
            let old_path = file.old_uri.file_name().as_path();
            let new_path = file.new_uri.file_name().as_path();
            self.rename_file_or_directory(&old_path, &new_path);
        }
    }

    /// `VerifyRename`
    pub fn verify_rename(
        &mut self,
        marker_name: &str,
        new_name: &str,
        expected_file_contents: &BTreeMap<String, String>,
    ) {
        self.go_to_marker(marker_name);
        self.rename_at_caret(new_name);
        for (file_name, expected_content) in expected_file_contents {
            let script = self.get_script_info(&tspath::to_rooted_file_path(file_name, &crate::fourslash::root_dir()));
            let Some(script) = script else {
                panic!("Expected script info for {file_name}, but got nil");
            };
            assert_eq!(
                script.content, *expected_content,
                "File content after rename did not match expected content for {file_name}."
            );
        }
    }

    /// `VerifyWillRenameFilesEdits`
    pub fn verify_will_rename_files_edits(
        &mut self,
        old_path: &str,
        new_path: &str,
        expected_file_contents: &BTreeMap<String, String>,
        preferences: Option<&UserPreferences>,
    ) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_will_rename_files_edits_impl(old_path, new_path, expected_file_contents);
            self.configure(original);
            return;
        }
        self.verify_will_rename_files_edits_impl(old_path, new_path, expected_file_contents);
    }

    fn verify_will_rename_files_edits_impl(
        &mut self,
        old_path: &str,
        new_path: &str,
        expected_file_contents: &BTreeMap<String, String>,
    ) {
        self.will_rename_files_worker(&[FileRename {
            old_uri: lsconv::file_name_to_document_uri(&tspath::to_rooted_file_path(old_path, &crate::fourslash::root_dir())),
            new_uri: lsconv::file_name_to_document_uri(&tspath::to_rooted_file_path(new_path, &crate::fourslash::root_dir())),
        }]);

        for (file_name, expected_content) in expected_file_contents {
            let script = self.get_or_load_script_info(&tspath::to_rooted_file_path(file_name, &crate::fourslash::root_dir()));
            let Some(script) = script else {
                panic!("Expected script info for {file_name}, but got nil");
            };
            assert_eq!(
                script.content, *expected_content,
                "File content after workspace/willRenameFiles edits did not match expected content for {file_name}."
            );
        }
    }

    /// `renameFileOrDirectory`
    fn rename_file_or_directory(&mut self, old_path: &RootedPath, new_path: &RootedPath) {
        // Collect all file paths that need to be renamed.
        let mut old_file_names: BTreeMap<RootedFilePath, ()> = BTreeMap::new();
        let old_file_name = tspath::rooted_file_path_from_path(old_path.clone());
        let mut old_directory = tspath::RootedDirectoryPath::default();
        let mut new_directory = tspath::RootedDirectoryPath::default();
        let mut new_file_name = RootedFilePath::default();
        if self.vfs.read_file(&old_file_name).is_some() {
            old_file_names.insert(old_file_name.clone(), ());
            new_file_name = tspath::rooted_file_path_from_path(new_path.clone());
        } else {
            old_directory = tspath::rooted_directory_path_from_path(old_path.clone());
            new_directory = tspath::rooted_directory_path_from_path(new_path.clone());
            for path in baselineutil::get_accessible_file_paths(&*self.vfs, &old_directory) {
                old_file_names.insert(path, ());
            }
        }
        if old_file_names.is_empty() {
            panic!("rename source {} did not exist in test environment", old_path.as_string());
        }

        // !!! TODO: handle overwrites if we need to.
        // For each file: close if open, update script infos, write to VFS at new path, and collect file-watch events.
        let mut file_events: Vec<FileEvent> = Vec::with_capacity(old_file_names.len() * 2);
        let mut reopen_at_new_path: BTreeMap<RootedFilePath, String> = BTreeMap::new(); // newFileName -> content, for files that were open
        for old_file_name in old_file_names.keys() {
            let mut renamed_file_name = new_file_name.clone();
            if old_directory != tspath::RootedDirectoryPath::default() {
                let Some(relative) = self
                    .vfs
                    .case_sensitivity()
                    .relative_file_path_from_directory(&old_directory, old_file_name)
                else {
                    panic!("failed to compute renamed path for {}", old_file_name.as_string());
                };
                renamed_file_name = new_directory.resolve_relative_file(&relative);
            }

            // Send didClose for open files; get content from the old script info.
            if self.open_files.contains(old_file_name) {
                let content = self
                    .get_script_info_or_panic(old_file_name)
                    .content
                    .clone();
                reopen_at_new_path.insert(renamed_file_name.clone(), content);
                self.send_notification(
                    &TEXT_DOCUMENT_DID_CLOSE_INFO,
                    DidCloseTextDocumentParams {
                        text_document: TextDocumentIdentifier {
                            uri: lsconv::file_name_to_document_uri(old_file_name),
                        },
                    },
                );
                self.open_files.remove(old_file_name);
            }

            let content = self
                .get_script_info_or_panic(old_file_name)
                .content
                .clone();
            self.script_infos.insert(
                renamed_file_name.clone(),
                crate::fourslash::new_script_info_from_file_name(renamed_file_name.clone(), &content),
            );
            self.script_infos.remove(old_file_name);

            // Write renamed file to VFS.
            let Some(content) = self.vfs.read_file(old_file_name) else {
                panic!(
                "failed to read content for {} during rename to {}",
                old_file_name.as_string(),
                renamed_file_name.as_string()
            );
            };
            if let Err(err) = self.vfs.write_file(&renamed_file_name, &content) {
                panic!(
                "failed to write renamed file {}: {err}",
                renamed_file_name.as_string()
            );
            }

            file_events.push(FileEvent {
                uri: lsconv::file_name_to_document_uri(old_file_name),
                type_: FileChangeType::Deleted,
            });
            file_events.push(FileEvent {
                uri: lsconv::file_name_to_document_uri(&renamed_file_name),
                type_: FileChangeType::Created,
            });
        }

        // Remove the old path from VFS and notify the server of all file-system changes.
        if let Err(err) = self.vfs.remove(old_path) {
            panic!("failed to remove old path {}: {err}", old_path.as_string());
        }
        self.send_notification(
            &WORKSPACE_DID_CHANGE_WATCHED_FILES_INFO,
            DidChangeWatchedFilesParams {
                changes: Some(file_events),
            },
        );

        // Reopen files that were previously open at their new paths.
        for (new_file_name, content) in &reopen_at_new_path {
            self.send_notification(
                &TEXT_DOCUMENT_DID_OPEN_INFO,
                DidOpenTextDocumentParams {
                    text_document: Some(TextDocumentItem {
                        uri: lsconv::file_name_to_document_uri(new_file_name),
                        language_id: get_language_kind(new_file_name.as_string()),
                        version: 0,
                        text: content.clone(),
                    }),
                },
            );
            self.open_files.insert(new_file_name.clone());
        }

        // Update active filename if it was under the renamed path.
        if old_directory != tspath::RootedDirectoryPath::default() {
            if let Some(relative) = self
                .vfs
                .case_sensitivity()
                .relative_file_path_from_directory(&old_directory, &self.active_filename)
            {
                self.active_filename = new_directory.resolve_relative_file(&relative);
            }
        } else if self
            .vfs
            .case_sensitivity()
            .compare_file_paths(&self.active_filename, &old_file_name)
            == 0
        {
            self.active_filename = new_file_name;
        }
    }

    /// `VerifyRenameFailed`
    pub fn verify_rename_failed(&mut self, preferences: Option<&UserPreferences>) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_rename_failed_impl();
            self.configure(original);
            return;
        }
        self.verify_rename_failed_impl();
    }

    fn verify_rename_failed_impl(&mut self) {
        let params = PrepareRenameParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            position: self.current_caret_position,
            ..Default::default()
        };

        let prefix = self.get_current_position_prefix();
        self.baseline_state();
        self.baseline_request_or_notification(&TEXT_DOCUMENT_PREPARE_RENAME_INFO.method, &params);
        let (res_msg, result, _ok) = self
            .client
            .send_request(&TEXT_DOCUMENT_PREPARE_RENAME_INFO, Some(params));
        self.baseline_state();

        // prepareRename can reject via an error response (with a localized message) or a null result.
        let rejected = res_msg
            .as_ref()
            .is_some_and(|m| m.as_response().error.is_some());
        if !rejected
            && (result.range.is_some()
                || result.prepare_rename_placeholder.is_some()
                || result.prepare_rename_default_behavior.is_some())
        {
            panic!("{prefix}Expected rename to fail, but prepareRename returned a result");
        }

        // Also verify that textDocument/rename does not produce usable edits, since prepareRename is optional.
        let (rename_msg, rename_result, _ok) = self.client.send_request(
            &TEXT_DOCUMENT_RENAME_INFO,
            Some(RenameParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                new_name: "RENAME_FAILED_TEST".to_string(),
                ..Default::default()
            }),
        );
        if rename_msg
            .as_ref()
            .is_some_and(|m| m.as_response().error.is_some())
        {
            return;
        }
        if rename_result
            .workspace_edit
            .as_ref()
            .and_then(|e| e.changes.as_ref())
            .is_some_and(|c| !c.is_empty())
        {
            panic!("{prefix}prepareRename returned null but textDocument/rename returned changes");
        }
    }

    /// `MarkTestAsStradaServer`
    pub fn mark_test_as_strada_server(&mut self) {
        self.is_strada_server = true;
    }
}

/// `lookupMarkersOrGetRanges` — collects all named markers if provided, or
/// defaults to anonymous ranges.
pub(crate) fn lookup_markers_or_get_ranges(
    f: &FourslashTest,
    markers: &[String],
) -> Vec<Rc<dyn MarkerOrRange>> {
    if markers.is_empty() {
        return f
            .test_data
            .ranges
            .iter()
            .map(|r| r.clone() as Rc<dyn MarkerOrRange>)
            .collect();
    }
    markers
        .iter()
        .map(|marker_name| {
            match f.test_data.marker_positions.get(marker_name) {
                Some(m) => m.clone() as Rc<dyn MarkerOrRange>,
                None => panic!("Marker '{marker_name}' not found"),
            }
        })
        .collect()
}
