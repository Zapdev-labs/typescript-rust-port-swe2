// Ported from tsc/internal/ls/lsutil/formatcodeoptions.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.

use std::borrow::Cow;

use serde::{Deserialize, Serialize};
use tsc_core::tristate::{bool_to_tristate, TS_FALSE, TS_TRUE};
use tsc_lsproto::FormattingOptions;
use tsc_printer::get_default_indent_size;

use crate::userpreferences_generated::{EditorSettings, FormatCodeSettings};

/// `type IndentStyle int`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct IndentStyle(pub i32);

impl IndentStyle {
    /// `IndentStyleNone`
    pub const NONE: Self = Self(0);
    /// `IndentStyleBlock`
    pub const BLOCK: Self = Self(1);
    /// `IndentStyleSmart`
    pub const SMART: Self = Self(2);
}

/// `type SemicolonPreference string`
#[derive(Clone, Default, PartialEq, Eq, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct SemicolonPreference(pub Cow<'static, str>);

impl SemicolonPreference {
    /// `SemicolonPreferenceIgnore`
    pub const IGNORE: Self = Self(Cow::Borrowed("ignore"));
    /// `SemicolonPreferenceInsert`
    pub const INSERT: Self = Self(Cow::Borrowed("insert"));
    /// `SemicolonPreferenceRemove`
    pub const REMOVE: Self = Self(Cow::Borrowed("remove"));

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// `FromLSFormatOptions`
pub fn from_ls_format_options(
    f: FormatCodeSettings,
    opt: &FormattingOptions,
) -> FormatCodeSettings {
    let mut updated_settings = f;
    updated_settings.editor_settings.tab_size = opt.tab_size as i32;
    updated_settings.editor_settings.indent_size = opt.tab_size as i32;
    updated_settings.editor_settings.convert_tabs_to_spaces =
        bool_to_tristate(opt.insert_spaces);
    if let Some(trim_trailing_whitespace) = opt.trim_trailing_whitespace {
        updated_settings.editor_settings.trim_trailing_whitespace =
            bool_to_tristate(trim_trailing_whitespace);
    }
    updated_settings
}

impl FormatCodeSettings {
    /// `(settings FormatCodeSettings) ToLSFormatOptions`
    pub fn to_ls_format_options(&self) -> FormattingOptions {
        let trim_trailing_whitespace = self.editor_settings.trim_trailing_whitespace.is_true();
        FormattingOptions {
            tab_size: self.editor_settings.tab_size as u32,
            insert_spaces: self.editor_settings.convert_tabs_to_spaces.is_true(),
            trim_trailing_whitespace: Some(trim_trailing_whitespace),
            ..Default::default()
        }
    }
}

/// `GetDefaultFormatCodeSettings`
pub fn get_default_format_code_settings() -> FormatCodeSettings {
    FormatCodeSettings {
        editor_settings: EditorSettings {
            indent_size: get_default_indent_size(),
            tab_size: get_default_indent_size(),
            new_line_character: "\n".to_string(),
            convert_tabs_to_spaces: TS_TRUE,
            indent_style: IndentStyle::SMART,
            trim_trailing_whitespace: TS_TRUE,
            ..Default::default()
        },
        insert_space_after_constructor: TS_FALSE,
        insert_space_after_comma_delimiter: TS_TRUE,
        insert_space_after_semicolon_in_for_statements: TS_TRUE,
        insert_space_before_and_after_binary_operators: TS_TRUE,
        insert_space_after_keywords_in_control_flow_statements: TS_TRUE,
        insert_space_after_function_keyword_for_anonymous_functions: TS_FALSE,
        insert_space_after_opening_and_before_closing_nonempty_parenthesis: TS_FALSE,
        insert_space_after_opening_and_before_closing_nonempty_brackets: TS_FALSE,
        insert_space_after_opening_and_before_closing_nonempty_braces: TS_TRUE,
        insert_space_after_opening_and_before_closing_template_string_braces: TS_FALSE,
        insert_space_after_opening_and_before_closing_jsx_expression_braces: TS_FALSE,
        insert_space_before_function_parenthesis: TS_FALSE,
        place_open_brace_on_new_line_for_functions: TS_FALSE,
        place_open_brace_on_new_line_for_control_blocks: TS_FALSE,
        semicolons: SemicolonPreference::IGNORE,
        indent_switch_case: TS_TRUE,
        ..Default::default()
    }
}
