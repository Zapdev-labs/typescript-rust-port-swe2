// Ported from tsc/internal/ls/lsutil/userpreferences_test.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.
//
// PORT: `map[string]any` configs are `serde_json::Map<String, Value>` built
// via `json!`; `assert.DeepEqual` is `assert_eq!` (`PartialEq`); the
// reflect-based `fillNonZeroValues` is a hand-written constructor that sets
// every field to the same non-zero value the Go helper would (Tristate→
// TS_TRUE, ints→1, strings→type-appropriate valid strings, []string→["test"]).

use serde_json::{Map, Value, json};
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN};
use tsc_modulespecifiers::{
    ImportModuleSpecifierEndingPreference, ImportModuleSpecifierPreference,
};

use crate::formatcodeoptions::{IndentStyle, SemicolonPreference};
use crate::userpreferences::{
    IncludeInlayParameterNameHints, JsxAttributeCompletionStyle, OrganizeImportsCaseFirst,
    OrganizeImportsCollation, OrganizeImportsSort, OrganizeImportsTypeOrder, QuotePreference,
    WorkspaceSymbolsScope, new_default_user_preferences, parse_user_preferences,
};
use crate::userpreferences_generated::{
    CodeLensUserPreferences, CompletionPreferences, EditorSettings, FormatCodeSettings,
    InlayHintsPreferences, UserPreferences,
};

fn obj(v: Value) -> Map<String, Value> {
    v.as_object().unwrap().clone()
}

#[test]
fn test_user_preferences_parsing_edge_cases() {
    struct Case {
        name: &'static str,
        config: Map<String, Value>,
        expected: fn(&mut UserPreferences),
    }
    let tests = [
        Case {
            name: "null raw values leave preferences unchanged",
            config: obj(json!({
                "quotePreference": null,
                "maximumHoverLength": null,
                "includeCompletionsForModuleExports": null,
            })),
            expected: |_| {},
        },
        Case {
            name: "invalid boolean becomes unknown",
            config: obj(json!({"includeCompletionsForModuleExports": "invalid"})),
            expected: |p| {
                p.completion_preferences
                    .include_completions_for_module_exports = TS_UNKNOWN;
            },
        },
        Case {
            name: "case-insensitive enums",
            config: obj(json!({
                "quotePreference": "SINGLE",
                "jsxAttributeCompletionStyle": "BRACES",
                "organizeImportsCaseFirst": "LOWER",
                "includeInlayParameterNameHints": "ALL",
                "organizeImportsTypeOrder": "FIRST",
                "workspaceSymbolsScope": "CURRENTPROJECT",
            })),
            expected: |p| {
                p.quote_preference = QuotePreference::SINGLE;
                p.completion_preferences.jsx_attribute_completion_style =
                    JsxAttributeCompletionStyle::BRACES;
                p.organize_imports_case_first = OrganizeImportsCaseFirst::LOWER;
                p.inlay_hints_preferences.include_inlay_parameter_name_hints =
                    IncludeInlayParameterNameHints::ALL;
                p.organize_imports_type_order = OrganizeImportsTypeOrder::FIRST;
                p.workspace_symbols_scope = WorkspaceSymbolsScope::CURRENT_PROJECT;
            },
        },
        Case {
            name: "present null primary path prevents fallback",
            config: obj(json!({
                "suggest": {"jsdoc": {"enabled": null}, "completeJSDocs": false},
            })),
            expected: |_| {},
        },
        Case {
            name: "null case sensitivity becomes unknown",
            config: obj(json!({
                "preferences": {"organizeImports": {"caseSensitivity": null}},
            })),
            expected: |p| {
                p.organize_imports_ignore_case = TS_UNKNOWN;
            },
        },
        Case {
            name: "numeric conversion and array filtering",
            config: obj(json!({
                "maximumHoverLength": 9.8,
                "indentStyle": 1.7,
                "autoImportFileExcludePatterns": ["first", false, 3, "second"],
            })),
            expected: |p| {
                p.maximum_hover_length = 9;
                p.format_code_settings.editor_settings.indent_style = IndentStyle::BLOCK;
                p.auto_import_file_exclude_patterns =
                    vec!["first".to_string(), "second".to_string()];
            },
        },
        Case {
            name: "empty array is not nil",
            config: obj(json!({"autoImportFileExcludePatterns": []})),
            expected: |p| {
                p.auto_import_file_exclude_patterns = Vec::new();
            },
        },
        Case {
            name: "invalid module specifier preference uses its default",
            config: obj(json!({"importModuleSpecifierPreference": true})),
            expected: |p| {
                p.import_module_specifier_preference = ImportModuleSpecifierPreference::SHORTEST;
            },
        },
    ];
    for test in tests {
        let mut base = new_default_user_preferences();
        base.quote_preference = QuotePreference::DOUBLE;
        base.maximum_hover_length = 17;
        base.organize_imports_ignore_case = TS_TRUE;
        let mut expected = base.clone();
        (test.expected)(&mut expected);
        assert_eq!(base.with_config(&test.config), expected, "{}", test.name);
    }
}

/// `fillNonZeroValues` — every field set to a non-zero value, mirroring the
/// Go reflection loop (`reflect.Bool`→true, ints→1, strings→valid enum
/// strings or "test", []string→["test"], struct→recurse).
fn filled_user_preferences() -> UserPreferences {
    UserPreferences {
        format_code_settings: FormatCodeSettings {
            editor_settings: EditorSettings {
                base_indent_size: 1,
                convert_tabs_to_spaces: TS_TRUE,
                indent_size: 1,
                indent_style: IndentStyle(1), // IndentStyleBlock
                new_line_character: "test".to_string(),
                tab_size: 1,
                trim_trailing_whitespace: TS_TRUE,
            },
            indent_multi_line_object_literal_beginning_on_blank_line: TS_TRUE,
            indent_switch_case: TS_TRUE,
            insert_space_after_comma_delimiter: TS_TRUE,
            insert_space_after_constructor: TS_TRUE,
            insert_space_after_function_keyword_for_anonymous_functions: TS_TRUE,
            insert_space_after_keywords_in_control_flow_statements: TS_TRUE,
            insert_space_after_opening_and_before_closing_empty_braces: TS_TRUE,
            insert_space_after_opening_and_before_closing_jsx_expression_braces: TS_TRUE,
            insert_space_after_opening_and_before_closing_nonempty_braces: TS_TRUE,
            insert_space_after_opening_and_before_closing_nonempty_brackets: TS_TRUE,
            insert_space_after_opening_and_before_closing_nonempty_parenthesis: TS_TRUE,
            insert_space_after_opening_and_before_closing_template_string_braces: TS_TRUE,
            insert_space_after_semicolon_in_for_statements: TS_TRUE,
            insert_space_after_type_assertion: TS_TRUE,
            insert_space_before_and_after_binary_operators: TS_TRUE,
            insert_space_before_function_parenthesis: TS_TRUE,
            insert_space_before_type_annotation: TS_TRUE,
            place_open_brace_on_new_line_for_control_blocks: TS_TRUE,
            place_open_brace_on_new_line_for_functions: TS_TRUE,
            semicolons: SemicolonPreference::INSERT,
        },
        completion_preferences: CompletionPreferences {
            include_automatic_optional_chain_completions: TS_TRUE,
            include_completions_for_import_statements: TS_TRUE,
            include_completions_for_module_exports: TS_TRUE,
            include_completions_with_class_member_snippets: TS_TRUE,
            include_completions_with_object_literal_method_snippets: TS_TRUE,
            jsx_attribute_completion_style: JsxAttributeCompletionStyle::BRACES,
        },
        inlay_hints_preferences: InlayHintsPreferences {
            include_inlay_enum_member_value_hints: TS_TRUE,
            include_inlay_function_like_return_type_hints: TS_TRUE,
            include_inlay_function_parameter_type_hints: TS_TRUE,
            include_inlay_parameter_name_hints: IncludeInlayParameterNameHints::ALL,
            include_inlay_parameter_name_hints_when_argument_matches_name: TS_TRUE,
            include_inlay_property_declaration_type_hints: TS_TRUE,
            include_inlay_variable_type_hints: TS_TRUE,
            include_inlay_variable_type_hints_when_type_matches_name: TS_TRUE,
        },
        code_lens_user_preferences: CodeLensUserPreferences {
            implementations_code_lens_enabled: TS_TRUE,
            implementations_code_lens_show_on_all_class_methods: TS_TRUE,
            implementations_code_lens_show_on_interface_methods: TS_TRUE,
            references_code_lens_enabled: TS_TRUE,
            references_code_lens_show_on_all_functions: TS_TRUE,
        },
        allow_rename_of_import_path: TS_TRUE,
        allow_text_changes_in_new_files: TS_TRUE,
        auto_closing_tags: TS_TRUE,
        auto_import_entrypoint_directory_search: TS_TRUE,
        auto_import_file_exclude_patterns: vec!["test".to_string()],
        auto_import_specifier_exclude_regexes: vec!["test".to_string()],
        automatic_type_acquisition_enabled: TS_TRUE,
        complete_jsdocs: TS_TRUE,
        custom_config_file_name: "test".to_string(),
        disable_automatic_type_acquisition: TS_TRUE,
        disable_line_text_in_references: TS_TRUE,
        disable_suggestions: TS_TRUE,
        display_parts_for_jsdoc: TS_TRUE,
        exclude_library_symbols_in_nav_to: TS_TRUE,
        format_enabled: TS_TRUE,
        generate_return_in_doc_template: TS_TRUE,
        import_module_specifier_ending: ImportModuleSpecifierEndingPreference::JS,
        import_module_specifier_preference: ImportModuleSpecifierPreference::RELATIVE,
        lazy_configured_projects_from_external_project: TS_TRUE,
        locale: "test".to_string(),
        maximum_hover_length: 1,
        organize_imports_accent_collation: TS_TRUE,
        organize_imports_case_first: OrganizeImportsCaseFirst(1), // OrganizeImportsCaseFirstLower
        organize_imports_collation: OrganizeImportsCollation(true), // unicode
        organize_imports_ignore_case: TS_TRUE,
        organize_imports_locale: "test".to_string(),
        organize_imports_numeric_collation: TS_TRUE,
        organize_imports_sort: OrganizeImportsSort(1), // OrganizeImportsSortOrdinal
        organize_imports_type_order: OrganizeImportsTypeOrder(1), // OrganizeImportsTypeOrderLast
        prefer_go_to_source_definition: true,
        prefer_type_only_auto_imports: TS_TRUE,
        provide_prefix_and_suffix_text_for_rename: TS_TRUE,
        provide_refactor_not_applicable_reason: TS_TRUE,
        quote_preference: QuotePreference::SINGLE,
        report_style_checks_as_warnings: TS_TRUE,
        validate_enabled: TS_TRUE,
        workspace_symbols_scope: WorkspaceSymbolsScope::ALL_OPEN_PROJECTS,
    }
}

#[test]
fn test_user_preferences_roundtrip() {
    let original = filled_user_preferences();

    let json_bytes = serde_json::to_vec(&original).unwrap();

    // `UnmarshalJSONFrom`
    let parsed: UserPreferences = serde_json::from_slice(&json_bytes).unwrap();
    assert_eq!(original, parsed, "UnmarshalJSONFrom round-trip");

    // `withConfig`
    let config: Map<String, Value> = serde_json::from_slice(&json_bytes).unwrap();
    let parsed = UserPreferences::default().with_config(&config);
    assert_eq!(original, parsed, "withConfig round-trip");
}

#[test]
fn test_user_preferences_serialize() {
    // config path field serializes to nested path
    {
        let prefs = UserPreferences {
            quote_preference: QuotePreference::SINGLE,
            ..Default::default()
        };
        let json_bytes = serde_json::to_vec(&prefs).unwrap();
        let actual: Map<String, Value> = serde_json::from_slice(&json_bytes).unwrap();
        let preferences = actual["preferences"].as_object().unwrap();
        assert_eq!(preferences["quoteStyle"], json!("single"));
    }

    // raw-only field serializes to unstable section
    {
        let prefs = UserPreferences {
            disable_suggestions: TS_TRUE,
            ..Default::default()
        };
        let json_bytes = serde_json::to_vec(&prefs).unwrap();
        let actual: Map<String, Value> = serde_json::from_slice(&json_bytes).unwrap();
        let unstable = actual["unstable"].as_object().unwrap();
        assert_eq!(unstable["disableSuggestions"], json!(true));
    }

    // inlay hint inversion on serialize
    {
        let prefs = UserPreferences {
            inlay_hints_preferences: InlayHintsPreferences {
                include_inlay_parameter_name_hints: IncludeInlayParameterNameHints::ALL,
                include_inlay_parameter_name_hints_when_argument_matches_name: TS_TRUE,
                ..Default::default()
            },
            ..Default::default()
        };
        let json_bytes = serde_json::to_vec(&prefs).unwrap();
        let actual: Map<String, Value> = serde_json::from_slice(&json_bytes).unwrap();
        let inlay_hints = actual["inlayHints"].as_object().unwrap();
        let parameter_names = inlay_hints["parameterNames"].as_object().unwrap();
        assert_eq!(parameter_names["enabled"], json!("all"));
        assert_eq!(
            parameter_names["suppressWhenArgumentMatchesName"],
            json!(false)
        ); // inverted
    }

    // mixed config and unstable fields
    {
        let prefs = UserPreferences {
            quote_preference: QuotePreference::SINGLE,
            disable_suggestions: TS_TRUE,
            display_parts_for_jsdoc: TS_TRUE,
            ..Default::default()
        };
        let json_bytes = serde_json::to_vec(&prefs).unwrap();
        let actual: Map<String, Value> = serde_json::from_slice(&json_bytes).unwrap();
        let preferences = actual["preferences"].as_object().unwrap();
        assert_eq!(preferences["quoteStyle"], json!("single"));
        let unstable = actual["unstable"].as_object().unwrap();
        assert_eq!(unstable["disableSuggestions"], json!(true));
        assert_eq!(unstable["displayPartsForJSDoc"], json!(true));
    }
}

#[test]
fn test_user_preferences_parse_unstable() {
    let tests: &[(&str, &str, UserPreferences)] = &[
        (
            "unstable fields with correct casing",
            r#"{
                "unstable": {
                    "disableSuggestions": true,
                    "maximumHoverLength": 100,
                    "allowRenameOfImportPath": true
                }
            }"#,
            UserPreferences {
                disable_suggestions: TS_TRUE,
                maximum_hover_length: 100,
                allow_rename_of_import_path: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "nested preferences path",
            r#"{
                "preferences": {
                    "quoteStyle": "single",
                    "useAliasesForRenames": true
                }
            }"#,
            UserPreferences {
                quote_preference: QuotePreference::SINGLE,
                provide_prefix_and_suffix_text_for_rename: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "suggest section",
            r#"{
                "suggest": {
                    "autoImports": false,
                    "includeCompletionsForImportStatements": true
                }
            }"#,
            UserPreferences {
                completion_preferences: CompletionPreferences {
                    include_completions_for_module_exports: TS_FALSE,
                    include_completions_for_import_statements: TS_TRUE,
                    ..Default::default()
                },
                ..Default::default()
            },
        ),
        (
            "inlayHints with invert",
            r#"{
                "inlayHints": {
                    "parameterNames": {
                        "enabled": "all",
                        "suppressWhenArgumentMatchesName": true
                    }
                }
            }"#,
            UserPreferences {
                inlay_hints_preferences: InlayHintsPreferences {
                    include_inlay_parameter_name_hints: IncludeInlayParameterNameHints::ALL,
                    include_inlay_parameter_name_hints_when_argument_matches_name: TS_FALSE, // inverted
                    ..Default::default()
                },
                ..Default::default()
            },
        ),
        (
            "mixed config",
            r#"{
                "unstable": {
                    "displayPartsForJSDoc": true
                },
                "preferences": {
                    "importModuleSpecifier": "relative"
                },
                "workspaceSymbols": {
                    "excludeLibrarySymbols": true,
                    "scope": "currentProject"
                }
            }"#,
            UserPreferences {
                display_parts_for_jsdoc: TS_TRUE,
                import_module_specifier_preference: ImportModuleSpecifierPreference::RELATIVE,
                exclude_library_symbols_in_nav_to: TS_TRUE,
                workspace_symbols_scope: WorkspaceSymbolsScope::CURRENT_PROJECT,
                ..Default::default()
            },
        ),
        (
            "stable config overrides unstable",
            r#"{
                "unstable": {
                    "quotePreference": "double"
                },
                "preferences": {
                    "quoteStyle": "single"
                }
            }"#,
            UserPreferences {
                quote_preference: QuotePreference::SINGLE, // stable wins
                ..Default::default()
            },
        ),
        (
            "unstable sets value when no stable config",
            r#"{
                "unstable": {
                    "includeAutomaticOptionalChainCompletions": false
                }
            }"#,
            UserPreferences {
                completion_preferences: CompletionPreferences {
                    include_automatic_optional_chain_completions: TS_FALSE,
                    ..Default::default()
                },
                ..Default::default()
            },
        ),
        (
            "any field can be passed via unstable by its raw name",
            r#"{
                "unstable": {
                    "quotePreference": "double",
                    "includeCompletionsForModuleExports": true,
                    "excludeLibrarySymbolsInNavTo": true
                }
            }"#,
            UserPreferences {
                quote_preference: QuotePreference::DOUBLE,
                completion_preferences: CompletionPreferences {
                    include_completions_for_module_exports: TS_TRUE,
                    ..Default::default()
                },
                exclude_library_symbols_in_nav_to: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "TypeScript raw names work in unstable section",
            r#"{
                "unstable": {
                    "includeCompletionsForModuleExports": true,
                    "quotePreference": "single",
                    "providePrefixAndSuffixTextForRename": true,
                    "includeInlayParameterNameHints": "all",
                    "organizeImportsLocale": "en"
                }
            }"#,
            UserPreferences {
                completion_preferences: CompletionPreferences {
                    include_completions_for_module_exports: TS_TRUE,
                    ..Default::default()
                },
                quote_preference: QuotePreference::SINGLE,
                provide_prefix_and_suffix_text_for_rename: TS_TRUE,
                organize_imports_locale: "en".to_string(),
                inlay_hints_preferences: InlayHintsPreferences {
                    include_inlay_parameter_name_hints: IncludeInlayParameterNameHints::ALL,
                    ..Default::default()
                },
                ..Default::default()
            },
        ),
        (
            "old raw organize imports unicode preferences load as raw state",
            r#"{
                "unstable": {
                    "organizeImportsCollation": "unicode",
                    "organizeImportsCaseFirst": "upper",
                    "organizeImportsIgnoreCase": false,
                    "organizeImportsNumericCollation": true
                }
            }"#,
            UserPreferences {
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_case_first: OrganizeImportsCaseFirst::UPPER,
                organize_imports_ignore_case: TS_FALSE,
                organize_imports_numeric_collation: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "old top-level raw organize imports unicode preferences load as raw state",
            r#"{
                "organizeImportsCollation": "unicode",
                "organizeImportsIgnoreCase": true
            }"#,
            UserPreferences {
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "new top-level raw organize imports sort is accepted",
            r#"{
                "organizeImportsSort": "natural"
            }"#,
            UserPreferences {
                organize_imports_sort: OrganizeImportsSort::NATURAL,
                ..Default::default()
            },
        ),
        (
            "old raw organize imports ignore case loads as raw state",
            r#"{
                "unstable": {
                    "organizeImportsIgnoreCase": true
                }
            }"#,
            UserPreferences {
                organize_imports_ignore_case: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "new raw organize imports sort loads alongside old raw preferences",
            r#"{
                "unstable": {
                    "organizeImportsSort": "ordinal",
                    "organizeImportsCollation": "unicode",
                    "organizeImportsIgnoreCase": true
                }
            }"#,
            UserPreferences {
                organize_imports_sort: OrganizeImportsSort::ORDINAL,
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_TRUE,
                ..Default::default()
            },
        ),
        (
            "old nested organize imports unicode preferences load as raw state",
            r#"{
                "preferences": {
                    "organizeImports": {
                        "unicodeCollation": "unicode",
                        "caseSensitivity": "caseSensitive",
                        "numericCollation": true,
                        "caseFirst": "upper"
                    }
                }
            }"#,
            UserPreferences {
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_FALSE,
                organize_imports_numeric_collation: TS_TRUE,
                organize_imports_case_first: OrganizeImportsCaseFirst::UPPER,
                ..Default::default()
            },
        ),
        (
            "new nested organize imports sort loads alongside old nested preferences",
            r#"{
                "preferences": {
                    "organizeImports": {
                        "sort": "ordinalIgnoreCase",
                        "unicodeCollation": "unicode",
                        "caseSensitivity": "caseSensitive"
                    }
                }
            }"#,
            UserPreferences {
                organize_imports_sort: OrganizeImportsSort::ORDINAL_IGNORE_CASE,
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_FALSE,
                ..Default::default()
            },
        ),
    ];

    for (name, json_text, expected) in tests {
        let config: Map<String, Value> = serde_json::from_str(json_text).unwrap();
        let parsed = UserPreferences::default().with_config(&config);
        assert_eq!(*expected, parsed, "{name}");
    }
}

#[test]
fn test_user_preferences_locale() {
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {"locale": "de"},
        "js/ts": {"locale": "fr"},
    })));

    assert_eq!(prefs.locale, "fr");
}

#[test]
fn test_user_preferences_report_style_checks_as_warnings() {
    // reportStyleChecksAsWarnings via config path
    let prefs = parse_user_preferences(&obj(json!({
        "js/ts": {"reportStyleChecksAsWarnings": false},
    })));
    assert_eq!(prefs.report_style_checks_as_warnings, TS_FALSE);

    // reportStyleChecksAsWarnings defaults to true
    let prefs = new_default_user_preferences();
    assert_eq!(prefs.report_style_checks_as_warnings, TS_TRUE);

    // reportStyleChecksAsWarnings via unstable section
    let prefs = parse_user_preferences(&obj(json!({
        "js/ts": {"unstable": {"reportStyleChecksAsWarnings": false}},
    })));
    assert_eq!(prefs.report_style_checks_as_warnings, TS_FALSE);
}

#[test]
fn test_user_preferences_parse_server_feature_preferences() {
    // preferred server feature settings
    let prefs = parse_user_preferences(&obj(json!({
        "js/ts": {
            "validate": {"enabled": false},
            "format": {"enabled": false},
            "autoClosingTags": {"enabled": false},
        },
    })));
    assert_eq!(prefs.validate_enabled, TS_FALSE);
    assert_eq!(prefs.format_enabled, TS_FALSE);
    assert_eq!(prefs.auto_closing_tags, TS_FALSE);

    // legacy server feature fallbacks
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {
            "validate": {"enable": false},
            "format": {"enable": false},
            "autoClosingTags": false,
        },
    })));
    assert_eq!(prefs.validate_enabled, TS_FALSE);
    assert_eq!(prefs.format_enabled, TS_FALSE);
    assert_eq!(prefs.auto_closing_tags, TS_FALSE);

    // preferred settings take precedence over fallbacks
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {
            "validate": {"enable": false},
            "format": {"enable": false},
            "autoClosingTags": false,
        },
        "js/ts": {
            "validate": {"enabled": true},
            "format": {"enabled": true},
            "autoClosingTags": {"enabled": true},
        },
    })));
    assert_eq!(prefs.validate_enabled, TS_TRUE);
    assert_eq!(prefs.format_enabled, TS_TRUE);
    assert_eq!(prefs.auto_closing_tags, TS_TRUE);
}

#[test]
fn test_parse_user_preferences_editor_formatting() {
    let prefs = parse_user_preferences(&obj(json!({
        "editor": {
            "tabSize": 2,
            "insertSpaces": false,
        },
    })));

    assert_eq!(prefs.format_code_settings.editor_settings.tab_size, 2);
    assert_eq!(prefs.format_code_settings.editor_settings.indent_size, 2);
    assert_eq!(
        prefs
            .format_code_settings
            .editor_settings
            .convert_tabs_to_spaces,
        TS_FALSE
    );
}

#[test]
fn test_user_preferences_parse_jsdoc_completion_preferences() {
    // unified jsdoc enabled setting
    let prefs = parse_user_preferences(&obj(json!({
        "js/ts": {"suggest": {"jsdoc": {"enabled": false}}},
    })));
    assert_eq!(prefs.complete_jsdocs, TS_FALSE);

    // language fallback completeJSDocs setting
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {"suggest": {"completeJSDocs": false}},
    })));
    assert_eq!(prefs.complete_jsdocs, TS_FALSE);

    // unified jsdoc enabled takes precedence over language fallback
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {"suggest": {"completeJSDocs": false}},
        "js/ts": {"suggest": {"jsdoc": {"enabled": true}}},
    })));
    assert_eq!(prefs.complete_jsdocs, TS_TRUE);

    // unified jsdoc generateReturns setting
    let prefs = parse_user_preferences(&obj(json!({
        "js/ts": {"suggest": {"jsdoc": {"generateReturns": false}}},
    })));
    assert_eq!(prefs.generate_return_in_doc_template, TS_FALSE);

    // language jsdoc generateReturns setting
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {"suggest": {"jsdoc": {"generateReturns": false}}},
    })));
    assert_eq!(prefs.generate_return_in_doc_template, TS_FALSE);
}

#[test]
fn test_user_preferences_parse_ata() {
    // ParseUserPreferences with unified ATA setting in js/ts section
    let prefs = parse_user_preferences(&obj(json!({
        "js/ts": {"tsserver": {"automaticTypeAcquisition": {"enabled": false}}},
    })));
    assert!(prefs.is_ata_disabled());
    assert_eq!(prefs.automatic_type_acquisition_enabled, TS_FALSE);

    // ParseUserPreferences with deprecated disableAutomaticTypeAcquisition in typescript section
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {"disableAutomaticTypeAcquisition": true},
    })));
    assert!(prefs.is_ata_disabled());
    assert_eq!(prefs.disable_automatic_type_acquisition, TS_TRUE);

    // unified setting takes precedence over deprecated setting
    let prefs = parse_user_preferences(&obj(json!({
        "typescript": {"disableAutomaticTypeAcquisition": true},
        "js/ts": {"tsserver": {"automaticTypeAcquisition": {"enabled": true}}},
    })));
    assert!(!prefs.is_ata_disabled());
    assert_eq!(prefs.automatic_type_acquisition_enabled, TS_TRUE);

    // IsATADisabled returns false when neither setting is configured
    let prefs = new_default_user_preferences();
    assert!(!prefs.is_ata_disabled());
}
