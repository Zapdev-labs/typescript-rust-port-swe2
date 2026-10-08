// Ported from tsc/internal/tsoptions/tsconfigparsing_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use crate::tsconfigparsing::{
    new_tsconfig_source_file_from_file_path, parse_config_file_text_to_json,
    parse_json_config_file_content, parse_json_source_file_config_file_content,
};
use crate::value::Value;
use tsc_collections::OrderedMap;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, to_rooted_file_path};
use tsc_vfs::vfstest;

fn value_map(entries: Vec<(&str, Value)>) -> Value {
    let mut map = OrderedMap::new();
    for (k, v) in entries {
        map.set(k.to_string(), v);
    }
    Value::Map(map)
}

/// `TestParseConfigFileTextToJson` (single representation check).
#[test]
fn test_parse_config_file_text_to_json() {
    // `parseConfigFileTextToJsonTests`.
    let tests: &[(&str, &[&str])] = &[
        (
            "returns empty config for file with only whitespaces",
            &["", " "],
        ),
        (
            "returns empty config for file with comments only",
            &["// Comment", "/* Comment*/"],
        ),
        ("returns empty config when config is empty object", &["{}"]),
        (
            "returns config object without comments",
            &[
                r#"{ // Excluded files
            "exclude": [
                // Exclude d.ts
                "file.d.ts"
            ]
        }"#,
                r#"{
            /* Excluded
                    Files
            */
            "exclude": [
                /* multiline comments can be in the middle of a line */"file.d.ts"
            ]
        }"#,
            ],
        ),
        (
            "keeps string content untouched",
            &[
                r#"{
            "exclude": [
                "xx//file.d.ts"
            ]
        }"#,
                r#"{
            "exclude": [
                "xx/*file.d.ts*/"
            ]
        }"#,
            ],
        ),
        (
            "handles escaped characters in strings correctly",
            &[
                r#"{
            "exclude": [
                "xx\"//files"
            ]
        }"#,
                r#"{
            "exclude": [
                "xx\\" // end of line comment
            ]
        }"#,
            ],
        ),
        (
            "returns object when users correctly specify library",
            &[
                r#"{
            "compilerOptions": {
                "lib": ["es5"]
            }
        }"#,
                r#"{
            "compilerOptions": {
                "lib": ["es5", "es6"]
            }
        }"#,
            ],
        ),
    ];
    for (title, inputs) in tests {
        let mut baseline_content = String::new();
        for (i, json_text) in inputs.iter().enumerate() {
            baseline_content.push_str("Input::\n");
            baseline_content.push_str(json_text);
            baseline_content.push('\n');
            let (parsed, errors) = parse_config_file_text_to_json(
                RootedFilePath::from("/apath/tsconfig.json"),
                "/apath".into(),
                json_text,
            );
            baseline_content.push_str("Config::\n");
            let mut buf = Vec::new();
            tsc_json::marshal_indent_write(&mut buf, &parsed, "", "  ")
                .expect("marshal config json");
            baseline_content.push_str(std::str::from_utf8(&buf).unwrap());
            baseline_content.push('\n');
            baseline_content.push_str("Errors::\n");
            let diags = tsc_diagnosticwriter::from_ast_diagnostics(&errors, &[]);
            let mut out = Vec::new();
            tsc_diagnosticwriter::format_diagnostics_with_color_and_context(
                &mut out,
                &diags,
                &FormattingOptions {
                    new_line: "\n".into(),
                    current_directory: RootedDirectoryPath::from("/"),
                    case_sensitivity: CaseSensitivity::CaseSensitive,
                    ..Default::default()
                },
            );
            baseline_content.push_str(std::str::from_utf8(&out).unwrap());
            baseline_content.push('\n');
            if i != inputs.len() - 1 {
                baseline_content.push('\n');
            }
        }
        tsc_testutil::baseline::run(
            &format!("{title} jsonParse.js"),
            &baseline_content,
            &tsc_testutil::baseline::Options {
                subfolder: "config/tsconfigParsing".into(),
                ..Default::default()
            },
        )
        .expect("baseline");
    }
}

/// `TestParseJsonConfigFileContentAcceptsJsonRepresentations`.
#[test]
fn test_parse_json_config_file_content_accepts_json_representations() {
    let fs = vfstest::from_map(
        [("/project/index.ts", "export {};")],
        CaseSensitivity::CaseSensitive,
    );
    let base_path = RootedDirectoryPath::from("/project");
    let config_file_name = RootedFilePath::from("/project/tsconfig.json");

    let (ordered_map, parse_errors) = parse_config_file_text_to_json(
        config_file_name.clone(),
        config_file_name.as_string().into(),
        r#"{"compilerOptions":{"strict":true},"files":["index.ts"]}"#,
    );
    assert_eq!(parse_errors.len(), 0);

    let mut compiler_options = OrderedMap::new();
    compiler_options.set("strict".to_string(), Value::Bool(true));
    let mut ordered_map_with_typed_slices = OrderedMap::new();
    ordered_map_with_typed_slices.set(
        "compilerOptions".to_string(),
        Value::GoMap(compiler_options.clone()),
    );
    ordered_map_with_typed_slices.set(
        "files".to_string(),
        Value::StringList(vec!["index.ts".into()]),
    );

    let mut plain_compiler_options = OrderedMap::new();
    plain_compiler_options.set("strict".to_string(), Value::Bool(true));

    let tests: Vec<(&str, Value)> = vec![
        ("ordered map", ordered_map),
        (
            "ordered map with typed slices",
            Value::Map(ordered_map_with_typed_slices),
        ),
        (
            "plain map",
            value_map(vec![
                (
                    "compilerOptions",
                    Value::GoMap(plain_compiler_options.clone()),
                ),
                ("files", Value::List(vec![Value::Str("index.ts".into())])),
            ]),
        ),
        (
            "typed slices",
            value_map(vec![
                ("compilerOptions", Value::GoMap(plain_compiler_options)),
                ("files", Value::StringList(vec!["index.ts".into()])),
            ]),
        ),
    ];
    for (name, json) in tests {
        let parsed = parse_json_config_file_content(
            &json,
            &fs,
            base_path.clone(),
            None,
            config_file_name.clone(),
            &[],
            None,
        );
        assert_eq!(
            parsed.file_names(),
            &[RootedFilePath::from("/project/index.ts")],
            "{name}"
        );
        assert!(
            parsed
                .compiler_options()
                .is_some_and(|o| o.strict.is_true()),
            "{name}"
        );
        assert_eq!(
            parsed
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .len(),
            0,
            "{name}"
        );
    }
}

/// `TestParseJsonConfigFileContentHandlesNullArrayElements`.
#[test]
fn test_parse_json_config_file_content_handles_null_array_elements() {
    let fs = vfstest::from_map(
        [("/project/index.ts", "export {};")],
        CaseSensitivity::CaseSensitive,
    );
    for property in ["files", "include", "exclude"] {
        let json = value_map(vec![(property, Value::List(vec![Value::Null]))]);
        let parsed = parse_json_config_file_content(
            &json,
            &fs,
            RootedDirectoryPath::from("/project"),
            None,
            RootedFilePath::from("/project/tsconfig.json"),
            &[],
            None,
        );
        let errors = parsed.errors.lock().unwrap_or_else(|e| e.into_inner());
        assert!(!errors.is_empty(), "{property}");
        assert_eq!(
            errors[0].lock().unwrap_or_else(|e| e.into_inner()).code(),
            tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1.code(),
            "{property}"
        );
    }
}

/// `TestParseJsonConfigFileContentDefaultsCompileOnSaveToFalse`.
#[test]
fn test_parse_json_config_file_content_defaults_compile_on_save_to_false() {
    let fs = vfstest::from_map(
        [("/project/index.ts", "export {};")],
        CaseSensitivity::CaseSensitive,
    );
    let parsed = parse_json_config_file_content(
        &value_map(vec![(
            "files",
            Value::List(vec![Value::Str("index.ts".into())]),
        )]),
        &fs,
        RootedDirectoryPath::from("/project"),
        None,
        RootedFilePath::from("/project/tsconfig.json"),
        &[],
        None,
    );
    assert_eq!(parsed.compile_on_save, Some(false));
}

/// `TestParseNullEnumCompilerOptions`.
#[test]
fn test_parse_null_enum_compiler_options() {
    let json_text = r#"{
        "compilerOptions": {
            "target": null,
            "module": null
        }
    }"#;
    let base_path = RootedDirectoryPath::from("/");

    let make_fs = || {
        vfstest::from_map(
            [("/app.ts", ""), ("/tsconfig.json", json_text)],
            CaseSensitivity::CaseSensitive,
        )
    };

    // json api
    let fs = make_fs();
    let config_file_name = to_rooted_file_path("tsconfig.json", &base_path);
    let path = fs.case_sensitivity().path_key(&config_file_name.as_path());
    let (json, _) = parse_config_file_text_to_json(config_file_name.clone(), path, json_text);
    let parsed = parse_json_config_file_content(
        &json,
        &fs,
        base_path.clone(),
        None,
        config_file_name,
        &[],
        None,
    );
    assert_eq!(
        parsed
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len(),
        0
    );

    // jsonSourceFile api
    let fs = make_fs();
    let config_file_name = RootedFilePath::from("/tsconfig.json");
    let path = fs.case_sensitivity().path_key(&config_file_name.as_path());
    let source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name,
        path,
        json_text,
    ));
    let parsed = parse_json_source_file_config_file_content(
        &source_file,
        &fs,
        base_path,
        None,
        None,
        &[],
        None,
    );
    assert_eq!(
        parsed
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len(),
        0
    );
}

/// `TestParseJsonConfigFileContentPreservesRaw`.
#[test]
fn test_parse_json_config_file_content_preserves_raw() {
    let fs = vfstest::from_map(
        [("/project/index.ts", "export {};")],
        CaseSensitivity::CaseSensitive,
    );
    let parsed = parse_json_config_file_content(
        &value_map(vec![
            (
                "customSetting",
                value_map(vec![("enabled", Value::Bool(true))]),
            ),
            ("compileOnSave", Value::Bool(true)),
            ("files", Value::List(vec![Value::Str("index.ts".into())])),
        ]),
        &fs,
        RootedDirectoryPath::from("/project"),
        None,
        RootedFilePath::from("/project/tsconfig.json"),
        &[],
        None,
    );
    assert_eq!(
        parsed
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len(),
        0
    );
    assert_eq!(parsed.compile_on_save, Some(true));

    let raw = parsed
        .raw
        .as_ref()
        .and_then(Value::as_map)
        .expect("raw map");
    let keys: Vec<&str> = raw.keys().map(String::as_str).collect();
    assert_eq!(keys, ["customSetting", "compileOnSave", "files"]);
    assert!(raw.has("customSetting"));
}

/// `TestCustomConditionsNullOverride`.
#[test]
fn test_custom_conditions_null_override() {
    use crate::commandlineparser::parse_command_line;
    use crate::tsconfigparsing::get_parsed_command_line_of_config_file;

    let fs = vfstest::from_map(
        [
            (
                "/project/tsconfig.json",
                r#"{
  "compilerOptions": {
    "customConditions": ["condition1", "condition2"]
  }
}"#,
            ),
            ("/project/index.ts", r#"console.log("Hello, World!");"#),
        ],
        CaseSensitivity::CaseSensitive,
    );

    // Parse command line with --customConditions null
    let cmd_line = parse_command_line(
        &[
            "--project".into(),
            "/project".into(),
            "--customConditions".into(),
            "null".into(),
        ],
        &fs,
        RootedDirectoryPath::from("/project"),
    );

    // Check that the raw options contain null for customConditions
    let raw_map = cmd_line
        .raw
        .as_ref()
        .and_then(Value::as_map)
        .expect("Raw options should be an OrderedMap");
    let custom_conditions_raw = raw_map.get("customConditions");
    assert!(
        custom_conditions_raw.is_some_and(Value::is_null),
        "customConditions should be nil in raw options"
    );

    // Wrap command line options in "compilerOptions" key to match
    // tsconfig.json structure
    let mut wrapped_raw = OrderedMap::new();
    wrapped_raw.set("compilerOptions".to_string(), cmd_line.raw.clone().unwrap());
    let parsed_config = get_parsed_command_line_of_config_file(
        RootedFilePath::from("/project/tsconfig.json"),
        cmd_line.compiler_options(),
        Some(&wrapped_raw),
        &fs,
        None,
    );
    let parsed_config = match parsed_config {
        Ok(p) => p,
        Err(errors) => panic!("Should not have errors: {}", errors.len()),
    };

    // customConditions is nil (overridden by command line)
    assert!(
        parsed_config
            .compiler_options()
            .is_some_and(|o| o.custom_conditions.is_none()),
        "customConditions should be nil after override"
    );
}

// ---------------------------------------------------------------------------
// `TestConfig` + `baselineParseConfigWith` harness
// (`TestParseJsonConfigFileContent` /
//  `TestParseJsonSourceFileConfigFileContent` / `TestParseTypeAcquisition`)
// ---------------------------------------------------------------------------

use std::collections::HashMap;
use std::sync::Mutex;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::diagnostic::lock_diagnostic;
use tsc_core::core::UTF16Offset;
use tsc_core::options_generated::{
    CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget,
};
use tsc_core::text::TextPos;
use tsc_core::tristate::TS_TRUE;
use tsc_diagnosticwriter::FormattingOptions;
use tsc_repo::test_data_path;
use tsc_tspath::{PathKey, RootedPath, rooted_directory_path_from_absolute};
use tsc_vfs::Vfs;

use crate::parsedcommandline::ParsedCommandLine;
use crate::tsconfigparsing::{
    ExtendedConfigCache, ExtendedConfigCacheEntry, get_content_mapper_option_diagnostic_location,
    get_parsed_command_line_of_config_file, parse_extended_config,
};

/// `type testConfig struct`.
struct TestConfig {
    json_text: &'static str,
    config_file_name: &'static str,
    base_path: &'static str,
    all_file_list: Vec<(&'static str, &'static str)>,
    existing_options: Option<CompilerOptions>,
}

fn test_vfs(files: &[(&str, &str)], case_sensitivity: CaseSensitivity) -> Arc<dyn Vfs> {
    vfstest::from_map(files.iter().copied(), case_sensitivity)
}

fn config_path_key(fs: &Arc<dyn Vfs>, config_file_name: &RootedFilePath) -> PathKey {
    fs.case_sensitivity()
        .path_key(&RootedPath::from(config_file_name.clone()))
}

/// `getParsedWithJsonApi`.
fn get_parsed_with_json_api(
    config: &TestConfig,
    fs: &Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
) -> ParsedCommandLine {
    let config_file_name = to_rooted_file_path(config.config_file_name, &base_path);
    let path = config_path_key(fs, &config_file_name);
    let (parsed, _) =
        parse_config_file_text_to_json(config_file_name.clone(), path, config.json_text);
    parse_json_config_file_content(
        &parsed,
        fs,
        base_path,
        config.existing_options.as_ref(),
        config_file_name,
        &[],
        None,
    )
}

/// `getParsedWithJsonSourceFileApi`.
fn get_parsed_with_json_source_file_api(
    config: &TestConfig,
    fs: &Arc<dyn Vfs>,
    base_path: RootedDirectoryPath,
) -> ParsedCommandLine {
    let config_file_name = to_rooted_file_path(config.config_file_name, &base_path);
    let path = config_path_key(fs, &config_file_name);
    let ts_config_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name,
        path,
        config.json_text,
    ));
    parse_json_source_file_config_file_content(
        &ts_config_source_file,
        fs,
        base_path,
        config.existing_options.as_ref(),
        None,
        &[],
        None,
    )
}

/// `tsoptionstest.GetParsedCommandLine`.
fn get_parsed_command_line(
    json_text: &str,
    files: &[(&str, &str)],
    current_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> ParsedCommandLine {
    let fs = test_vfs(files, case_sensitivity);
    let config_file_name = current_directory.resolve_file("tsconfig.json");
    let ts_config_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name.clone(),
        case_sensitivity.path_key(&RootedPath::from(config_file_name)),
        json_text,
    ));
    parse_json_source_file_config_file_content(
        &ts_config_source_file,
        &fs,
        current_directory,
        None,
        None,
        &[],
        None,
    )
}

/// `printFS`.
fn print_fs(output: &mut String, files: &Arc<dyn Vfs>, root: RootedDirectoryPath) {
    tsc_vfs::walk_dir(files, &root.as_path(), &mut |path, entry, err| {
        if let Some(err) = err {
            panic!("walk error: {err:?}");
        }
        if let Some(entry) = entry
            && entry.type_().is_regular()
        {
            let content = files
                .read_file(&RootedFilePath::from(path.clone()))
                .unwrap_or_else(|| panic!("failed to read file {}", path.as_string()));
            output.push_str(&format!(
                "//// [{}]\r\n{}\r\n\r\n",
                path.as_string(),
                content
            ));
        }
        Ok(())
    })
    .expect("walk dir");
}

/// Snapshot the errors out of `parsed.errors`, stripping `DiagnosticFile.node`
/// so diagnostics render against their snapshotted text instead of requiring
/// the producing file's node arena (Go's `*SourceFile` pointers carry the
/// whole file; `DiagnosticFile` snapshots `text`/`file_name`/`span_map`, so
/// rendered output is identical for unmapped files).
fn errors_of(parsed: &ParsedCommandLine) -> Vec<DiagnosticRef> {
    let errors = parsed.errors.lock().unwrap_or_else(|e| e.into_inner());
    errors
        .iter()
        .map(|d| {
            let d = lock_diagnostic(d).clone();
            let mut d = d;
            if let Some(mut file) = d.file().cloned() {
                file.node = None;
                d.set_file(Some(file));
            }
            Arc::new(Mutex::new(d))
        })
        .collect()
}

/// `baselineParseConfigWith`.
fn baseline_parse_config_with(
    baseline_file_name: &str,
    include_compiler_options: bool,
    input: &[TestConfig],
    get_parsed: fn(&TestConfig, &Arc<dyn Vfs>, RootedDirectoryPath) -> ParsedCommandLine,
) {
    let mut baseline_content = String::new();
    for (i, config) in input.iter().enumerate() {
        let base_path = if config.base_path.is_empty() {
            to_rooted_file_path(config.config_file_name, &RootedDirectoryPath::from("/"))
                .directory()
        } else {
            RootedDirectoryPath::from(config.base_path)
        };
        let config_file_name = base_path.resolve_file(config.config_file_name);
        let mut files = config.all_file_list.clone();
        files.push((config_file_name.as_string(), config.json_text));
        let fs = test_vfs(&files, CaseSensitivity::CaseSensitive);
        let parsed_config_file_content = get_parsed(config, &fs, base_path.clone());

        baseline_content.push_str("Fs::\n");
        print_fs(&mut baseline_content, &fs, RootedDirectoryPath::from("/"));
        baseline_content.push('\n');
        baseline_content.push_str("configFileName:: ");
        baseline_content.push_str(config.config_file_name);
        baseline_content.push('\n');
        if include_compiler_options {
            baseline_content.push_str("CompilerOptions::\n");
            let compiler_options = parsed_config_file_content
                .parsed_config
                .as_ref()
                .and_then(|p| p.compiler_options.as_ref());
            let mut buf = Vec::new();
            tsc_json::marshal_indent_write(&mut buf, &compiler_options, "", "  ")
                .expect("marshal compiler options");
            baseline_content.push_str(std::str::from_utf8(&buf).unwrap());
            baseline_content.push_str("\n\n");

            let type_acquisition = parsed_config_file_content
                .parsed_config
                .as_ref()
                .and_then(|p| p.type_acquisition.as_ref());
            if let Some(type_acquisition) = type_acquisition {
                baseline_content.push_str("TypeAcquisition::\n");
                let mut buf = Vec::new();
                tsc_json::marshal_indent_write(&mut buf, &type_acquisition, "", "  ")
                    .expect("marshal type acquisition");
                baseline_content.push_str(std::str::from_utf8(&buf).unwrap());
                baseline_content.push_str("\n\n");
            }
        }
        baseline_content.push_str("FileNames::\n");
        let file_names: Vec<String> = parsed_config_file_content
            .file_names()
            .iter()
            .map(|f| f.as_string().to_string())
            .collect();
        baseline_content.push_str(&file_names.join(","));
        baseline_content.push('\n');
        baseline_content.push_str("Errors::\n");
        let errors = errors_of(&parsed_config_file_content);
        let diags = tsc_diagnosticwriter::from_ast_diagnostics(&errors, &[]);
        let mut diagnostics_out = Vec::new();
        tsc_diagnosticwriter::format_diagnostics_with_color_and_context(
            &mut diagnostics_out,
            &diags,
            &FormattingOptions {
                new_line: "\r\n".into(),
                current_directory: base_path.clone(),
                case_sensitivity: CaseSensitivity::CaseSensitive,
                ..Default::default()
            },
        );
        baseline_content.push_str(std::str::from_utf8(&diagnostics_out).unwrap());
        baseline_content.push('\n');
        if i != input.len() - 1 {
            baseline_content.push('\n');
        }
    }
    tsc_testutil::baseline::run(
        baseline_file_name,
        &baseline_content,
        &tsc_testutil::baseline::Options {
            subfolder: "config/tsconfigParsing".into(),
            ..Default::default()
        },
    )
    .expect("baseline");
}

const TSCONFIG_WITH_EXTENDS: &str = r#"{
  "files": ["/src/index.ts", "/src/app.ts"],
  "include": ["/src/**/*"],
  "exclude": [],
  "ts-node": {
    "compilerOptions": {
      "module": "commonjs"
    },
    "transpileOnly": true
  }
}"#;

const TSCONFIG_WITHOUT_CONFIG_DIR: &str = r#"{
  "compilerOptions": {
    "outDir": "bin"
  }
}"#;

const TSCONFIG_WITH_CONFIG_DIR: &str = r#"{
  "compilerOptions": {
    "outDir": "${configDir}/bin"
  }
}"#;

const TSCONFIG_WITH_EXTENDS_AND_CONFIG_DIR: &str = r#"{
  "compilerOptions": {
    "outFile": "${configDir}/outFile",
    "outDir": "${configDir}/outDir",
    "rootDir": "${configDir}/rootDir",
    "tsBuildInfoFile": "${configDir}/tsBuildInfoFile",
    "baseUrl": "${configDir}/baseUrl",
    "declarationDir": "${configDir}/declarationDir",
  }
}"#;

fn tc(
    json_text: &'static str,
    config_file_name: &'static str,
    base_path: &'static str,
    all_file_list: &[(&'static str, &'static str)],
) -> TestConfig {
    TestConfig {
        json_text,
        config_file_name,
        base_path,
        all_file_list: all_file_list.to_vec(),
        existing_options: None,
    }
}

/// `parseJsonConfigFileTests`.
fn parse_json_config_file_tests() -> Vec<(&'static str, bool, Vec<TestConfig>)> {
    vec![
        (
            "ignore dotted files and folders",
            false,
            vec![tc(
                r#"{}"#,
                "tsconfig.json",
                "/apath",
                &[
                    ("/apath/test.ts", ""),
                    ("/apath/.git/a.ts", ""),
                    ("/apath/.b.ts", ""),
                    ("/apath/..c.ts", ""),
                ],
            )],
        ),
        (
            "allow dotted files and folders when explicitly requested",
            false,
            vec![tc(
                r#"{
                    "files": ["/apath/.git/a.ts", "/apath/.b.ts", "/apath/..c.ts"]
                }"#,
                "tsconfig.json",
                "/apath",
                &[
                    ("/apath/test.ts", ""),
                    ("/apath/.git/a.ts", ""),
                    ("/apath/.b.ts", ""),
                    ("/apath/..c.ts", ""),
                ],
            )],
        ),
        (
            "implicitly exclude common package folders",
            false,
            vec![tc(
                r#"{}"#,
                "tsconfig.json",
                "/",
                &[
                    ("/node_modules/a.ts", ""),
                    ("/bower_components/b.ts", ""),
                    ("/jspm_packages/c.ts", ""),
                    ("/d.ts", ""),
                    ("/folder/e.ts", ""),
                ],
            )],
        ),
        (
            "generates errors for empty files list",
            false,
            vec![tc(
                r#"{
                "files": []
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "handles empty file name in files list",
            false,
            vec![tc(
                r#"{
                "files": [""]
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "generates errors for empty files list when no references are provided",
            false,
            vec![tc(
                r#"{
                "files": [],
                "references": []
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "generates errors for directory with no .ts files",
            false,
            vec![tc(
                r#"{
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.js", "")],
            )],
        ),
        (
            "generates errors for empty include",
            false,
            vec![tc(
                r#"{
                "include": []
            }"#,
                "/apath/tsconfig.json",
                "/tests/cases/unittests",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "generates errors for include with parent directory after recursive wildcard",
            false,
            vec![tc(
                r#"{
                "include": ["**/../*.ts"]
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/main.ts", "")],
            )],
        ),
        (
            "parses tsconfig with compilerOptions, files, include, and exclude",
            true,
            vec![tc(
                r#"{
  "compilerOptions": {
    "outDir": "./dist",
    "strict": true,
    "noImplicitAny": true,
    "target": "ES2017",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "moduleDetection": "auto",
    "jsx": "react",
	"maxNodeModuleJsDepth": 1,
	"paths": {
      "jquery": ["./vendor/jquery/dist/jquery"]
    }
  },
  "files": ["/apath/src/index.ts", "/apath/src/app.ts"],
  "include": ["/apath/src/**/*"],
  "exclude": ["/apath/node_modules", "/apath/dist"]
}"#,
                "/apath/tsconfig.json",
                "/apath",
                &[
                    ("/apath/src/index.ts", ""),
                    ("/apath/src/app.ts", ""),
                    ("/apath/node_modules/module.ts", ""),
                    ("/apath/dist/output.js", ""),
                ],
            )],
        ),
        (
            "generates errors when commandline option is in tsconfig",
            false,
            vec![tc(
                r#"{
  "compilerOptions": {
    "help": true
  }
}"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "does not generate errors for empty files list when one or more references are provided",
            false,
            vec![tc(
                r#"{
                "files": [],
                "references": [{ "path": "/apath" }]
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "exclude outDir unless overridden",
            false,
            vec![
                tc(
                    r#"{
                "compilerOptions": {
                    "outDir": "bin"
                }
            }"#,
                    "tsconfig.json",
                    "/",
                    &[("/bin/a.ts", ""), ("/b.ts", "")],
                ),
                tc(
                    r#"{
                "compilerOptions": {
                    "outDir": "bin"
                },
                "exclude": [ "obj" ]
            }"#,
                    "tsconfig.json",
                    "/",
                    &[("/bin/a.ts", ""), ("/b.ts", "")],
                ),
            ],
        ),
        (
            "exclude declarationDir unless overridden",
            false,
            vec![
                tc(
                    r#"{
                "compilerOptions": {
                    "declarationDir": "declarations"
                }
            }"#,
                    "tsconfig.json",
                    "/",
                    &[("/declarations/a.d.ts", ""), ("/a.ts", "")],
                ),
                tc(
                    r#"{
                "compilerOptions": {
                    "declarationDir": "declarations"
                },
                "exclude": [ "types" ]
            }"#,
                    "tsconfig.json",
                    "/",
                    &[("/declarations/a.d.ts", ""), ("/a.ts", "")],
                ),
            ],
        ),
        (
            "generates errors for empty directory",
            false,
            vec![tc(
                r#"{
                "compilerOptions": {
                    "allowJs": true
                }
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[],
            )],
        ),
        (
            "generates errors for includes with outDir",
            false,
            vec![tc(
                r#"{
                "compilerOptions": {
                    "outDir": "./"
                },
                "include": ["**/*"]
            }"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "generates errors when include is not string",
            false,
            vec![tc(
                r#"{
  "include": [
    [
      "./**/*.ts"
    ]
  ]
}"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "generates errors when files is not string",
            false,
            vec![tc(
                r#"{
  "files": [
    {
      "compilerOptions": {
        "experimentalDecorators": true,
        "allowJs": true
      }
    }
  ]
}"#,
                "/apath/tsconfig.json",
                "/apath",
                &[("/apath/a.ts", "")],
            )],
        ),
        (
            "with outDir from base tsconfig",
            false,
            vec![
                tc(
                    r#"{
  "extends": "./tsconfigWithoutConfigDir.json"
}"#,
                    "tsconfig.json",
                    "/",
                    &[
                        (
                            "/tsconfigWithoutConfigDir.json",
                            TSCONFIG_WITHOUT_CONFIG_DIR,
                        ),
                        ("/bin/a.ts", ""),
                        ("/b.ts", ""),
                    ],
                ),
                tc(
                    r#"{
  "extends": "./tsconfigWithConfigDir.json"
}"#,
                    "tsconfig.json",
                    "/",
                    &[
                        ("/tsconfigWithConfigDir.json", TSCONFIG_WITH_CONFIG_DIR),
                        ("/bin/a.ts", ""),
                        ("/b.ts", ""),
                    ],
                ),
            ],
        ),
        (
            "returns error when tsconfig have excludes",
            false,
            vec![tc(
                r#"{
                    "compilerOptions": {
                        "lib": ["es5"]
                    },
                    "excludes": [
                        "foge.ts"
                    ]
                }"#,
                "tsconfig.json",
                "/apath",
                &[("/apath/test.ts", ""), ("/apath/foge.ts", "")],
            )],
        ),
        (
            "parses tsconfig with extends, files, include and other options",
            true,
            vec![tc(
                r#"{
				"extends": "./tsconfigWithExtends.json",
				"compilerOptions": {
				    "outDir": "./dist",
    				"strict": true,
    				"noImplicitAny": true,
					"baseUrl": "",
				},
			}"#,
                "tsconfig.json",
                "/",
                &[
                    ("/tsconfigWithExtends.json", TSCONFIG_WITH_EXTENDS),
                    ("/src/index.ts", ""),
                    ("/src/app.ts", ""),
                    ("/node_modules/module.ts", ""),
                    ("/dist/output.js", ""),
                ],
            )],
        ),
        (
            "parses tsconfig with extends and configDir",
            true,
            vec![tc(
                r#"{
				"extends": "./tsconfig.base.json"
			}"#,
                "tsconfig.json",
                "/",
                &[
                    ("/tsconfig.base.json", TSCONFIG_WITH_EXTENDS_AND_CONFIG_DIR),
                    ("/src/index.ts", ""),
                    ("/src/app.ts", ""),
                    ("/node_modules/module.ts", ""),
                    ("/dist/output.js", ""),
                ],
            )],
        ),
        (
            "reports error for an unknown option",
            false,
            vec![tc(
                r#"{
			    "compilerOptions": {
				"unknown": true
			    }
			}"#,
                "tsconfig.json",
                "/",
                &[("/app.ts", "")],
            )],
        ),
        (
            "reports spelling suggestion for an unknown option",
            false,
            vec![tc(
                r#"{
			    "compilerOptions": {
				"targt": 1
			    }
			}"#,
                "tsconfig.json",
                "/",
                &[("/app.ts", "")],
            )],
        ),
        (
            "reports errors for wrong type option and invalid enum value",
            false,
            vec![tc(
                r#"{
			    "compilerOptions": {
				"target": "invalid value",
				"removeComments": "should be a boolean",
				"moduleResolution": "invalid value"
			    }
			}"#,
                "tsconfig.json",
                "/",
                &[("/app.ts", "")],
            )],
        ),
        (
            "reports errors for incorrectly cased option names",
            true,
            vec![tc(
                r#"{
			    "compilerOptions": {
				"sourcemap": true,
				"declarationmap": true,
				"nouncheckedindexedaccess": true,
				"exactoptionalpropertytypes": true,
				"verbatimmodulesyntax": true,
				"isolatedmodules": true,
				"nouncheckedsideeffectimports": true,
				"moduledetection": "force",
				"skiplibcheck": true,
				"checkjs": true
			    }
			}"#,
                "tsconfig.json",
                "/",
                &[("/app.ts", "")],
            )],
        ),
        (
            "handles empty types array",
            true,
            vec![tc(
                r#"{
			    "compilerOptions": {
					"types": []
				}
			}"#,
                "tsconfig.json",
                "/",
                &[("/app.ts", "")],
            )],
        ),
        (
            "issue 1267 scenario - extended files not picked up",
            true,
            vec![tc(
                r#"{
  "extends": "./tsconfig-base/backend.json",
  "compilerOptions": {
    "baseUrl": "./",
    "outDir": "dist",
    "rootDir": "src",
    "resolveJsonModule": true
  },
  "exclude": ["node_modules", "dist"],
  "include": ["src/**/*"]
}"#,
                "tsconfig.json",
                "/",
                &[
                    (
                        "/tsconfig-base/backend.json",
                        r#"{
  "$schema": "https://json.schemastore.org/tsconfig",
  "display": "Backend",
  "compilerOptions": {
    "allowJs": true,
    "module": "nodenext",
    "removeComments": true,
    "emitDecoratorMetadata": true,
    "experimentalDecorators": true,
    "allowSyntheticDefaultImports": true,
    "target": "esnext",
    "lib": ["ESNext"],
    "incremental": false,
    "esModuleInterop": true,
    "noImplicitAny": true,
    "moduleResolution": "nodenext",
    "types": ["node", "vitest/globals"],
    "sourceMap": true,
    "strictPropertyInitialization": false
  },
  "files": [
    "types/ical2json.d.ts",
    "types/express.d.ts",
    "types/multer.d.ts",
    "types/reset.d.ts",
    "types/stripe-custom-typings.d.ts",
    "types/nestjs-modules.d.ts",
    "types/luxon.d.ts",
    "types/nestjs-pino.d.ts"
  ],
  "ts-node": {
    "files": true
  }
}"#,
                    ),
                    ("/tsconfig-base/types/ical2json.d.ts", "export {}"),
                    ("/tsconfig-base/types/express.d.ts", "export {}"),
                    ("/tsconfig-base/types/multer.d.ts", "export {}"),
                    ("/tsconfig-base/types/reset.d.ts", "export {}"),
                    (
                        "/tsconfig-base/types/stripe-custom-typings.d.ts",
                        "export {}",
                    ),
                    ("/tsconfig-base/types/nestjs-modules.d.ts", "export {}"),
                    (
                        "/tsconfig-base/types/luxon.d.ts",
                        "declare module 'luxon' {
  interface TSSettings {
    throwOnInvalid: true
  }
}
export {}",
                    ),
                    ("/tsconfig-base/types/nestjs-pino.d.ts", "export {}"),
                    ("/src/main.ts", "export {}"),
                    ("/src/utils.ts", "export {}"),
                ],
            )],
        ),
        (
            "null overrides in extended tsconfig - array fields",
            true,
            vec![tc(
                r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": null,
    "lib": null,
    "typeRoots": null
  }
}"#,
                "tsconfig.json",
                "/",
                &[
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node", "@types/jest"],
    "lib": ["es2020", "dom"],
    "typeRoots": ["./types", "./node_modules/@types"]
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ],
            )],
        ),
        (
            "null overrides in extended tsconfig - string fields",
            true,
            vec![tc(
                r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "outDir": null,
    "baseUrl": null,
    "rootDir": null
  }
}"#,
                "tsconfig.json",
                "/",
                &[
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "outDir": "./dist",
    "baseUrl": "./src",
    "rootDir": "./src"
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ],
            )],
        ),
        (
            "null overrides in extended tsconfig - mixed field types",
            true,
            vec![tc(
                r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": null,
    "outDir": null,
    "strict": false,
    "lib": ["es2022"],
    "allowJs": null
  }
}"#,
                "tsconfig.json",
                "/",
                &[
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node"],
    "lib": ["es2020", "dom"],
    "outDir": "./dist",
    "strict": true,
    "allowJs": true,
    "target": "es2020"
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ],
            )],
        ),
        (
            "null overrides with multiple extends levels",
            true,
            vec![tc(
                r#"{
  "extends": "./tsconfig-middle.json",
  "compilerOptions": {
    "types": null,
    "lib": null
  }
}"#,
                "tsconfig.json",
                "/",
                &[
                    (
                        "/tsconfig-middle.json",
                        r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": ["jest"],
    "outDir": "./build"
  }
}"#,
                    ),
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node"],
    "lib": ["es2020"],
    "outDir": "./dist",
    "strict": true
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ],
            )],
        ),
        (
            "null overrides in middle level of extends chain",
            true,
            vec![tc(
                r#"{
  "extends": "./tsconfig-middle.json",
  "compilerOptions": {
    "outDir": "./final"
  }
}"#,
                "tsconfig.json",
                "/",
                &[
                    (
                        "/tsconfig-middle.json",
                        r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": null,
    "lib": null,
    "outDir": "./middle"
  }
}"#,
                    ),
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node"],
    "lib": ["es2020"],
    "outDir": "./base",
    "strict": true
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ],
            )],
        ),
    ]
}

/// `TestParseJsonConfigFileContent`.
#[test]
fn test_parse_json_config_file_content() {
    for (title, include_compiler_options, input) in parse_json_config_file_tests() {
        baseline_parse_config_with(
            &format!("{title} with json api.js"),
            include_compiler_options,
            &input,
            get_parsed_with_json_api,
        );
    }
}

/// `TestParseJsonSourceFileConfigFileContent`.
#[test]
fn test_parse_json_source_file_config_file_content() {
    for (title, include_compiler_options, input) in parse_json_config_file_tests() {
        baseline_parse_config_with(
            &format!("{title} with jsonSourceFile api.js"),
            include_compiler_options,
            &input,
            get_parsed_with_json_source_file_api,
        );
    }
}

/// `TestParseJsonSourceFileConfigFileContentReportsInvalidExtendedConfig`.
#[test]
fn test_parse_json_source_file_config_file_content_reports_invalid_extended_config() {
    let files: &[(&str, &str)] = &[
        (
            "/project/tsconfig.json",
            "{\n  \"extends\": \"./bad.json\"\n}",
        ),
        // The parser recovers from this as object-like JSON, producing
        // expected-token errors for ':', ',', ',', and '}'.
        ("/project/bad.json", "{ this is not json"),
        ("/project/main.ts", "export const x = 1;"),
    ];
    let fs = test_vfs(files, CaseSensitivity::CaseSensitive);
    let config_file_name = RootedFilePath::from("/project/tsconfig.json");
    let config_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name.clone(),
        config_path_key(&fs, &config_file_name),
        files
            .iter()
            .find(|f| f.0 == "/project/tsconfig.json")
            .unwrap()
            .1,
    ));

    let parsed = parse_json_source_file_config_file_content(
        &config_file,
        &fs,
        RootedDirectoryPath::from("/project"),
        None,
        None,
        &[],
        None,
    );

    let errors = parsed.errors.lock().unwrap_or_else(|e| e.into_inner());
    let parse_errors: Vec<&DiagnosticRef> = errors
        .iter()
        .filter(|d| lock_diagnostic(d).code() == tsc_diagnostics::X_0_expected.code())
        .collect();
    let expected_parse_error_messages = [":", ",", ",", "}"];
    let expected_parse_error_positions = [7, 10, 14, 18];
    assert_eq!(expected_parse_error_messages.len(), parse_errors.len());
    assert_eq!(
        parse_errors
            .iter()
            .map(|d| lock_diagnostic(d).message_args()[0].clone())
            .collect::<Vec<_>>(),
        expected_parse_error_messages
    );
    assert_eq!(
        parse_errors
            .iter()
            .map(|d| lock_diagnostic(d).pos())
            .collect::<Vec<_>>(),
        expected_parse_error_positions
    );
    for diagnostic in &parse_errors {
        assert_eq!(
            lock_diagnostic(diagnostic)
                .file()
                .expect("diagnostic file")
                .file_name
                .as_string(),
            "/project/bad.json"
        );
    }
}

/// `TestParseJsonSourceFileConfigFileContentWithEmptyExtendedConfig` —
/// extending an empty config file used to panic on nil Statements (#4265).
#[test]
fn test_parse_json_source_file_config_file_content_with_empty_extended_config() {
    let files: &[(&str, &str)] = &[
        (
            "/project/tsconfig.json",
            "{\n  \"extends\": \"./base.json\"\n}",
        ),
        ("/project/base.json", ""),
        ("/project/main.ts", "export const x = 1;"),
    ];
    let fs = test_vfs(files, CaseSensitivity::CaseSensitive);
    let config_file_name = RootedFilePath::from("/project/tsconfig.json");
    let config_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name.clone(),
        config_path_key(&fs, &config_file_name),
        "{\n  \"extends\": \"./base.json\"\n}",
    ));

    let parsed = parse_json_source_file_config_file_content(
        &config_file,
        &fs,
        RootedDirectoryPath::from("/project"),
        None,
        None,
        &[],
        None,
    );

    assert_eq!(
        parsed.file_names(),
        &[RootedFilePath::from("/project/main.ts")]
    );
}

/// `TestParseJsonSourceFileConfigFileContentDoesNotDuplicateUnquotedKeyDiagnostics`.
#[test]
fn test_parse_json_source_file_config_file_content_does_not_duplicate_unquoted_key_diagnostics() {
    let parsed = get_parsed_command_line(
        "{\n  compilerOptions: {\n    strict: true\n  }\n}",
        &[("/main.ts", "export const x = 1;")],
        RootedDirectoryPath::from("/"),
        CaseSensitivity::CaseSensitive,
    );

    let diags = parsed.get_config_file_parsing_diagnostics();
    assert_eq!(diags.len(), 2);
    let expected_locations = [(1, 2), (2, 4)];
    for (index, diagnostic) in diags.iter().enumerate() {
        let d = lock_diagnostic(diagnostic);
        assert_eq!(
            d.code(),
            tsc_diagnostics::String_literal_with_double_quotes_expected.code()
        );
        let file = d.file().expect("diagnostic file");
        let (line, character) = ecma_line_and_character(&file.text, d.pos());
        assert_eq!((line, character), expected_locations[index]);
    }
}

/// `TestParseJsonSourceFileConfigFileContentReportsQuestionTokenDiagnostics`.
#[test]
fn test_parse_json_source_file_config_file_content_reports_question_token_diagnostics() {
    let parsed = get_parsed_command_line(
        "{\n  compilerOptions?: {\n    strict?: true\n  }\n}",
        &[("/main.ts", "export const x = 1;")],
        RootedDirectoryPath::from("/"),
        CaseSensitivity::CaseSensitive,
    );

    let mut question_token_diagnostics = Vec::new();
    for diagnostic in parsed.get_config_file_parsing_diagnostics() {
        if lock_diagnostic(&diagnostic).code()
            == tsc_diagnostics::The_0_modifier_can_only_be_used_in_TypeScript_files.code()
        {
            question_token_diagnostics.push(diagnostic);
        }
    }
    assert_eq!(question_token_diagnostics.len(), 2);
    let expected_locations = [(1, 17), (2, 10)];
    for (index, diagnostic) in question_token_diagnostics.iter().enumerate() {
        let d = lock_diagnostic(diagnostic);
        let file = d.file().expect("diagnostic file");
        let (line, character) = ecma_line_and_character(&file.text, d.pos());
        assert_eq!((line, character), expected_locations[index]);
    }
}

/// `scanner.GetECMALineAndUTF16CharacterOfPosition` over the diagnostic's
/// snapshotted file text (a `DiagnosticFile` is not `SourceFileLike`).
fn ecma_line_and_character(text: &str, pos: i32) -> (i32, UTF16Offset) {
    struct TextFile<'a>(&'a str);
    impl tsc_scanner::scanner::SourceFileLike for TextFile<'_> {
        fn text(&self) -> &str {
            self.0
        }
        fn ecma_line_map(&self) -> Vec<TextPos> {
            tsc_core::core::compute_ecma_line_starts(self.0)
        }
    }
    tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(&TextFile(text), pos)
}

/// `TestContentMappers`.
#[test]
fn test_content_mappers() {
    let config = TestConfig {
        json_text: r#"{
			"contentMappers": [
				{ "package": "vue-mapper", "extensions": [".vue"], "options": { "strictTemplates": true } }
			],
			"include": ["src"]
		}"#,
        config_file_name: "tsconfig.json",
        base_path: "/",
        all_file_list: vec![
            ("/src/app.ts", "export {}"),
            ("/src/Component.vue", "<template></template>"),
            (
                "/node_modules/vue-mapper/package.json",
                r#"{ "name": "vue-mapper", "version": "1.2.3", "typescript": { "contentMapper": { "exec": ["node", "./mapper.js"], "dynamicConfig": true } } }"#,
            ),
        ],
        existing_options: Some(CompilerOptions {
            run_external_code: TS_TRUE,
            ..Default::default()
        }),
    };
    for (name, get_parsed) in [
        (
            "json api",
            get_parsed_with_json_api
                as fn(&TestConfig, &Arc<dyn Vfs>, RootedDirectoryPath) -> ParsedCommandLine,
        ),
        ("jsonSourceFile api", get_parsed_with_json_source_file_api),
    ] {
        let mut files = config.all_file_list.clone();
        files.push(("/tsconfig.json", config.json_text));
        let fs = test_vfs(&files, CaseSensitivity::CaseSensitive);
        let parsed = get_parsed(&config, &fs, RootedDirectoryPath::from("/"));

        assert_eq!(
            parsed
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .len(),
            0,
            "{name}"
        );

        let mappers = parsed.content_mappers();
        assert_eq!(mappers.len(), 1, "{name}");
        assert_eq!(mappers[0].package, "vue-mapper", "{name}");
        assert_eq!(
            mappers[0].extensions.as_deref(),
            Some(&[".vue".to_string()][..]),
            "{name}"
        );
        assert_eq!(
            mappers[0].options.as_ref().unwrap().get(),
            r#"{"strictTemplates":true}"#,
            "{name}"
        );
        assert_eq!(
            parsed.content_mapper_extensions(),
            &[".vue".to_string()],
            "{name}"
        );

        // The package.json is resolved during parsing, populating name,
        // version, and exec.
        assert_eq!(mappers[0].name, "vue-mapper", "{name}");
        assert_eq!(mappers[0].version, "1.2.3", "{name}");
        assert_eq!(
            mappers[0].exec.as_deref(),
            Some(&["node".to_string(), "./mapper.js".to_string()][..]),
            "{name}"
        );
        assert!(mappers[0].dynamic_config, "{name}");
        assert_eq!(
            mappers[0].package_directory,
            RootedDirectoryPath::from("/node_modules/vue-mapper"),
            "{name}"
        );

        // The .vue file is picked up by the include glob because its
        // extension is registered.
        assert!(
            parsed
                .file_names()
                .contains(&RootedFilePath::from("/src/Component.vue")),
            "{name}: expected /src/Component.vue in {:?}",
            parsed.file_names()
        );
        assert!(
            parsed
                .file_names()
                .contains(&RootedFilePath::from("/src/app.ts")),
            "{name}: expected /src/app.ts in {:?}",
            parsed.file_names()
        );
    }
}

/// `TestContentMapperOptionDiagnosticLocation`.
#[test]
fn test_content_mapper_option_diagnostic_location() {
    let config = TestConfig {
        json_text: r#"{
			"contentMappers": [{
				"package": "mapper",
				"extensions": [".vue"],
				"options": { "plugins": [{ "name": 1 }] }
			}]
		}"#,
        config_file_name: "tsconfig.json",
        base_path: "/",
        all_file_list: vec![
            ("/index.ts", "export {};"),
            (
                "/node_modules/mapper/package.json",
                r#"{ "name": "mapper", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["mapper"] } } }"#,
            ),
        ],
        existing_options: Some(CompilerOptions {
            run_external_code: TS_TRUE,
            ..Default::default()
        }),
    };
    let fs = test_vfs(&config.all_file_list, CaseSensitivity::CaseSensitive);
    let parsed = get_parsed_with_json_source_file_api(&config, &fs, RootedDirectoryPath::from("/"));
    let mappers = parsed.content_mappers().to_vec();
    let (file, loc) = get_content_mapper_option_diagnostic_location(
        Some(&parsed),
        &mappers[0],
        &[
            tsc_contentmapper::OptionPathSegment {
                property: "plugins".into(),
                index: 0,
                is_index: false,
            },
            tsc_contentmapper::OptionPathSegment {
                property: String::new(),
                index: 0,
                is_index: true,
            },
            tsc_contentmapper::OptionPathSegment {
                property: "name".into(),
                index: 0,
                is_index: false,
            },
        ],
    )
    .expect("diagnostic location");
    assert_eq!(&file.text()[loc.pos() as usize..loc.end() as usize], "1");
}

/// `TestContentMappersAreInheritedFromExtendedConfig`.
#[test]
fn test_content_mappers_are_inherited_from_extended_config() {
    let config = TestConfig {
        json_text: r#"{ "extends": "./base.json" }"#,
        config_file_name: "tsconfig.json",
        base_path: "/project",
        all_file_list: vec![
            (
                "/project/base.json",
                r#"{ "contentMappers": [{ "package": "vue-mapper", "extensions": [".vue"] }], "include": ["src"] }"#,
            ),
            ("/project/src/index.ts", "export {};"),
            ("/project/src/component.vue", "<template></template>"),
            (
                "/project/node_modules/vue-mapper/package.json",
                r#"{ "name": "vue-mapper", "version": "1.2.3", "typescript": { "contentMapper": { "exec": ["node", "./mapper.js"] } } }"#,
            ),
        ],
        existing_options: Some(CompilerOptions {
            run_external_code: TS_TRUE,
            ..Default::default()
        }),
    };
    for (name, get_parsed) in [
        (
            "json api",
            get_parsed_with_json_api
                as fn(&TestConfig, &Arc<dyn Vfs>, RootedDirectoryPath) -> ParsedCommandLine,
        ),
        ("jsonSourceFile api", get_parsed_with_json_source_file_api),
    ] {
        let fs = test_vfs(&config.all_file_list, CaseSensitivity::CaseSensitive);
        let parsed = get_parsed(&config, &fs, RootedDirectoryPath::from("/project"));
        assert_eq!(
            parsed
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .len(),
            0,
            "{name}"
        );
        assert_eq!(parsed.content_mappers().len(), 1, "{name}");
        assert_eq!(parsed.content_mappers()[0].package, "vue-mapper", "{name}");
        assert_eq!(
            parsed.content_mapper_extensions(),
            &[".vue".to_string()],
            "{name}"
        );
        assert!(
            parsed
                .file_names()
                .contains(&RootedFilePath::from("/project/src/component.vue")),
            "{name}"
        );
    }
}

/// `TestContentMappersRequireFlag`.
#[test]
fn test_content_mappers_require_flag() {
    let config = TestConfig {
        json_text: r#"{ "contentMappers": [{ "package": "vue-mapper", "extensions": [".vue"] }] }"#,
        config_file_name: "tsconfig.json",
        base_path: "/",
        all_file_list: vec![("/app.ts", "export {}")],
        // existing_options omitted: --runExternalCode is not set.
        existing_options: None,
    };
    let expected_code =
        tsc_diagnostics::Content_mappers_require_the_runExternalCode_command_line_flag_to_be_enabled
            .code();
    for (name, get_parsed) in [
        (
            "json api",
            get_parsed_with_json_api
                as fn(&TestConfig, &Arc<dyn Vfs>, RootedDirectoryPath) -> ParsedCommandLine,
        ),
        ("jsonSourceFile api", get_parsed_with_json_source_file_api),
    ] {
        let mut files = vec![("/tsconfig.json", config.json_text)];
        files.extend(config.all_file_list.iter().copied());
        let fs = test_vfs(&files, CaseSensitivity::CaseSensitive);
        let parsed = get_parsed(&config, &fs, RootedDirectoryPath::from("/"));
        let errors = parsed.errors.lock().unwrap_or_else(|e| e.into_inner());
        let found = errors
            .iter()
            .any(|d| lock_diagnostic(d).code() == expected_code);
        assert!(found, "{name}: expected diagnostic {expected_code}");
    }
}

/// `TestUnresolvedContentMapperDoesNotRegisterExtensions`.
#[test]
fn test_unresolved_content_mapper_does_not_register_extensions() {
    let config = TestConfig {
        json_text: r#"{ "contentMappers": [{ "package": "missing-mapper", "extensions": [".vue"] }], "include": ["src"] }"#,
        config_file_name: "tsconfig.json",
        base_path: "/",
        all_file_list: vec![
            ("/src/app.ts", "export {}"),
            ("/src/Component.vue", "<template />"),
        ],
        existing_options: Some(CompilerOptions {
            run_external_code: TS_TRUE,
            ..Default::default()
        }),
    };
    for (name, get_parsed) in [
        (
            "json api",
            get_parsed_with_json_api
                as fn(&TestConfig, &Arc<dyn Vfs>, RootedDirectoryPath) -> ParsedCommandLine,
        ),
        ("jsonSourceFile api", get_parsed_with_json_source_file_api),
    ] {
        let fs = test_vfs(&config.all_file_list, CaseSensitivity::CaseSensitive);
        let parsed = get_parsed(&config, &fs, RootedDirectoryPath::from("/"));

        assert_eq!(parsed.content_mappers().len(), 0, "{name}");
        assert_eq!(parsed.content_mapper_extensions().len(), 0, "{name}");
        assert!(
            !parsed
                .file_names()
                .contains(&RootedFilePath::from("/src/Component.vue")),
            "{name}"
        );
        assert!(
            parsed
                .file_names()
                .contains(&RootedFilePath::from("/src/app.ts")),
            "{name}"
        );
    }
}

/// `TestContentMappersValidation`.
#[test]
fn test_content_mappers_validation() {
    struct Case {
        name: &'static str,
        content_mappers: &'static str,
        expected_code: i32,
    }
    let tests = [
        Case {
            name: "extension without leading dot",
            content_mappers: r#"[{ "package": "vue-mapper", "extensions": ["vue"] }]"#,
            expected_code: tsc_diagnostics::Content_mapper_file_extension_0_must_begin_with_a
                .code(),
        },
        Case {
            name: "built-in extension",
            content_mappers: r#"[{ "package": "x", "extensions": [".ts"] }]"#,
            expected_code:
                tsc_diagnostics::Content_mapper_file_extension_0_is_a_built_in_extension_and_cannot_be_registered_by_a_content_mapper
                    .code(),
        },
        Case {
            name: "missing extensions",
            content_mappers: r#"[{ "package": "x" }]"#,
            expected_code: tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1
                .code(),
        },
        Case {
            name: "duplicate extension across mappers",
            content_mappers: r#"[{ "package": "a", "extensions": [".vue"] }, { "package": "b", "extensions": [".vue"] }]"#,
            expected_code:
                tsc_diagnostics::Content_mapper_file_extension_0_is_registered_by_more_than_one_content_mapper
                    .code(),
        },
        Case {
            name: "extensions is not an array",
            content_mappers: r#"[{ "package": "x", "extensions": ".vue" }]"#,
            expected_code: tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1
                .code(),
        },
        Case {
            name: "extensions contains a non-string",
            content_mappers: r#"[{ "package": "x", "extensions": [".vue", 1] }]"#,
            expected_code: tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1
                .code(),
        },
        Case {
            name: "package is not a string",
            content_mappers: r#"[{ "package": ["x"], "extensions": [".vue"] }]"#,
            expected_code: tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1
                .code(),
        },
        Case {
            name: "missing package",
            content_mappers: r#"[{ "extensions": [".vue"] }]"#,
            expected_code: tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1
                .code(),
        },
        Case {
            name: "options is not an object",
            content_mappers: r#"[{ "package": "x", "extensions": [".vue"], "options": ["strict"] }]"#,
            expected_code: tsc_diagnostics::Compiler_option_0_requires_a_value_of_type_1
                .code(),
        },
    ];

    for test in tests {
        let mut all_file_list = vec![("/app.ts", "export {}")];
        if test.name == "duplicate extension across mappers" {
            all_file_list.push((
                "/node_modules/a/package.json",
                r#"{ "name": "a", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["a"] } } }"#,
            ));
            all_file_list.push((
                "/node_modules/b/package.json",
                r#"{ "name": "b", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["b"] } } }"#,
            ));
        }
        let json_text: String = format!("{{ \"contentMappers\": {} }}", test.content_mappers);
        let json_text: &'static str = Box::leak(json_text.into_boxed_str());
        let config = TestConfig {
            json_text,
            config_file_name: "tsconfig.json",
            base_path: "/",
            all_file_list,
            existing_options: Some(CompilerOptions {
                run_external_code: TS_TRUE,
                ..Default::default()
            }),
        };
        for (api_name, get_parsed) in [
            (
                "json api",
                get_parsed_with_json_api
                    as fn(&TestConfig, &Arc<dyn Vfs>, RootedDirectoryPath) -> ParsedCommandLine,
            ),
            ("jsonSourceFile api", get_parsed_with_json_source_file_api),
        ] {
            let mut files = vec![("/tsconfig.json", config.json_text)];
            files.extend(config.all_file_list.iter().copied());
            let fs = test_vfs(&files, CaseSensitivity::CaseSensitive);
            let parsed = get_parsed(&config, &fs, RootedDirectoryPath::from("/"));
            let errors = parsed.errors.lock().unwrap_or_else(|e| e.into_inner());
            let diagnostic = errors
                .iter()
                .find(|d| lock_diagnostic(d).code() == test.expected_code);
            assert!(
                diagnostic.is_some(),
                "{} ({}): expected diagnostic {}",
                test.name,
                api_name,
                test.expected_code
            );
            let diagnostic = diagnostic.unwrap();
            match test.name {
                "built-in extension" => {
                    assert_eq!(parsed.content_mappers().len(), 0, "{}", test.name);
                    assert_eq!(parsed.content_mapper_extensions().len(), 0, "{}", test.name);
                }
                "duplicate extension across mappers" => {
                    assert_eq!(parsed.content_mappers().len(), 2, "{}", test.name);
                    assert_eq!(
                        parsed.content_mappers()[0].extensions.as_deref(),
                        Some(&[".vue".to_string()][..]),
                        "{}",
                        test.name
                    );
                    assert_eq!(
                        parsed.content_mappers()[1]
                            .extensions
                            .as_deref()
                            .map_or(0, |e| e.len()),
                        0,
                        "{}",
                        test.name
                    );
                    assert_eq!(
                        parsed.content_mapper_extensions(),
                        &[".vue".to_string()],
                        "{}",
                        test.name
                    );
                }
                "missing extensions"
                | "extensions is not an array"
                | "extensions contains a non-string"
                | "package is not a string"
                | "missing package"
                | "options is not an object" => {
                    assert_eq!(parsed.content_mappers().len(), 0, "{}", test.name);
                }
                _ => {}
            }

            // With the jsonSourceFile API the diagnostic is located at the
            // offending tsconfig syntax.
            if api_name == "jsonSourceFile api" {
                let d = lock_diagnostic(diagnostic);
                assert!(
                    d.file().is_some(),
                    "{}: expected diagnostic {} to have a source file",
                    test.name,
                    test.expected_code
                );
                assert!(
                    d.len() > 0,
                    "{}: expected diagnostic {} to have a non-empty location",
                    test.name,
                    test.expected_code
                );
            }
        }
    }
}

/// `TestContentMapperExtensionValidationUsesHostCaseSensitivity`.
#[test]
fn test_content_mapper_extension_validation_uses_host_case_sensitivity() {
    struct Case {
        name: &'static str,
        case_sensitivity: CaseSensitivity,
        content_mappers: &'static str,
        expected_code: i32,
    }
    let tests = [
        Case {
            name: "built-in extension on case-insensitive host",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            content_mappers: r#"[{ "package": "mapper", "extensions": [".TS"] }]"#,
            expected_code:
                tsc_diagnostics::Content_mapper_file_extension_0_is_a_built_in_extension_and_cannot_be_registered_by_a_content_mapper
                    .code(),
        },
        Case {
            name: "duplicate extension on case-insensitive host",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            content_mappers: r#"[{ "package": "a", "extensions": [".vue"] }, { "package": "b", "extensions": [".VUE"] }]"#,
            expected_code:
                tsc_diagnostics::Content_mapper_file_extension_0_is_registered_by_more_than_one_content_mapper
                    .code(),
        },
        Case {
            name: "built-in extension on case-sensitive host",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            content_mappers: r#"[{ "package": "mapper", "extensions": [".TS"] }]"#,
            expected_code:
                tsc_diagnostics::Content_mapper_file_extension_0_is_a_built_in_extension_and_cannot_be_registered_by_a_content_mapper
                    .code(),
        },
        Case {
            name: "mapper extension casing is distinct on case-sensitive host",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            content_mappers: r#"[{ "package": "a", "extensions": [".vue"] }, { "package": "b", "extensions": [".VUE"] }]"#,
            expected_code: 0,
        },
    ];

    for test in tests {
        let json_text: String = format!("{{ \"contentMappers\": {} }}", test.content_mappers);
        let json_text: &'static str = Box::leak(json_text.into_boxed_str());
        let files: &[(&str, &str)] = &[
            ("/tsconfig.json", json_text),
            ("/app.ts", "export {};"),
            (
                "/node_modules/mapper/package.json",
                r#"{ "name": "mapper", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["mapper"] } } }"#,
            ),
            (
                "/node_modules/a/package.json",
                r#"{ "name": "a", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["a"] } } }"#,
            ),
            (
                "/node_modules/b/package.json",
                r#"{ "name": "b", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["b"] } } }"#,
            ),
        ];
        let fs = test_vfs(files, test.case_sensitivity);
        let config = TestConfig {
            json_text,
            config_file_name: "tsconfig.json",
            base_path: "/",
            all_file_list: files.to_vec(),
            existing_options: Some(CompilerOptions {
                run_external_code: TS_TRUE,
                ..Default::default()
            }),
        };
        let parsed =
            get_parsed_with_json_source_file_api(&config, &fs, RootedDirectoryPath::from("/"));
        let errors = parsed.errors.lock().unwrap_or_else(|e| e.into_inner());
        if test.expected_code == 0 {
            assert_eq!(errors.len(), 0, "{}: unexpected errors", test.name);
        } else {
            let found = errors
                .iter()
                .any(|d| lock_diagnostic(d).code() == test.expected_code);
            assert!(
                found,
                "{}: expected diagnostic {}",
                test.name, test.expected_code
            );
        }
    }
}

/// `TestParseTypeAcquisition`.
#[test]
fn test_parse_type_acquisition() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "Convert correctly format tsconfig.json to typeAcquisition ",
            "tsconfig.json",
            "{\n\t\"typeAcquisition\": {\n\t\t\"enable\": true,\n\t\t\"include\": [\"0.d.ts\", \"1.d.ts\"],\n\t\t\"exclude\": [\"0.js\", \"1.js\"],\n\t},\n}",
        ),
        (
            "Convert incorrect format tsconfig.json to typeAcquisition ",
            "tsconfig.json",
            "{\n\t\"typeAcquisition\": {\n\t\t\"enableAutoDiscovy\": true,\n\t}\n}",
        ),
        (
            "Convert default tsconfig.json to typeAcquisition ",
            "tsconfig.json",
            "{}",
        ),
        (
            "Convert tsconfig.json with only enable property to typeAcquisition ",
            "tsconfig.json",
            "{\n\t\"typeAcquisition\": {\n\t\t\"enable\": true,\n\t},\n}",
        ),
        // jsconfig.json
        (
            "Convert jsconfig.json to typeAcquisition ",
            "jsconfig.json",
            "{\n\t\"typeAcquisition\": {\n\t\t\"enable\": false,\n\t\t\"include\": [\"0.d.ts\"],\n\t\t\"exclude\": [\"0.js\"],\n\t},\n}",
        ),
        (
            "Convert default jsconfig.json to typeAcquisition ",
            "jsconfig.json",
            "{}",
        ),
        (
            "Convert incorrect format jsconfig.json to typeAcquisition ",
            "jsconfig.json",
            "{\n\t\"typeAcquisition\": {\n\t\t\"enableAutoDiscovy\": true,\n\t},\n}",
        ),
        (
            "Convert jsconfig.json with only enable property to typeAcquisition ",
            "jsconfig.json",
            "{\n\t\"typeAcquisition\": {\n\t\t\"enable\": false,\n\t},\n}",
        ),
    ];
    for (title, config_name, config) in cases {
        let input = vec![tc(
            config,
            config_name,
            "/apath",
            &[("/apath/a.ts", ""), ("/apath/b.ts", "")],
        )];
        baseline_parse_config_with(
            &format!("{title} with json api.js"),
            true,
            &input,
            get_parsed_with_json_api,
        );
        baseline_parse_config_with(
            &format!("{title} with jsonSourceFile api.js"),
            true,
            &input,
            get_parsed_with_json_source_file_api,
        );
    }
}

/// `TestParseSrcCompiler`.
#[test]
fn test_parse_src_compiler() {
    let compiler_dir =
        rooted_directory_path_from_absolute(&format!("{}/fixtures/compiler", test_data_path()));
    let tsconfig_file_name = compiler_dir.resolve_file("tsconfig.json");
    let fs = tsc_vfs::osvfs::fs();
    let json_text = fs
        .read_file(&tsconfig_file_name)
        .expect("read compiler tsconfig");
    let config_file = Arc::new(new_tsconfig_source_file_from_file_path(
        tsconfig_file_name.clone(),
        fs.case_sensitivity()
            .path_key(&RootedPath::from(tsconfig_file_name)),
        &json_text,
    ));
    let parsed = parse_json_source_file_config_file_content(
        &config_file,
        &fs,
        compiler_dir,
        None,
        None,
        &[],
        None,
    );
    assert_eq!(
        parsed
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len(),
        0,
        "expected no errors in parsed command line"
    );
    let opts = parsed.compiler_options().expect("compiler options");
    assert_eq!(opts.types.as_deref(), Some(&[][..]));
    assert_eq!(opts.module, ModuleKind::NodeNext);
    assert_eq!(opts.module_resolution, ModuleResolutionKind::NodeNext);
    assert_eq!(opts.target, ScriptTarget::ES2020);
    assert_eq!(parsed.file_names().len(), 79);
    let config_directory = opts.config_file_path.directory();
    for file in [
        "checker.ts",
        "diagnosticInformationMap.generated.ts",
        "node.d.ts",
        "program.ts",
    ] {
        assert!(
            parsed
                .file_names()
                .contains(&config_directory.resolve_file(file)),
            "expected {file} in file names"
        );
    }
}

/// `memoCache` — a minimal memoizing ExtendedConfigCache used by tests to
/// simulate cache hits across multiple parses of configs that extend a
/// common base.
#[derive(Default)]
struct MemoCache {
    m: Mutex<HashMap<PathKey, ExtendedConfigCacheEntry>>,
}

impl ExtendedConfigCache for MemoCache {
    fn get_extended_config(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        resolution_stack: &[PathKey],
        fs: &Arc<dyn Vfs>,
    ) -> Option<ExtendedConfigCacheEntry> {
        if let Some(e) = self.m.lock().unwrap_or_else(|e| e.into_inner()).get(path) {
            return Some(e.clone());
        }
        let e = parse_extended_config(file_name, path, resolution_stack, fs, Some(self));
        self.m
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(path.clone(), e.clone());
        Some(e)
    }
}

/// `TestExtendedConfigErrorsAppearOnCacheHit` — diagnostics produced while
/// parsing an extended config are still reported when the extended config
/// comes from the cache.
#[test]
fn test_extended_config_errors_appear_on_cache_hit() {
    // "single config parsed twice"
    {
        let files: &[(&str, &str)] = &[
            ("/tsconfig.json", "{\n  \"extends\": \"./base.json\"\n}"),
            // 'excludes' instead of 'exclude' triggers diagnostic
            ("/base.json", "{\n  \"excludes\": [\"**/*.ts\"]\n}"),
            ("/app.ts", "export {}"),
        ];
        let fs = test_vfs(files, CaseSensitivity::CaseSensitive);

        let parse_config = |config_file_name: &str, cache: &MemoCache| -> ParsedCommandLine {
            let config_file_name = RootedFilePath::from(config_file_name);
            let cfg_path = fs
                .case_sensitivity()
                .path_key(&RootedPath::from(config_file_name.clone()));
            let json_text = fs.read_file(&config_file_name).expect("read tsconfig");
            let ts_config_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
                config_file_name,
                cfg_path,
                &json_text,
            ));
            parse_json_source_file_config_file_content(
                &ts_config_source_file,
                &fs,
                RootedDirectoryPath::from("/"),
                None,
                None,
                &[],
                Some(cache),
            )
        };

        let cache = MemoCache::default();
        let first = parse_config("/tsconfig.json", &cache);
        assert!(
            !first
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .is_empty(),
            "expected diagnostics on first parse, got 0"
        );
        let second = parse_config("/tsconfig.json", &cache);
        assert!(
            !second
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .is_empty(),
            "expected diagnostics on second parse (cache hit), got 0"
        );
    }

    // "two configs share same base"
    {
        let files: &[(&str, &str)] = &[
            ("/base.json", "{\n  \"excludes\": [\"**/*.ts\"]\n}"),
            (
                "/projA/tsconfig.json",
                "{\n  \"extends\": \"../base.json\"\n}",
            ),
            (
                "/projB/tsconfig.json",
                "{\n  \"extends\": \"../base.json\"\n}",
            ),
            ("/projA/app.ts", "export {}"),
            ("/projB/app.ts", "export {}"),
        ];
        let fs = test_vfs(files, CaseSensitivity::CaseSensitive);

        let parse_config = |config_file_name: &str, cache: &MemoCache| -> ParsedCommandLine {
            let config_file_name = RootedFilePath::from(config_file_name);
            let cfg_path = fs
                .case_sensitivity()
                .path_key(&RootedPath::from(config_file_name.clone()));
            let json_text = fs.read_file(&config_file_name).expect("read tsconfig");
            let ts_config_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
                config_file_name,
                cfg_path,
                &json_text,
            ));
            parse_json_source_file_config_file_content(
                &ts_config_source_file,
                &fs,
                RootedDirectoryPath::from("/"),
                None,
                None,
                &[],
                Some(cache),
            )
        };

        let cache = MemoCache::default();
        let first = parse_config("/projA/tsconfig.json", &cache);
        assert!(
            !first
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .is_empty(),
            "expected diagnostics for projA parse, got 0"
        );
        let second = parse_config("/projB/tsconfig.json", &cache);
        assert!(
            !second
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .is_empty(),
            "expected diagnostics for projB parse (cache hit on base), got 0"
        );
    }
}

/// `TestExtendedConfigConfigDirPathsAreNotCached`.
#[test]
fn test_extended_config_config_dir_paths_are_not_cached() {
    let files: &[(&str, &str)] = &[
        (
            "/tsconfig.base.json",
            "{\n  \"compilerOptions\": {\n    \"paths\": {\n      \"@pkg/*\": [\"${configDir}/src/*\"]\n    }\n  }\n}",
        ),
        (
            "/packages/a/tsconfig.json",
            "{\n  \"extends\": \"../../tsconfig.base.json\"\n}",
        ),
        (
            "/packages/b/tsconfig.json",
            "{\n  \"extends\": \"../../tsconfig.base.json\"\n}",
        ),
        ("/packages/a/index.ts", "export {}"),
        ("/packages/b/index.ts", "export {}"),
    ];
    let fs = test_vfs(files, CaseSensitivity::CaseSensitive);
    let cache = MemoCache::default();

    let parse_config = |config_file_name: &str| -> ParsedCommandLine {
        get_parsed_command_line_of_config_file(
            RootedFilePath::from(config_file_name),
            None,
            None,
            &fs,
            Some(&cache),
        )
        .unwrap_or_else(|errors| {
            panic!(
                "unexpected errors parsing {config_file_name}: {} errors",
                errors.len()
            )
        })
    };

    parse_config("/packages/a/tsconfig.json");
    let paths = parse_config("/packages/b/tsconfig.json")
        .compiler_options()
        .expect("compiler options")
        .paths
        .clone()
        .expect("paths");
    assert_eq!(
        paths.get("@pkg/*").and_then(|v| v.as_deref()),
        Some(&["/packages/b/src/*".to_string()][..])
    );
}
