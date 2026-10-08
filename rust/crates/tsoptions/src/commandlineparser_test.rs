// Ported from tsc/internal/tsoptions/commandlineparser_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::commandlineparser::{parse_build_command_line, parse_command_line};
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath};
use tsc_vfs::vfstest;

/// `TestParseCommandLineTypeRootsRelativePath`.
#[test]
fn test_parse_command_line_type_roots_relative_path() {
    let fs = vfstest::from_map(
        [("/home/project/bug.ts", "let x = 1;")],
        CaseSensitivity::CaseSensitive,
    );

    let cmd_line = parse_command_line(
        &["--typeRoots".into(), "t".into(), "bug.ts".into()],
        &fs,
        RootedDirectoryPath::from("/home/project"),
    );

    let type_roots = cmd_line
        .compiler_options()
        .and_then(|o| o.type_roots.clone())
        .expect("typeRoots should not be nil");
    assert_eq!(type_roots.len(), 1);
    assert_eq!(type_roots[0], RootedDirectoryPath::from("/home/project/t"));
}

/// `TestRemovedWatchOptions` — the assertion part (baseline output is not
/// ported).
#[test]
fn test_removed_watch_options() {
    let fs = vfstest::from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseSensitive,
    );
    let current_directory = RootedDirectoryPath::from("/project");
    for option in [
        "watchInterval",
        "watchFile",
        "watchDirectory",
        "fallbackPolling",
        "synchronousWatchDirectory",
        "excludeDirectories",
        "excludeFiles",
    ] {
        let args = vec!["--watch".to_string(), format!("--{}", option)];
        let parsed = parse_command_line(&args, &fs, current_directory.clone());
        assert!(
            parsed.compiler_options().is_some_and(|o| o.watch.is_true()),
            "{option}"
        );
        assert_eq!(
            parsed
                .errors
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .len(),
            1,
            "{option}"
        );
        let build = parse_build_command_line(&args, &fs, current_directory.clone());
        assert!(
            build
                .compiler_options
                .as_ref()
                .is_some_and(|o| o.watch.is_true()),
            "{option}"
        );
        assert_eq!(build.errors.len(), 1, "{option}");
    }
}

/// `TestResponseFileParsing`.
#[test]
fn test_response_file_parsing() {
    // final token without trailing whitespace
    let fs = vfstest::from_map(
        [("/project/args.txt", "--strict --outDir dist")],
        CaseSensitivity::CaseSensitive,
    );
    let parsed = parse_command_line(
        &["@args.txt".into()],
        &fs,
        RootedDirectoryPath::from("/project"),
    );
    assert_eq!(
        parsed
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len(),
        0
    );
    assert!(
        parsed
            .compiler_options()
            .is_some_and(|o| o.strict.is_true())
    );
    assert_eq!(
        parsed.compiler_options().unwrap().out_dir,
        RootedDirectoryPath::from("/project/dist")
    );

    // cyclic response files
    let fs = vfstest::from_map(
        [
            ("/project/a.txt", "@/project/b.txt --strict"),
            ("/project/b.txt", "@/project/a.txt --outDir dist"),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let parsed = parse_command_line(
        &["@a.txt".into()],
        &fs,
        RootedDirectoryPath::from("/project"),
    );
    assert_eq!(
        parsed
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len(),
        0
    );
    assert!(
        parsed
            .compiler_options()
            .is_some_and(|o| o.strict.is_true())
    );
    assert_eq!(
        parsed.compiler_options().unwrap().out_dir,
        RootedDirectoryPath::from("/project/dist")
    );
}

/// `TestResponseFileDoesNotPanic` — passing `@` with an empty or relative
/// filename should not panic; it should produce a diagnostic error instead.
#[test]
fn test_response_file_does_not_panic() {
    let cwd = rooted_directory_path_from_absolute(
        std::env::temp_dir().to_str().expect("temp dir is UTF-8"),
    );
    let parsed =
        parse_command_line_test_worker(Vec::new(), &["@".to_string()], os_fs(), cwd.clone());
    assert!(
        !parsed.errors.is_empty(),
        "expected an error for empty response file name"
    );

    let parsed = parse_command_line_test_worker(Vec::new(), &["@blah".to_string()], os_fs(), cwd);
    assert!(
        !parsed.errors.is_empty(),
        "expected an error for non-existent response file"
    );
}

// ---------------------------------------------------------------------------
// Baseline-driven scenarios (`TestCommandLineParseResult`,
// `TestParseCommandLineVerifyNull`, `TestParseBuildCommandLine`)
// ---------------------------------------------------------------------------

use std::sync::Arc;

use crate::commandlineoption::{
    CommandLineOption, CommandLineOptionKind, CommandLineOptionRef, DefaultValueDescription,
};
use crate::commandlineparser::parse_command_line_test_worker;
use crate::generated::declarations;
use tsc_core::options_generated::{BuildOptions, CompilerOptions};
use tsc_testutil::baseline;
use tsc_tspath::rooted_directory_path_from_absolute;
use tsc_vfs::Vfs;

/// `filefixture.FromFile` — the reference baseline under
/// `testdata/fixtures/typescript/tests/baselines/reference/config/commandLineParsing`.
fn read_sub_scenario_baseline(sub_scenario_name: &str) -> String {
    let path = format!(
        "{}/fixtures/typescript/tests/baselines/reference/config/commandLineParsing/{sub_scenario_name}.js",
        tsc_repo::test_data_path()
    );
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("could not read baseline {path}: {e}"))
}

/// `parseExistingCompilerBaseline` — the fixture format separates sections
/// with `X::` headers on their own lines.
fn parse_existing_compiler_baseline(baseline: &str) -> (CompilerOptions, String, String) {
    let (_, rest, _) = cut(baseline, "CompilerOptions::\n");
    let (compiler_options, rest, _) = cut(&rest, "\nWatchOptions::\n");
    let (_, rest, _) = cut(&rest, "\nFileNames::\n");
    let (file_names, errors, _) = cut(&rest, "\nErrors::\n");
    let baseline_compiler_options: CompilerOptions =
        serde_json::from_str(&compiler_options).expect("baseline CompilerOptions unmarshal");
    (baseline_compiler_options, file_names, errors)
}

/// `parseExistingCompilerBaselineBuild`.
fn parse_existing_compiler_baseline_build(
    baseline: &str,
) -> (BuildOptions, CompilerOptions, String, String) {
    let (_, rest, _) = cut(baseline, "buildOptions::\n");
    let (build_options, rest, _) = cut(&rest, "\nWatchOptions::\n");
    let (_, rest, _) = cut(&rest, "\nProjects::\n");
    let (projects, errors, _) = cut(&rest, "\nErrors::\n");
    let baseline_build_options: BuildOptions =
        serde_json::from_str(&build_options).expect("baseline BuildOptions unmarshal");
    let baseline_compiler_options: CompilerOptions =
        serde_json::from_str(&build_options).expect("baseline CompilerOptions unmarshal");
    (
        baseline_build_options,
        baseline_compiler_options,
        projects,
        errors,
    )
}

/// Go `json.Unmarshal` treats `null` members as no-ops; serde rejects them
/// for non-Option fields, so drop them before decoding (same result).
fn unmarshal_options_go_semantics<T: serde::de::DeserializeOwned>(json: &str) -> T {
    let mut v: serde_json::Value = serde_json::from_str(json).expect("parse options json");
    if let Some(obj) = v.as_object_mut() {
        obj.retain(|_, val| !val.is_null());
    }
    serde_json::from_value(v).expect("unmarshal options")
}

fn cut(s: &str, sep: &str) -> (String, String, bool) {
    match s.split_once(sep) {
        Some((a, b)) => (a.to_string(), b.to_string(), true),
        None => (s.to_string(), String::new(), false),
    }
}

fn os_fs() -> Arc<dyn Vfs> {
    tsc_vfs::osvfs::fs()
}

fn temp_dir() -> RootedDirectoryPath {
    rooted_directory_path_from_absolute(std::env::temp_dir().to_str().expect("temp dir is UTF-8"))
}

/// `formatNewBaseline`.
fn format_new_baseline(
    command_line: &[String],
    opts: &str,
    file_names: &str,
    errors: &str,
) -> String {
    let mut formatted = String::new();
    formatted.push_str("Args::\n[");
    for (i, arg) in command_line.iter().enumerate() {
        if i > 0 {
            formatted.push_str(", ");
        }
        formatted.push('"');
        formatted.push_str(arg);
        formatted.push('"');
    }
    formatted.push(']');
    formatted.push_str("\n\nCompilerOptions::\n");
    formatted.push_str(opts);
    formatted.push_str("\n\nFileNames::\n");
    formatted.push_str(file_names);
    formatted.push_str("\n\nErrors::\n");
    formatted.push_str(errors);
    formatted
}

/// `formatNewBaselineBuild`.
fn format_new_baseline_build(
    command_line: &[String],
    opts: &str,
    compiler_opts: &str,
    projects: &str,
    errors: &str,
) -> String {
    let mut formatted = String::new();
    formatted.push_str("Args::\n[");
    for (i, arg) in command_line.iter().enumerate() {
        if i > 0 {
            formatted.push_str(", ");
        }
        formatted.push('"');
        formatted.push_str(arg);
        formatted.push('"');
    }
    formatted.push(']');
    formatted.push_str("\n\nbuildOptions::\n");
    formatted.push_str(opts);
    formatted.push_str("\n\ncompilerOptions::\n");
    formatted.push_str(compiler_opts);
    formatted.push_str("\n\nProjects::\n");
    formatted.push_str(projects);
    formatted.push_str("\n\nErrors::\n");
    formatted.push_str(errors);
    formatted
}

fn format_errors(errors: &[tsc_ast::diagnostic::DiagnosticRef]) -> String {
    let mut formatted = Vec::new();
    let diags = tsc_diagnosticwriter::from_ast_diagnostics(errors, &[]);
    tsc_diagnosticwriter::write_format_diagnostics(
        &mut formatted,
        &diags,
        &tsc_diagnosticwriter::FormattingOptions {
            new_line: "\n".into(),
            ..Default::default()
        },
    );
    String::from_utf8(formatted).expect("diagnostics are UTF-8")
}

/// `commandLineSubScenario.assertParseResult`.
fn assert_parse_result(
    test_name: &str,
    command_line: &[&str],
    opt_decls: Vec<CommandLineOptionRef>,
) {
    let sub_scenario_name = format!("parseCommandLine/{test_name}");
    let original_baseline = read_sub_scenario_baseline(&sub_scenario_name);
    let (baseline_options, baseline_file_names, _baseline_errors) =
        parse_existing_compiler_baseline(&original_baseline);

    let args: Vec<String> = command_line.iter().map(|s| s.to_string()).collect();
    let parsed = parse_command_line_test_worker(opt_decls, &args, os_fs(), temp_dir());

    let new_baseline_file_names = parsed.file_names.join(",");
    assert_eq!(baseline_file_names, new_baseline_file_names);

    let o = serde_json::to_string(&parsed.options).expect("marshal options");
    let new_parsed_compiler_options: CompilerOptions = unmarshal_options_go_semantics(&o);
    // Go compares with reflect.DeepEqual; serde value equality is the closest
    // field-wise comparison available.
    assert_eq!(
        serde_json::to_value(&baseline_options).unwrap(),
        serde_json::to_value(&new_parsed_compiler_options).unwrap(),
    );

    let new_baseline_errors = format_errors(&parsed.errors);

    baseline::run(
        &format!("{sub_scenario_name}.js"),
        &format_new_baseline(&args, &o, &new_baseline_file_names, &new_baseline_errors),
        &baseline::Options {
            subfolder: "tsoptions/commandLineParsing".into(),
            ..Default::default()
        },
    )
    .expect("baseline");
}

/// `commandLineSubScenario.assertBuildParseResult`.
fn assert_build_parse_result(test_name: &str, command_line: &[&str], with_ts_baseline: bool) {
    let sub_scenario_name = format!("parseBuildOptions/{test_name}");
    let ts_baseline = if with_ts_baseline {
        let original_baseline = read_sub_scenario_baseline(&sub_scenario_name);
        Some(parse_existing_compiler_baseline_build(&original_baseline))
    } else {
        None
    };

    let args: Vec<String> = command_line.iter().map(|s| s.to_string()).collect();
    let current_directory = rooted_directory_path_from_absolute(tsc_repo::test_data_path());
    let parsed = parse_build_command_line(&args, &os_fs(), current_directory);

    let new_baseline_projects = parsed.projects.join(",");
    if let Some((_, _, projects, _)) = &ts_baseline {
        assert_eq!(projects, &new_baseline_projects);
    }

    let o = serde_json::to_string(&parsed.build_options.clone().unwrap_or_default())
        .expect("marshal build options");
    let new_parsed_build_options: BuildOptions = unmarshal_options_go_semantics(&o);
    let compiler_opts = serde_json::to_string(&parsed.compiler_options.clone().unwrap_or_default())
        .expect("marshal compiler options");
    let new_parsed_compiler_options: CompilerOptions =
        unmarshal_options_go_semantics(&compiler_opts);

    if let Some((baseline_build_options, baseline_compiler_options, _, _)) = &ts_baseline {
        assert_eq!(
            serde_json::to_value(baseline_build_options).unwrap(),
            serde_json::to_value(&new_parsed_build_options).unwrap(),
        );
        assert_eq!(
            serde_json::to_value(baseline_compiler_options).unwrap(),
            serde_json::to_value(&new_parsed_compiler_options).unwrap(),
        );
    }

    let new_baseline_errors = format_errors(&parsed.errors);

    baseline::run(
        &format!("{sub_scenario_name}.js"),
        &format_new_baseline_build(
            &args,
            &o,
            &compiler_opts,
            &new_baseline_projects,
            &new_baseline_errors,
        ),
        &baseline::Options {
            subfolder: "tsoptions/commandLineParsing".into(),
            ..Default::default()
        },
    )
    .expect("baseline");
}

/// `TestCommandLineParseResult`.
#[test]
fn test_command_line_parse_result() {
    let scenarios: &[(&str, &[&str])] = &[
        (
            "Parse single option of library flag",
            &["--lib", "es6", "0.ts"],
        ),
        (
            "Handles may only be used with --build flags",
            &["--build", "--clean", "--dry", "--force", "--verbose"],
        ),
        (
            "Handles did you mean for misspelt flags",
            &["--declarations", "--allowTS"],
        ),
        (
            "Parse multiple options of library flags",
            &["--lib", "es5,es2015.symbol.wellknown", "0.ts"],
        ),
        (
            "Parse invalid option of library flags",
            &["--lib", "es5,invalidOption", "0.ts"],
        ),
        ("Parse empty options of --jsx", &["0.ts", "--jsx"]),
        ("Parse empty options of --module", &["0.ts", "--module"]),
        ("Parse empty options of --newLine", &["0.ts", "--newLine"]),
        ("Parse empty options of --target", &["0.ts", "--target"]),
        (
            "Parse empty options of --moduleResolution",
            &["0.ts", "--moduleResolution"],
        ),
        ("Parse empty options of --lib", &["0.ts", "--lib"]),
        // This test is an error because the empty string is falsey
        ("Parse empty string of --lib", &["0.ts", "--lib", ""]),
        (
            "Parse immediately following command line argument of --lib",
            &["0.ts", "--lib", "--sourcemap"],
        ),
        (
            "Parse --lib option with extra comma",
            &["--lib", "es5,", "es7", "0.ts"],
        ),
        (
            "Parse --lib option with trailing white-space",
            &["--lib", "es5, ", "es7", "0.ts"],
        ),
        (
            "Parse multiple compiler flags with input files at the end",
            &[
                "--lib",
                "es5,es2015.symbol.wellknown",
                "--target",
                "es5",
                "0.ts",
            ],
        ),
        (
            "Parse multiple compiler flags with input files in the middle",
            &[
                "--module",
                "commonjs",
                "--target",
                "es5",
                "0.ts",
                "--lib",
                "es5,es2015.symbol.wellknown",
            ],
        ),
        (
            "Parse multiple library compiler flags ",
            &[
                "--module",
                "commonjs",
                "--target",
                "es5",
                "--lib",
                "es5",
                "0.ts",
                "--lib",
                "es2015.core, es2015.symbol.wellknown ",
            ],
        ),
        (
            "Parse explicit boolean flag value",
            &["--strictNullChecks", "false", "0.ts"],
        ),
        (
            "Parse non boolean argument after boolean flag",
            &["--noImplicitAny", "t", "0.ts"],
        ),
        ("Parse implicit boolean flag value", &["--strictNullChecks"]),
        ("parse --incremental", &["--incremental", "0.ts"]),
        (
            "parse --tsBuildInfoFile",
            &["--tsBuildInfoFile", "build.tsbuildinfo", "0.ts"],
        ),
        (
            "allows tsconfig only option to be set to null",
            &["--composite", "null", "-tsBuildInfoFile", "null", "0.ts"],
        ),
    ];
    for (name, command_line) in scenarios {
        assert_parse_result(name, command_line, Vec::new());
    }
}

/// `createVerifyNullForNonNullIncluded`.
fn verify_null_option_decls(kind: CommandLineOptionKind) -> Vec<CommandLineOptionRef> {
    let option = Box::leak(Box::new(CommandLineOption {
        name: "optionName",
        short_name: "",
        kind,
        path_kind: crate::commandlineoption::CommandLineOptionPathKind::None,
        is_file_path: false,
        is_ts_config_only: true,
        is_command_line_only: false,
        description: Some(&tsc_diagnostics::Enable_project_compilation),
        default_value_description: DefaultValueDescription::None,
        show_in_simplified_help_view: false,
        category: Some(&tsc_diagnostics::Backwards_Compatibility),
        extra_validation: None,
        min_value: 0,
        list_preserve_falsy_values: false,
        element_options: None,
    }));
    let mut decls: Vec<CommandLineOptionRef> = declarations::options_declarations().collect();
    decls.push(option);
    decls
}

/// `TestParseCommandLineVerifyNull`.
#[test]
fn test_parse_command_line_verify_null() {
    // "allows setting option type boolean to false"
    assert_parse_result(
        "allows setting option type boolean to false",
        &["--composite", "false", "0.ts"],
        Vec::new(),
    );

    struct VerifyNull {
        sub_scenario: &'static str,
        option_name: &'static str,
        non_null_value: &'static str,
        decls: Option<Vec<CommandLineOptionRef>>,
    }
    let verify_null_cases = [
        VerifyNull {
            sub_scenario: "option of type boolean",
            option_name: "composite",
            non_null_value: "true",
            decls: None,
        },
        VerifyNull {
            sub_scenario: "option of type object",
            option_name: "paths",
            non_null_value: "",
            decls: None,
        },
        VerifyNull {
            sub_scenario: "option of type list",
            option_name: "rootDirs",
            non_null_value: "abc,xyz",
            decls: None,
        },
        VerifyNull {
            sub_scenario: "option of type string",
            option_name: "optionName",
            non_null_value: "hello",
            decls: Some(verify_null_option_decls(CommandLineOptionKind::String)),
        },
        VerifyNull {
            sub_scenario: "option of type number",
            option_name: "optionName",
            non_null_value: "10",
            decls: Some(verify_null_option_decls(CommandLineOptionKind::Number)),
        },
    ];
    for case in verify_null_cases {
        let decls = || case.decls.clone().unwrap_or_default();
        assert_parse_result(
            &format!("{} allows setting it to null", case.sub_scenario),
            &[&format!("--{}", case.option_name), "null", "0.ts"],
            decls(),
        );
        if !case.non_null_value.is_empty() {
            assert_parse_result(
                &format!("{} errors if non null value is passed", case.sub_scenario),
                &[
                    &format!("--{}", case.option_name),
                    case.non_null_value,
                    "0.ts",
                ],
                decls(),
            );
        }
        assert_parse_result(
            &format!(
                "{} errors if its followed by another option",
                case.sub_scenario
            ),
            &[
                "0.ts",
                "--strictNullChecks",
                &format!("--{}", case.option_name),
            ],
            decls(),
        );
        assert_parse_result(
            &format!("{} errors if its last option", case.sub_scenario),
            &["0.ts", &format!("--{}", case.option_name)],
            decls(),
        );
    }
}

/// `TestParseBuildCommandLine`.
#[test]
fn test_parse_build_command_line() {
    let scenarios: &[(&str, &[&str])] = &[
        ("parse build without any options ", &[]),
        ("Parse multiple options", &["--verbose", "--force", "tests"]),
        (
            "Parse option with invalid option",
            &["--verbose", "--invalidOption"],
        ),
        (
            "Parse multiple flags with input projects at the end",
            &["--force", "--verbose", "src", "tests"],
        ),
        (
            "Parse multiple flags with input projects in the middle",
            &["--force", "src", "tests", "--verbose"],
        ),
        (
            "Parse multiple flags with input projects in the beginning",
            &["src", "tests", "--force", "--verbose"],
        ),
        (
            "parse build with --incremental",
            &["--incremental", "tests"],
        ),
        (
            "parse build with --locale en-us",
            &["--locale", "en-us", "src"],
        ),
        (
            "parse build with --tsBuildInfoFile",
            &["--tsBuildInfoFile", "build.tsbuildinfo", "tests"],
        ),
        (
            "reports other common may not be used with --build flags",
            &["--strict"],
        ),
        (
            "--clean and --force together is invalid",
            &["--clean", "--force"],
        ),
        (
            "--clean and --verbose together is invalid",
            &["--clean", "--verbose"],
        ),
        (
            "--clean and --watch together is invalid",
            &["--clean", "--watch"],
        ),
        (
            "--watch and --dry together is invalid",
            &["--watch", "--dry"],
        ),
    ];
    for (name, command_line) in scenarios {
        assert_build_parse_result(name, command_line, true);
    }

    let extra_scenarios: &[(&str, &[&str])] = &[
        ("parse --builders", &["--builders", "2"]),
        (
            "--singleThreaded and --builders together",
            &["--singleThreaded", "--builders", "2"],
        ),
        ("reports error when --builders is 0", &["--builders", "0"]),
        (
            "reports error when --builders is negative",
            &["--builders", "-1"],
        ),
        (
            "reports error when --builders is invalid type",
            &["--builders", "invalid"],
        ),
    ];
    for (name, command_line) in extra_scenarios {
        assert_build_parse_result(name, command_line, false);
    }
}
