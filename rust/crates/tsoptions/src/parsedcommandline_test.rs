// Ported from tsc/internal/tsoptions/parsedcommandline_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;
use std::sync::Arc;

use crate::parsedcommandline::ParsedCommandLine;
use crate::tsconfigparsing::{
    new_tsconfig_source_file_from_file_path, parse_json_source_file_config_file_content,
};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;
use tsc_tspath::{
    CaseSensitivity, RootedDirectoryPath, RootedFilePath, path_key_from_canonical,
    rooted_file_path_from_normalized, to_rooted_file_path,
};
use tsc_vfs::vfstest;

/// `tsoptionstest.GetParsedCommandLine`.
fn get_parsed_command_line(
    json_text: &str,
    files: &[(&str, &str)],
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> ParsedCommandLine {
    let fs = vfstest::from_map(files.iter().copied(), case_sensitivity);
    let config_file_name = current_directory.resolve_file("tsconfig.json");
    let tsconfig_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name.clone(),
        case_sensitivity.path_key(&config_file_name.as_path()),
        json_text,
    ));
    parse_json_source_file_config_file_content(
        &tsconfig_source_file,
        &fs,
        current_directory.clone(),
        None,
        None,
        &[],
        None,
    )
}

fn dev_files() -> Vec<(&'static str, &'static str)> {
    vec![
        ("/dev/a.ts", ""),
        ("/dev/a.d.ts", ""),
        ("/dev/a.js", ""),
        ("/dev/b.ts", ""),
        ("/dev/b.js", ""),
        ("/dev/c.d.ts", ""),
        ("/dev/z/a.ts", ""),
        ("/dev/z/abz.ts", ""),
        ("/dev/z/aba.ts", ""),
        ("/dev/z/b.ts", ""),
        ("/dev/z/bbz.ts", ""),
        ("/dev/z/bba.ts", ""),
        ("/dev/x/a.ts", ""),
        ("/dev/x/aa.ts", ""),
        ("/dev/x/b.ts", ""),
        ("/dev/x/y/a.ts", ""),
        ("/dev/x/y/b.ts", ""),
        ("/dev/js/a.js", ""),
        ("/dev/js/b.js", ""),
        ("/dev/js/d.min.js", ""),
        ("/dev/js/ab.min.js", ""),
        ("/ext/ext.ts", ""),
        ("/ext/b/a..b.ts", ""),
    ]
}

fn assert_matches(
    parsed_command_line: &ParsedCommandLine,
    files: &[(&str, &str)],
    matches: &[&str],
) {
    for (file_name, _) in files {
        let actual = parsed_command_line.possibly_matches_file_name(&to_rooted_file_path(
            file_name,
            parsed_command_line.base_directory(),
        ));
        let expected = matches.contains(file_name);
        assert_eq!(actual, expected, "fileName: {file_name}");
    }
    for file_name in matches {
        if !files.iter().any(|(name, _)| name == file_name) {
            let actual = parsed_command_line.possibly_matches_file_name(&to_rooted_file_path(
                file_name,
                parsed_command_line.base_directory(),
            ));
            assert!(actual, "fileName: {file_name}");
        }
    }
}

/// `TestParsedCommandLine/PossiblyMatchesFileName/with literal file list/without exclude`.
#[test]
fn test_literal_file_list_without_exclude() {
    let files = dev_files();
    let parsed_command_line = get_parsed_command_line(
        r#"{
            "files": [
                "a.ts",
                "b.ts"
            ]
        }"#,
        &files,
        &RootedDirectoryPath::from("/dev"),
        CaseSensitivity::CaseSensitive,
    );
    assert_matches(&parsed_command_line, &files, &["/dev/a.ts", "/dev/b.ts"]);
}

/// `.../with literal file list/are not removed due to excludes`.
#[test]
fn test_literal_file_list_are_not_removed_due_to_excludes() {
    let files = dev_files();
    let parsed_command_line = get_parsed_command_line(
        r#"{
            "files": [
                "a.ts",
                "b.ts"
            ],
            "exclude": [
                "b.ts"
            ]
        }"#,
        &files,
        &RootedDirectoryPath::from("/dev"),
        CaseSensitivity::CaseSensitive,
    );
    assert_matches(&parsed_command_line, &files, &["/dev/a.ts", "/dev/b.ts"]);

    let no_files_fs = vfstest::from_map(Vec::<(&str, &str)>::new(), CaseSensitivity::CaseSensitive);
    let empty_parsed_command_line =
        parsed_command_line.reload_file_names_of_parsed_command_line(&no_files_fs);
    assert_matches(&empty_parsed_command_line, &[], &["/dev/a.ts", "/dev/b.ts"]);
}

/// `.../with literal file list/duplicates`.
#[test]
fn test_literal_file_list_duplicates() {
    let files = dev_files();
    let parsed_command_line = get_parsed_command_line(
        r#"{
            "files": [
                "a.ts",
                "a.ts",
                "b.ts",
            ]
        }"#,
        &files,
        &RootedDirectoryPath::from("/dev"),
        CaseSensitivity::CaseSensitive,
    );
    assert_eq!(
        parsed_command_line.literal_file_names(),
        Some(
            [
                RootedFilePath::from("/dev/a.ts"),
                RootedFilePath::from("/dev/b.ts")
            ]
            .as_slice()
        )
    );
}

/// `.../with literal include list/without exclude`.
#[test]
fn test_literal_include_list_without_exclude() {
    let files = dev_files();
    let parsed_command_line = get_parsed_command_line(
        r#"{
            "include": [
                "a.ts",
                "b.ts"
            ]
        }"#,
        &files,
        &RootedDirectoryPath::from("/dev"),
        CaseSensitivity::CaseSensitive,
    );
    assert_matches(&parsed_command_line, &files, &["/dev/a.ts", "/dev/b.ts"]);

    let no_files_fs = vfstest::from_map(Vec::<(&str, &str)>::new(), CaseSensitivity::CaseSensitive);
    let empty_parsed_command_line =
        parsed_command_line.reload_file_names_of_parsed_command_line(&no_files_fs);
    assert_matches(&empty_parsed_command_line, &[], &["/dev/a.ts", "/dev/b.ts"]);
}

/// `.../PossiblyMatchesFileName with content mapper extensions`.
#[test]
fn test_possibly_matches_file_name_with_content_mapper_extensions() {
    let mapper_package_json = r#"{ "name": "mapper", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["mapper"] } } }"#;
    let fs = vfstest::from_map(
        [("/dev/node_modules/mapper/package.json", mapper_package_json)],
        CaseSensitivity::CaseSensitive,
    );
    let config_file_name = "/dev/tsconfig.json";
    let json_text = r#"{
    "include": ["src"],
    "contentMappers": [ { "package": "mapper", "extensions": [".box"] } ]
}"#;
    let tsconfig_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        rooted_file_path_from_normalized(config_file_name),
        path_key_from_canonical(config_file_name),
        json_text,
    ));
    let mut existing_options = CompilerOptions::default();
    existing_options.run_external_code = TS_TRUE;
    let parsed_command_line = parse_json_source_file_config_file_content(
        &tsconfig_source_file,
        &fs,
        RootedDirectoryPath::from("/dev"),
        Some(&existing_options),
        None,
        &[],
        None,
    );

    // A created content-mapped file under an included directory must be
    // recognized as a possible root file, or the config's root files are never
    // reloaded for it.
    assert!(
        parsed_command_line.possibly_matches_file_name(&RootedFilePath::from("/dev/src/new.box"))
    );
    assert!(
        parsed_command_line.possibly_matches_file_name(&RootedFilePath::from("/dev/src/new.ts"))
    );
    assert!(
        !parsed_command_line.possibly_matches_file_name(&RootedFilePath::from("/dev/src/new.vue"))
    );
    assert!(
        !parsed_command_line
            .possibly_matches_file_name(&RootedFilePath::from("/dev/other/new.box"))
    );

    let insensitive_fs = vfstest::from_map(
        [("/dev/node_modules/mapper/package.json", mapper_package_json)],
        CaseSensitivity::CaseInsensitive,
    );
    let insensitive_command_line = parse_json_source_file_config_file_content(
        &tsconfig_source_file,
        &insensitive_fs,
        RootedDirectoryPath::from("/dev"),
        Some(&existing_options),
        None,
        &[],
        None,
    );
    assert!(
        insensitive_command_line
            .possibly_matches_file_name(&RootedFilePath::from("/dev/src/new.BOX"))
    );
}

/// `.../Config file specs are owned by the parsed command line`.
#[test]
fn test_config_file_specs_are_owned_by_the_parsed_command_line() {
    let config_file_name = RootedFilePath::from("/dev/tsconfig.json");
    let tsconfig_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        config_file_name.clone(),
        CaseSensitivity::CaseSensitive.path_key(&config_file_name.as_path()),
        r#"{ "files": ["SRC/a.ts"] }"#,
    ));
    let sensitive_command_line = parse_json_source_file_config_file_content(
        &tsconfig_source_file,
        &vfstest::from_map(Vec::<(&str, &str)>::new(), CaseSensitivity::CaseSensitive),
        RootedDirectoryPath::from("/dev"),
        None,
        None,
        &[],
        None,
    );
    let _ = parse_json_source_file_config_file_content(
        &tsconfig_source_file,
        &vfstest::from_map(Vec::<(&str, &str)>::new(), CaseSensitivity::CaseInsensitive),
        RootedDirectoryPath::from("/dev"),
        None,
        None,
        &[],
        None,
    );

    assert_eq!(
        sensitive_command_line.get_matched_file_spec(&RootedFilePath::from("/dev/SRC/a.ts")),
        "SRC/a.ts"
    );
}

/// `.../Literal files and include matches share canonical keys`.
#[test]
fn test_literal_files_and_include_matches_share_canonical_keys() {
    let fs = vfstest::from_map([("/dev/src/a.ts", "")], CaseSensitivity::CaseSensitive);
    let config_file_name = RootedFilePath::from("/dev/tsconfig.json");
    let command_line = parse_json_source_file_config_file_content(
        &Arc::new(new_tsconfig_source_file_from_file_path(
            config_file_name.clone(),
            CaseSensitivity::CaseSensitive.path_key(&config_file_name.as_path()),
            r#"{ "files": ["src/a.ts"], "include": ["src/*.ts"] }"#,
        )),
        &fs,
        RootedDirectoryPath::from("/dev"),
        None,
        None,
        &[],
        None,
    );

    assert_eq!(
        command_line.file_names(),
        &[RootedFilePath::from("/dev/src/a.ts")]
    );
}

/// `.../WithFileNames preserves config identity`.
#[test]
fn test_with_file_names_preserves_config_identity() {
    let config_file_name = "/dev/tsconfig.json";
    let tsconfig_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
        rooted_file_path_from_normalized(config_file_name),
        path_key_from_canonical(config_file_name),
        "{}",
    ));
    let parsed_command_line = parse_json_source_file_config_file_content(
        &tsconfig_source_file,
        &vfstest::from_map(HashMap::<&str, &str>::new(), CaseSensitivity::CaseSensitive),
        RootedDirectoryPath::from("/dev"),
        None,
        None,
        &[],
        None,
    );

    let with_typings = parsed_command_line.with_file_names(vec![
        to_rooted_file_path("/dev/index.ts", parsed_command_line.base_directory()),
        to_rooted_file_path(
            "/cache/@types/pkg/index.d.ts",
            parsed_command_line.base_directory(),
        ),
    ]);
    assert_eq!(with_typings.config_name().as_string(), config_file_name);
    assert_eq!(
        with_typings.file_names(),
        &[
            RootedFilePath::from("/dev/index.ts"),
            RootedFilePath::from("/cache/@types/pkg/index.d.ts")
        ]
    );
}
