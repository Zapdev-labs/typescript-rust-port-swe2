// Ported from tsc/internal/tsoptions/contentmappers_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use crate::contentmappers::resolve_content_mapper_manifest;
use crate::parsedcommandline::new_parsed_command_line;
use tsc_contentmapper::Mapper;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, to_rooted_file_path};
use tsc_vfs::vfstest;

/// `TestGetContentMapperForFileNameUsesLongestExtension`.
#[test]
fn test_get_content_mapper_for_file_name_uses_longest_extension() {
    let z_mapper = Arc::new(Mapper {
        package: "z".into(),
        extensions: Some(vec![".z".into()]),
        ..Default::default()
    });
    let yz_mapper = Arc::new(Mapper {
        package: "yz".into(),
        extensions: Some(vec![".y.z".into()]),
        ..Default::default()
    });
    let mut command_line = new_parsed_command_line(
        CompilerOptions::default(),
        vec![],
        vec![],
        RootedDirectoryPath::from("/"),
        CaseSensitivity::CaseSensitive,
    );
    let mut parsed = command_line.parsed_config.clone().unwrap_or_default();
    parsed.content_mappers = vec![z_mapper.clone(), yz_mapper.clone()];
    command_line.set_parsed_options(parsed);

    assert!(Arc::ptr_eq(
        command_line
            .get_content_mapper_for_file_name(&RootedFilePath::from("/src/Component.y.z"))
            .unwrap(),
        &yz_mapper
    ));
    assert!(Arc::ptr_eq(
        command_line
            .get_content_mapper_for_file_name(&RootedFilePath::from("/src/Component.z"))
            .unwrap(),
        &z_mapper
    ));
}

/// `TestGetContentMapperForFileNameUsesHostCaseSensitivity`.
#[test]
fn test_get_content_mapper_for_file_name_uses_host_case_sensitivity() {
    let mapper = Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        ..Default::default()
    });
    let make = |case_sensitivity| {
        let mut command_line = new_parsed_command_line(
            CompilerOptions::default(),
            vec![],
            vec![],
            RootedDirectoryPath::from("/"),
            case_sensitivity,
        );
        let mut parsed = command_line.parsed_config.clone().unwrap_or_default();
        parsed.content_mappers = vec![mapper.clone()];
        command_line.set_parsed_options(parsed);
        command_line
    };
    let insensitive = make(CaseSensitivity::CaseInsensitive);
    let sensitive = make(CaseSensitivity::CaseSensitive);

    assert!(
        insensitive
            .get_content_mapper_for_file_name(&RootedFilePath::from("/src/Component.VUE"))
            .is_some()
    );
    assert!(
        sensitive
            .get_content_mapper_for_file_name(&RootedFilePath::from("/src/Component.VUE"))
            .is_none()
    );
}

/// `TestGetOutputFileNamesExcludesMapperOwnedOutputs`.
#[test]
fn test_get_output_file_names_excludes_mapper_owned_outputs() {
    let mapper = Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        ..Default::default()
    });
    let current_directory = RootedDirectoryPath::from("/");
    let mut command_line = new_parsed_command_line(
        CompilerOptions {
            out_dir: RootedDirectoryPath::from("/dist"),
            declaration: TS_TRUE,
            declaration_map: TS_TRUE,
            source_map: TS_TRUE,
            ..Default::default()
        },
        vec![to_rooted_file_path(
            "/src/Component.vue",
            &current_directory,
        )],
        vec![],
        current_directory,
        CaseSensitivity::CaseSensitive,
    );
    let mut parsed = command_line.parsed_config.clone().unwrap_or_default();
    parsed.content_mappers = vec![mapper];
    command_line.set_parsed_options(parsed);

    assert_eq!(
        command_line.get_output_file_names(),
        vec![RootedFilePath::from("/dist/Component.d.vue.ts")]
    );
}

/// `TestResolveContentMapperManifest`.
#[test]
fn test_resolve_content_mapper_manifest() {
    let fs = vfstest::from_map(
        [
            (
                "/home/project/node_modules/vue-ts-mapper/package.json",
                r#"{
			"name": "vue-ts-mapper",
			"version": "1.2.3",
			"typescript": { "contentMapper": { "exec": ["node", "./dist/mapper.js"], "compilerOptions": ["target", "jsx"] } }
		}"#,
            ),
            (
                "/home/node_modules/@scope/noversion/package.json",
                r#"{
			"name": "@scope/noversion",
			"typescript": { "contentMapper": { "exec": ["run"] } }
		}"#,
            ),
            (
                "/home/project/node_modules/no-name/package.json",
                r#"{
			"version": "1.0.0"
		}"#,
            ),
            (
                "/home/project/node_modules/no-manifest/package.json",
                r#"{
			"name": "no-manifest"
		}"#,
            ),
            (
                "/home/project/node_modules/no-exec/package.json",
                r#"{
			"name": "no-exec",
			"typescript": { "contentMapper": {} }
		}"#,
            ),
            (
                "/home/project/node_modules/bad-exec/package.json",
                r#"{
			"name": "bad-exec",
			"typescript": { "contentMapper": { "exec": "node ./mapper.js" } }
		}"#,
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );

    // Name, version, and the verbatim exec argv are preserved.
    let tsconfig = RootedFilePath::from("/home/project/tsconfig.json");
    let (manifest, package_directory, diagnostic) =
        resolve_content_mapper_manifest(&fs, &tsconfig, "vue-ts-mapper");
    assert!(diagnostic.is_none());
    let manifest = manifest.expect("manifest");
    assert_eq!(manifest.name, "vue-ts-mapper");
    assert_eq!(manifest.version, "1.2.3");
    assert_eq!(
        package_directory,
        RootedDirectoryPath::from("/home/project/node_modules/vue-ts-mapper")
    );
    assert_eq!(
        manifest
            .exec
            .as_deref()
            .map(|v| v.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["node", "./dist/mapper.js"])
    );
    assert_eq!(
        manifest
            .compiler_options
            .as_deref()
            .map(|v| v.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["target", "jsx"])
    );

    // Resolution walks up node_modules; a package with no version resolves to
    // a name and empty version.
    let src_tsconfig = RootedFilePath::from("/home/project/src/tsconfig.json");
    let (manifest, _, diagnostic) =
        resolve_content_mapper_manifest(&fs, &src_tsconfig, "@scope/noversion");
    assert!(diagnostic.is_none());
    let manifest = manifest.expect("manifest");
    assert_eq!(manifest.name, "@scope/noversion");
    assert_eq!(manifest.version, "");

    // A package that is not installed reports a resolution diagnostic.
    let (_, _, diagnostic) = resolve_content_mapper_manifest(&fs, &tsconfig, "missing-mapper");
    let diagnostic = diagnostic.expect("diagnostic");
    assert_eq!(
        diagnostic.lock().unwrap_or_else(|e| e.into_inner()).code(),
        tsc_diagnostics::The_content_mapper_package_0_could_not_be_resolved.code()
    );

    // A package whose package.json has no name reports a diagnostic.
    let (_, package_directory, diagnostic) =
        resolve_content_mapper_manifest(&fs, &tsconfig, "no-name");
    let diagnostic = diagnostic.expect("diagnostic");
    assert_eq!(
        package_directory,
        RootedDirectoryPath::from("/home/project/node_modules/no-name")
    );
    assert_eq!(
        diagnostic.lock().unwrap_or_else(|e| e.into_inner()).code(),
        tsc_diagnostics::The_package_json_of_the_content_mapper_package_0_does_not_specify_a_name
            .code()
    );

    // A package that does not declare a "typescript.contentMapper" object
    // reports a diagnostic.
    let (_, _, diagnostic) = resolve_content_mapper_manifest(&fs, &tsconfig, "no-manifest");
    let diagnostic = diagnostic.expect("diagnostic");
    assert_eq!(
        diagnostic.lock().unwrap_or_else(|e| e.into_inner()).code(),
        tsc_diagnostics::The_package_json_of_the_content_mapper_package_0_does_not_declare_a_typescript_contentMapper_object
            .code()
    );

    // A "typescript.contentMapper" with no "exec", or an "exec" of the wrong
    // type, reports a diagnostic.
    for pkg in ["no-exec", "bad-exec"] {
        let (_, _, diagnostic) = resolve_content_mapper_manifest(&fs, &tsconfig, pkg);
        let diagnostic = diagnostic.unwrap_or_else(|| panic!("expected a diagnostic for {pkg}"));
        assert_eq!(
            diagnostic.lock().unwrap_or_else(|e| e.into_inner()).code(),
            tsc_diagnostics::The_typescript_contentMapper_exec_of_the_content_mapper_package_0_must_be_a_non_empty_array_of_strings
                .code()
        );
    }
}
