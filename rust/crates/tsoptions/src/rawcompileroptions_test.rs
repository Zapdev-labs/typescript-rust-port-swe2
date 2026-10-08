// Ported from tsc/internal/tsoptions/rawcompileroptions_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::rawcompileroptions::RawCompilerOptions;
use tsc_core::tristate::{TS_TRUE, TS_UNKNOWN};
use tsc_tspath::{RootedDirectoryPath, RootedFilePath, to_source_map_location};

/// `TestRawCompilerOptionsFinalizePaths`.
#[test]
fn test_raw_compiler_options_finalize_paths() {
    let raw: RawCompilerOptions = serde_json::from_str(
        r#"{
		"outDir": "dist",
		"rootDirs": ["src", "${configDir}/generated"],
		"tsBuildInfoFile": "cache/build.tsbuildinfo",
		"sourceRoot": "sources\\mapped",
		"paths": {
			"*a": ["first/*"],
			"*": ["fallback/*"]
		},
		"allowNonTsExtensions": true,
		"suppressOutputPathCheck": true,
		"configFilePath": "",
		"NoImplicitAny": true
	}"#,
    )
    .expect("unmarshal");

    let (options, diagnostics) = raw.finalize(&RootedDirectoryPath::from("/project"));
    assert_eq!(diagnostics.len(), 0);
    assert_eq!(options.out_dir, RootedDirectoryPath::from("/project/dist"));
    assert_eq!(
        options.root_dirs.as_deref(),
        Some(
            [
                RootedDirectoryPath::from("/project/src"),
                RootedDirectoryPath::from("/project/generated"),
            ]
            .as_slice()
        )
    );
    assert_eq!(
        options.ts_build_info_file,
        RootedFilePath::from("/project/cache/build.tsbuildinfo")
    );
    assert_eq!(
        options.source_root,
        to_source_map_location("sources/mapped")
    );
    let paths = options.paths.as_ref().expect("paths");
    let keys: Vec<&str> = paths.keys().map(String::as_str).collect();
    assert_eq!(keys, ["*a", "*"]);
    let paths_a = paths.get("*a").expect("*a key");
    assert_eq!(
        paths_a
            .as_deref()
            .map(|s| s.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["first/*"])
    );
    assert_eq!(options.allow_non_ts_extensions, TS_TRUE);
    assert_eq!(options.suppress_output_path_check, TS_TRUE);
    assert_eq!(options.config_file_path, RootedFilePath::from(""));
    assert_eq!(options.no_implicit_any, TS_UNKNOWN);
}
