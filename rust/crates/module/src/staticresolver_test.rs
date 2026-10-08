// Ported from tsc/internal/module/staticresolver_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_core::compileroptions::{RESOLUTION_MODE_COMMON_JS, RESOLUTION_MODE_ESM};
use tsc_core::options_generated::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::cache::ResolverOptions;
use crate::resolver::DefaultResolver;
use crate::staticresolver::{
    StaticResolutionEntry, new_static_resolutions, new_static_resolver,
};
use crate::types::{ResolutionHost, ResolvedModule, Resolver};

/// `type resolutionTestInputs struct` — minimal host providing an FS and cwd.
struct ResolutionTestInputs {
    fs: Arc<dyn Vfs>,
    cwd: RootedDirectoryPath,
}

impl ResolutionHost for ResolutionTestInputs {
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.cwd.clone()
    }
}

/// `func TestStaticResolver(t *testing.T)`
#[test]
fn test_static_resolver() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            ("/repo/node_modules/fallback/package.json", "{\"name\":\"fallback\",\"types\":\"index.d.ts\"}"),
            ("/repo/node_modules/fallback/index.d.ts", "export {};"),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let fallback = Arc::new(DefaultResolver::new(ResolverOptions {
        host: Arc::new(ResolutionTestInputs {
            fs,
            cwd: RootedDirectoryPath::from("/repo"),
        }),
        compiler_options: Arc::new(CompilerOptions {
            module: ModuleKind::ESNext,
            module_resolution: ModuleResolutionKind::Bundler,
            ..CompilerOptions::default()
        }),
        typings_location: RootedDirectoryPath::default(),
        project_name: String::new(),
        extra_extensions: Vec::new(),
        package_json_cache: None,
    }));
    let resolutions = new_static_resolutions(
        vec![
            StaticResolutionEntry {
                module_name: "provided".to_string(),
                containing_directory: RootedDirectoryPath::default(),
                resolution_mode: None,
                result: Some(ResolvedModule {
                    resolved_file_name: RootedFilePath::from("/global.d.ts"),
                    ..ResolvedModule::default()
                }),
            },
            StaticResolutionEntry {
                module_name: "provided".to_string(),
                containing_directory: RootedDirectoryPath::from("/repo/src"),
                resolution_mode: None,
                result: Some(ResolvedModule {
                    resolved_file_name: RootedFilePath::from("/directory.d.ts"),
                    ..ResolvedModule::default()
                }),
            },
            StaticResolutionEntry {
                module_name: "provided".to_string(),
                containing_directory: RootedDirectoryPath::default(),
                resolution_mode: Some(RESOLUTION_MODE_ESM),
                result: Some(ResolvedModule {
                    resolved_file_name: RootedFilePath::from("/esm.d.ts"),
                    ..ResolvedModule::default()
                }),
            },
            StaticResolutionEntry {
                module_name: "provided".to_string(),
                containing_directory: RootedDirectoryPath::from("/repo/src"),
                resolution_mode: Some(RESOLUTION_MODE_ESM),
                result: Some(ResolvedModule {
                    resolved_file_name: RootedFilePath::from("/directory-esm.d.ts"),
                    ..ResolvedModule::default()
                }),
            },
            StaticResolutionEntry {
                module_name: "unresolved".to_string(),
                containing_directory: RootedDirectoryPath::default(),
                resolution_mode: None,
                result: None,
            },
        ],
        true,
        RootedDirectoryPath::from("/repo"),
        CaseSensitivity::CaseSensitive,
    )
    .expect("new_static_resolutions failed");
    let resolver: Arc<dyn Resolver> =
        Arc::new(new_static_resolver(fallback, resolutions));

    struct Case {
        name: &'static str,
        containing_file: &'static str,
        mode: tsc_core::compileroptions::ResolutionMode,
        resolved_file_name: &'static str,
    }
    let tests = [
        Case { name: "provided", containing_file: "/repo/src/index.ts", mode: RESOLUTION_MODE_ESM, resolved_file_name: "/directory-esm.d.ts" },
        Case { name: "provided", containing_file: "/repo/src/index.ts", mode: RESOLUTION_MODE_COMMON_JS, resolved_file_name: "/directory.d.ts" },
        Case { name: "provided", containing_file: "/repo/other/index.ts", mode: RESOLUTION_MODE_ESM, resolved_file_name: "/esm.d.ts" },
        Case { name: "provided", containing_file: "/repo/other/index.ts", mode: RESOLUTION_MODE_COMMON_JS, resolved_file_name: "/global.d.ts" },
        Case { name: "fallback", containing_file: "/repo/src/index.ts", mode: RESOLUTION_MODE_ESM, resolved_file_name: "/repo/node_modules/fallback/index.d.ts" },
        Case { name: "unresolved", containing_file: "/repo/src/index.ts", mode: RESOLUTION_MODE_ESM, resolved_file_name: "" },
    ];
    for test in tests {
        let (result, _traces) = resolver.resolve_module_name(
            test.name,
            &RootedFilePath::from(test.containing_file),
            test.mode,
            None,
        );
        if test.resolved_file_name.is_empty() {
            assert!(result.is_none(), "{}: expected unresolved", test.name);
        } else {
            let result = result.unwrap_or_else(|| {
                panic!("{}: expected {}", test.name, test.resolved_file_name)
            });
            assert_eq!(
                result.resolved_file_name.as_string(),
                test.resolved_file_name,
                "{}",
                test.name
            );
        }
    }
}
