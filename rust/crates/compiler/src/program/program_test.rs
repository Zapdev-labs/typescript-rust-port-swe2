// Ported from program_test.go @ ec47d33c (internal test — `package compiler`).
//
// Not ported:
//   - `TestProgramSharedData` — relies on Go reflection (`testutil.CheckDataOnly`)
//     to verify shared-data/host-retention rules; Rust's ownership model makes
//     the same guarantees statically.
//   - `TestIncludeReasonDiagnosticsAreProgramLocal` — constructs a bare
//     `&Program{opts: ...}`; the Rust `Program` requires a full construction.
//   - `BenchmarkNewProgram` — Go benchmark harness.
//   - `TestProgramHostsAndFactories` / `TestClonedProgramProjectReferenceResolution`
//     are ported below where the ported APIs allow.
//   - emit_test.go is all benchmarks (`BenchmarkEmit*`) — not ported.

use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::utilities::is_source_phase_import;
use tsc_core::compileroptions::RESOLUTION_MODE_COMMON_JS;
use tsc_core::options_generated::{CompilerOptions, ScriptTarget};
use tsc_core::tristate::{TS_TRUE, bool_to_tristate};
use tsc_tspath::{
    CaseSensitivity, rooted_directory_path_from_normalized, rooted_file_path_from_normalized,
};
use tsc_vfs::vfstest;

use crate::checker_pool::{CheckerPool, new_checker_pool_with_tracing};
use crate::host::{CompilerHost, new_compiler_host};
use crate::program::{
    Program, ProgramConfig, ProgramFactories, ProgramHosts, ProgramOptions, new_program,
    update_program,
};
use crate::project_reference_dts_faking_host::CompilerResolutionHost;

fn test_file_names(file_names: &[&str]) -> Vec<tsc_tspath::RootedFilePath> {
    file_names
        .iter()
        .map(|f| rooted_file_path_from_normalized(f))
        .collect()
}

/// `esnextLibs` from program_test.go @ ec47d33c.
const ESNEXT_LIBS: &[&str] = &[
    "lib.es5.d.ts",
    "lib.es2015.d.ts",
    "lib.es2016.d.ts",
    "lib.es2017.d.ts",
    "lib.es2018.d.ts",
    "lib.es2019.d.ts",
    "lib.es2020.d.ts",
    "lib.es2021.d.ts",
    "lib.es2022.d.ts",
    "lib.es2023.d.ts",
    "lib.es2024.d.ts",
    "lib.es2025.d.ts",
    "lib.es2026.d.ts",
    "lib.esnext.d.ts",
    "lib.dom.d.ts",
    "lib.dom.iterable.d.ts",
    "lib.dom.asynciterable.d.ts",
    "lib.webworker.importscripts.d.ts",
    "lib.scripthost.d.ts",
    "lib.es2015.core.d.ts",
    "lib.es2015.collection.d.ts",
    "lib.es2015.generator.d.ts",
    "lib.es2015.iterable.d.ts",
    "lib.es2015.promise.d.ts",
    "lib.es2015.proxy.d.ts",
    "lib.es2015.reflect.d.ts",
    "lib.es2015.symbol.d.ts",
    "lib.es2015.symbol.wellknown.d.ts",
    "lib.es2016.array.include.d.ts",
    "lib.es2016.intl.d.ts",
    "lib.es2017.arraybuffer.d.ts",
    "lib.es2017.date.d.ts",
    "lib.es2017.object.d.ts",
    "lib.es2017.sharedmemory.d.ts",
    "lib.es2017.string.d.ts",
    "lib.es2017.intl.d.ts",
    "lib.es2017.typedarrays.d.ts",
    "lib.es2018.asyncgenerator.d.ts",
    "lib.es2018.asynciterable.d.ts",
    "lib.es2018.intl.d.ts",
    "lib.es2018.promise.d.ts",
    "lib.es2018.regexp.d.ts",
    "lib.es2019.array.d.ts",
    "lib.es2019.object.d.ts",
    "lib.es2019.string.d.ts",
    "lib.es2019.symbol.d.ts",
    "lib.es2019.intl.d.ts",
    "lib.es2020.bigint.d.ts",
    "lib.es2020.date.d.ts",
    "lib.es2020.promise.d.ts",
    "lib.es2020.sharedmemory.d.ts",
    "lib.es2020.string.d.ts",
    "lib.es2020.symbol.wellknown.d.ts",
    "lib.es2020.intl.d.ts",
    "lib.es2020.number.d.ts",
    "lib.es2021.promise.d.ts",
    "lib.es2021.string.d.ts",
    "lib.es2021.weakref.d.ts",
    "lib.es2021.intl.d.ts",
    "lib.es2022.array.d.ts",
    "lib.es2022.error.d.ts",
    "lib.es2022.intl.d.ts",
    "lib.es2022.object.d.ts",
    "lib.es2022.string.d.ts",
    "lib.es2022.regexp.d.ts",
    "lib.es2023.array.d.ts",
    "lib.es2023.collection.d.ts",
    "lib.es2023.intl.d.ts",
    "lib.es2024.arraybuffer.d.ts",
    "lib.es2024.collection.d.ts",
    "lib.es2024.object.d.ts",
    "lib.es2024.promise.d.ts",
    "lib.es2024.regexp.d.ts",
    "lib.es2024.sharedmemory.d.ts",
    "lib.es2024.string.d.ts",
    "lib.es2025.collection.d.ts",
    "lib.es2025.float16.d.ts",
    "lib.es2025.intl.d.ts",
    "lib.es2025.iterator.d.ts",
    "lib.es2025.promise.d.ts",
    "lib.es2025.regexp.d.ts",
    "lib.es2026.array.d.ts",
    "lib.es2026.collection.d.ts",
    "lib.es2026.error.d.ts",
    "lib.es2026.iterator.d.ts",
    "lib.es2026.json.d.ts",
    "lib.es2026.math.d.ts",
    "lib.es2026.typedarrays.d.ts",
    "lib.esnext.promise.d.ts",
    "lib.esnext.date.d.ts",
    "lib.esnext.decorators.d.ts",
    "lib.esnext.disposable.d.ts",
    "lib.esnext.intl.d.ts",
    "lib.esnext.modulesource.d.ts",
    "lib.esnext.sharedmemory.d.ts",
    "lib.esnext.temporal.d.ts",
    "lib.decorators.d.ts",
    "lib.decorators.legacy.d.ts",
    "lib.esnext.full.d.ts",
];

struct ProgramTestCase {
    test_name: &'static str,
    files: Vec<(&'static str, &'static str)>,
    expected_files: Vec<&'static str>,
}

fn program_test_cases() -> Vec<ProgramTestCase> {
    let mut expected = Vec::new();
    expected.extend_from_slice(ESNEXT_LIBS);
    expected.extend_from_slice(&[
        "c:/dev/src2/a/b/c/1.ts",
        "c:/dev/src2/a/b/2.ts",
        "c:/dev/src2/a/b/3.ts",
        "c:/dev/src2/a/4.ts",
        "c:/dev/src2/a/5.ts",
        "c:/dev/src2/a/b/c/d/e/f/6.ts",
        "c:/dev/src2/a/b/c/d/e/7.ts",
        "c:/dev/src2/a/b/c/d/e/8.ts",
        "c:/dev/src2/a/b/c/d/9.ts",
        "c:/dev/src2/a/10.ts",
        "c:/dev/src/index.ts",
    ]);
    vec![
        ProgramTestCase {
            test_name: "BasicFileOrdering",
            files: vec![
                (
                    "c:/dev/src/index.ts",
                    "/// <reference path='c:/dev/src2/a/5.ts' />\n/// <reference path='c:/dev/src2/a/10.ts' />",
                ),
                ("c:/dev/src2/a/5.ts", "/// <reference path='4.ts' />"),
                ("c:/dev/src2/a/4.ts", "/// <reference path='b/3.ts' />"),
                ("c:/dev/src2/a/b/3.ts", "/// <reference path='2.ts' />"),
                ("c:/dev/src2/a/b/2.ts", "/// <reference path='c/1.ts' />"),
                ("c:/dev/src2/a/b/c/1.ts", "console.log('hello');"),
                ("c:/dev/src2/a/10.ts", "/// <reference path='b/c/d/9.ts' />"),
                (
                    "c:/dev/src2/a/b/c/d/9.ts",
                    "/// <reference path='e/8.ts' />",
                ),
                (
                    "c:/dev/src2/a/b/c/d/e/8.ts",
                    "/// <reference path='7.ts' />",
                ),
                (
                    "c:/dev/src2/a/b/c/d/e/7.ts",
                    "/// <reference path='f/6.ts' />",
                ),
                ("c:/dev/src2/a/b/c/d/e/f/6.ts", "console.log('world!');"),
            ],
            expected_files: expected.clone(),
        },
        ProgramTestCase {
            test_name: "FileOrderingImports",
            files: vec![
                (
                    "c:/dev/src/index.ts",
                    "import * as five from '../src2/a/5.ts';\nimport * as ten from '../src2/a/10.ts';",
                ),
                ("c:/dev/src2/a/5.ts", "import * as four from './4.ts';"),
                ("c:/dev/src2/a/4.ts", "import * as three from './b/3.ts';"),
                ("c:/dev/src2/a/b/3.ts", "import * as two from './2.ts';"),
                ("c:/dev/src2/a/b/2.ts", "import * as one from './c/1.ts';"),
                ("c:/dev/src2/a/b/c/1.ts", "console.log('hello');"),
                (
                    "c:/dev/src2/a/10.ts",
                    "import * as nine from './b/c/d/9.ts';",
                ),
                (
                    "c:/dev/src2/a/b/c/d/9.ts",
                    "import * as eight from './e/8.ts';",
                ),
                (
                    "c:/dev/src2/a/b/c/d/e/8.ts",
                    "import * as seven from './7.ts';",
                ),
                (
                    "c:/dev/src2/a/b/c/d/e/7.ts",
                    "import * as six from './f/6.ts';",
                ),
                ("c:/dev/src2/a/b/c/d/e/f/6.ts", "console.log('world!');"),
            ],
            expected_files: expected.clone(),
        },
        ProgramTestCase {
            test_name: "FileOrderingCycles",
            files: vec![
                (
                    "c:/dev/src/index.ts",
                    "import * as five from '../src2/a/5.ts';\nimport * as ten from '../src2/a/10.ts';",
                ),
                ("c:/dev/src2/a/5.ts", "import * as four from './4.ts';"),
                ("c:/dev/src2/a/4.ts", "import * as three from './b/3.ts';"),
                (
                    "c:/dev/src2/a/b/3.ts",
                    "import * as two from './2.ts';\nimport * as cycle from 'c:/dev/src/index.ts'; ",
                ),
                ("c:/dev/src2/a/b/2.ts", "import * as one from './c/1.ts';"),
                ("c:/dev/src2/a/b/c/1.ts", "console.log('hello');"),
                (
                    "c:/dev/src2/a/10.ts",
                    "import * as nine from './b/c/d/9.ts';",
                ),
                (
                    "c:/dev/src2/a/b/c/d/9.ts",
                    "import * as eight from './e/8.ts';\nimport * as cycle from 'c:/dev/src/index.ts';",
                ),
                (
                    "c:/dev/src2/a/b/c/d/e/8.ts",
                    "import * as seven from './7.ts';",
                ),
                (
                    "c:/dev/src2/a/b/c/d/e/7.ts",
                    "import * as six from './f/6.ts';",
                ),
                ("c:/dev/src2/a/b/c/d/e/f/6.ts", "console.log('world!');"),
            ],
            expected_files: expected,
        },
    ]
}

/// `TestProgram`.
#[test]
fn test_program() {
    let lib_prefix = format!("{}/", tsc_bundled::lib_path().as_string());
    for test_case in program_test_cases() {
        let fs = vfstest::from_map(
            std::iter::empty::<(String, String)>(),
            CaseSensitivity::CaseInsensitive,
        );
        let fs = tsc_bundled::wrap_fs(fs);
        for (name, contents) in &test_case.files {
            fs.write_file(&rooted_file_path_from_normalized(name), contents)
                .expect("write test file");
        }
        let opts = CompilerOptions {
            target: ScriptTarget::ESNext,
            ..Default::default()
        };
        let program = new_program(ProgramOptions {
            config: Rc::new(ProgramConfig {
                config: Arc::new(tsc_tsoptions::parsedcommandline::new_parsed_command_line(
                    opts,
                    test_file_names(&["c:/dev/src/index.ts"]),
                    Vec::new(),
                    rooted_directory_path_from_normalized("c:/dev/src"),
                    fs.case_sensitivity(),
                )),
                ..Default::default()
            }),
            hosts: ProgramHosts {
                host: Arc::new(new_compiler_host(
                    fs.clone(),
                    tsc_bundled::lib_path(),
                    None,
                    None,
                    None,
                )),
                tracing: None,
            },
            factories: ProgramFactories::default(),
        });

        let mut actual_files: Vec<String> = Vec::new();
        for file in program.source_files() {
            let nodes = program.arena_of(file);
            let name = nodes[file]
                .as_source_file()
                .file_name()
                .as_string()
                .to_string();
            actual_files.push(name.strip_prefix(&lib_prefix).unwrap_or(&name).to_string());
        }
        assert_eq!(
            test_case.expected_files, actual_files,
            "{}",
            test_case.test_name
        );
    }
}

/// `TestImportSourceProgram`.
#[test]
fn test_import_source_program() {
    struct Case {
        name: &'static str,
        source: &'static str,
        evaluation: &'static str,
    }
    let cases = [
        Case {
            name: "static",
            source: "import source a from \"./a.js\";",
            evaluation: "import { a as value } from \"./a.js\";",
        },
        Case {
            name: "dynamic",
            source: "import.source(\"./a.js\");",
            evaluation: "import(\"./a.js\");",
        },
    ];
    for test in &cases {
        let content = format!(
            "{}import source b from \"missing\"; import.source(\"other\");",
            test.source
        );
        let files: Vec<(String, String)> = vec![
            (
                "/src/tsconfig.json".to_string(),
                r#"{"compilerOptions":{"module":"esnext","noLib":true},"files":["index.ts"]}"#
                    .to_string(),
            ),
            ("/src/index.ts".to_string(), content.clone()),
            ("/src/a.ts".to_string(), "export const a = 1;".to_string()),
        ];
        let fs = vfstest::from_map(files.clone(), CaseSensitivity::CaseSensitive);
        let host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            fs.clone(),
            rooted_directory_path_from_normalized("/"),
            None,
            None,
            None,
        ));
        let config = Arc::new(
            tsc_tsoptions::tsconfigparsing::get_parsed_command_line_of_config_file(
                rooted_file_path_from_normalized("/src/tsconfig.json"),
                None,
                None,
                &fs,
                None,
            )
            .unwrap_or_else(|d| panic!("config diagnostics: {}", d.len())),
        );
        let mut program = new_program(ProgramOptions {
            config: Rc::new(ProgramConfig {
                config: config.clone(),
                ..Default::default()
            }),
            hosts: ProgramHosts {
                host: host.clone(),
                tracing: None,
            },
            factories: ProgramFactories::default(),
        });
        let index_name = rooted_file_path_from_normalized("/src/index.ts");
        let file = program
            .get_source_file(&index_name)
            .expect("index.ts in program");
        assert!(
            program
                .get_source_file(&rooted_file_path_from_normalized("/src/a.ts"))
                .is_none(),
            "{}",
            test.name
        );
        let index_key = fs.case_sensitivity().path_key(&index_name.as_path());
        let resolutions = program.resolved_modules.get(&index_key);
        assert!(resolutions.is_none_or(|r| r.is_empty()), "{}", test.name);
        assert!(program.get_unresolved_imports().is_empty(), "{}", test.name);
        assert!(
            program.collect_package_names().unresolved.is_empty(),
            "{}",
            test.name
        );

        let mut new_files = files.clone();
        new_files[1].1 = format!("{}{}", test.evaluation, &content[test.source.len()..]);
        let fs2 = vfstest::from_map(new_files.clone(), CaseSensitivity::CaseSensitive);
        let host2: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            fs2,
            rooted_directory_path_from_normalized("/"),
            None,
            None,
            None,
        ));
        let (next_program, new_file, reused) =
            update_program(&program, &index_key, host2, None, None);
        program = next_program;
        assert!(!reused, "{}", test.name);
        // `newFile` is parsed by the *old* host and is not part of the
        // rebuilt program; resolution lookups need the program's own file
        // node (Go's global `*ast.SourceFile` pointer hides this).
        let _ = new_file;
        assert!(
            program
                .get_source_file(&rooted_file_path_from_normalized("/src/a.ts"))
                .is_some(),
            "{}",
            test.name
        );
        let program_file = program
            .get_source_file(&index_name)
            .expect("index.ts in program");
        let program_imports: Vec<tsc_ast::NodeId> = {
            let nodes = program.arena_of(program_file);
            nodes[program_file].as_source_file().imports().to_vec()
        };
        for specifier in program_imports {
            let is_source_phase = {
                let nodes = program.arena_of(program_file);
                nodes[specifier]
                    .parent
                    .is_some_and(|p| is_source_phase_import(&nodes[p], &nodes))
            };
            let resolved =
                program.get_resolved_module_from_module_specifier(program_file, specifier);
            assert_eq!(
                resolved.as_ref().is_some_and(|r| r.is_resolved()),
                !is_source_phase,
                "{}",
                test.name
            );
        }

        let mut old_files = files.clone();
        old_files[1].1 = content.clone();
        let fs3 = vfstest::from_map(old_files, CaseSensitivity::CaseSensitive);
        let host3: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            fs3,
            rooted_directory_path_from_normalized("/"),
            None,
            None,
            None,
        ));
        let (next_program, _f, reused) = update_program(&program, &index_key, host3, None, None);
        program = next_program;
        assert!(!reused, "{}", test.name);
        assert!(
            program
                .get_source_file(&rooted_file_path_from_normalized("/src/a.ts"))
                .is_none(),
            "{}",
            test.name
        );

        let mut eval_files = files.clone();
        eval_files[1].1 = format!("{}{}", test.evaluation, content);
        let fs4 = vfstest::from_map(eval_files, CaseSensitivity::CaseSensitive);
        let host4: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            fs4,
            rooted_directory_path_from_normalized("/"),
            None,
            None,
            None,
        ));
        let program = new_program(ProgramOptions {
            config: Rc::new(ProgramConfig {
                config: config.clone(),
                ..Default::default()
            }),
            hosts: ProgramHosts {
                host: host4,
                tracing: None,
            },
            factories: ProgramFactories::default(),
        });
        let file = program
            .get_source_file(&index_name)
            .expect("index.ts in program");
        let imports: Vec<tsc_ast::NodeId> = {
            let nodes = program.arena_of(file);
            nodes[file].as_source_file().imports().to_vec()
        };
        for specifier in imports {
            let is_source_phase = {
                let nodes = program.arena_of(file);
                nodes[specifier]
                    .parent
                    .is_some_and(|p| is_source_phase_import(&nodes[p], &nodes))
            };
            let resolved = program.get_resolved_module_from_module_specifier(file, specifier);
            assert_eq!(
                resolved.as_ref().is_some_and(|r| r.is_resolved()),
                !is_source_phase,
                "{}",
                test.name
            );
        }
    }
}

/// `TestIncludeProcessorDiagnosticsWithMissingFileCasing`.
#[test]
fn test_include_processor_diagnostics_with_missing_file_casing() {
    // Case-sensitive file names so /src/MyFile.ts and /src/myFile.ts have
    // different canonical paths but the same lower-case path, triggering
    // file casing diagnostics in the include processor.
    let fs = vfstest::from_map(
        std::iter::empty::<(String, String)>(),
        CaseSensitivity::CaseSensitive,
    );
    let fs = tsc_bundled::wrap_fs(fs);

    // Only create the lowercase version; /src/MyFile.ts does not exist.
    fs.write_file(
        &rooted_file_path_from_normalized("/src/myFile.ts"),
        "export const y = 2;",
    )
    .expect("write test file");

    let opts = CompilerOptions {
        skip_default_lib_check: TS_TRUE,
        ..Default::default()
    };

    // List both casings as root files. The first one (/src/MyFile.ts) fails
    // to load because it does not exist on the case-sensitive filesystem.
    let program = new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: Arc::new(tsc_tsoptions::parsedcommandline::new_parsed_command_line(
                opts,
                test_file_names(&["/src/MyFile.ts", "/src/myFile.ts"]),
                Vec::new(),
                rooted_directory_path_from_normalized("/"),
                fs.case_sensitivity(),
            )),
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: Arc::new(new_compiler_host(
                fs.clone(),
                tsc_bundled::lib_path(),
                None,
                None,
                None,
            )),
            tracing: None,
        },
        factories: ProgramFactories::default(),
    });

    // GetProgramDiagnostics triggers getDiagnostics which processes all
    // include processor diagnostics including the casing diagnostic whose
    // file path points to the missing /src/MyFile.ts. Before the fix this
    // panicked with a nil pointer dereference.
    program.get_program_diagnostics();
}

/// `TestProgramHostsAndFactories`.
#[test]
fn test_program_hosts_and_factories() {
    let files: Vec<(String, String)> = vec![
        (
            "/src/tsconfig.json".to_string(),
            r#"{"compilerOptions":{"noLib":true,"module":"nodenext"},"files":["index.ts"]}"#
                .to_string(),
        ),
        (
            "/src/index.ts".to_string(),
            "/// <reference types=\"dep\" />\nimport { value } from \"./dep.js\"; export const result = value;"
                .to_string(),
        ),
        ("/src/dep.ts".to_string(), "export const value = 1;".to_string()),
        (
            "/src/node_modules/@types/dep/index.d.ts".to_string(),
            "export {};".to_string(),
        ),
    ];
    let fs = vfstest::from_map(files.clone(), CaseSensitivity::CaseSensitive);
    let host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
        fs.clone(),
        rooted_directory_path_from_normalized("/"),
        None,
        None,
        None,
    ));
    let config = Arc::new(
        tsc_tsoptions::tsconfigparsing::get_parsed_command_line_of_config_file(
            rooted_file_path_from_normalized("/src/tsconfig.json"),
            None,
            None,
            &fs,
            None,
        )
        .unwrap_or_else(|d| panic!("config diagnostics: {}", d.len())),
    );
    let pools = Rc::new(std::cell::Cell::new(0));
    let resolvers = Rc::new(std::cell::Cell::new(0));
    let tr: Arc<tsc_tracing::Tracing> = Arc::new(tsc_tracing::Tracing::default());

    let pools_c = pools.clone();
    let tr_c = tr.clone();
    let resolvers_c = resolvers.clone();
    let files_for_resolver = files.clone();
    let p = new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: config.clone(),
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: host.clone(),
            tracing: Some(tr.clone()),
        },
        factories: ProgramFactories {
            create_checker_pool: Some(Arc::new(move |p: &Rc<Program>| {
                pools_c.set(pools_c.get() + 1);
                assert!(p.tracing().is_some_and(|t| Arc::ptr_eq(&t, &tr_c)));
                Rc::new(new_checker_pool_with_tracing(p, p.tracing())) as Rc<dyn CheckerPool>
            })),
            create_module_resolver: Some(Arc::new(
                move |mut options: tsc_module::ResolverOptions| {
                    resolvers_c.set(resolvers_c.get() + 1);
                    let mut resolver_files = files_for_resolver.clone();
                    resolver_files.push((
                        "/factory-only/package.json".to_string(),
                        r#"{"name":"factory-host"}"#.to_string(),
                    ));
                    options.host = Arc::new(CompilerResolutionHost {
                        host: Arc::new(new_compiler_host(
                            vfstest::from_map(resolver_files, CaseSensitivity::CaseSensitive),
                            rooted_directory_path_from_normalized("/"),
                            None,
                            None,
                            None,
                        )),
                        base_directory: rooted_directory_path_from_normalized("/"),
                    });
                    Arc::new(tsc_module::DefaultResolver::new(options))
                        as Arc<dyn tsc_module::Resolver>
                },
            )),
        },
    });
    assert_eq!(pools.get(), 1);
    assert_eq!(resolvers.get(), 1);
    assert!(p.tracing().is_some_and(|t| Arc::ptr_eq(&t, &tr)));
    // lazy lookups must not retain the factory's host
    assert!(
        p.get_package_json_info(&rooted_file_path_from_normalized(
            "/factory-only/package.json"
        ))
        .is_none()
    );
    let old_file = p
        .get_source_file(&rooted_file_path_from_normalized("/src/index.ts"))
        .expect("index.ts");
    let old_imports: Vec<tsc_ast::NodeId> = {
        let nodes = p.arena_of(old_file);
        nodes[old_file].as_source_file().imports().to_vec()
    };
    let resolved = p
        .get_resolved_module_from_module_specifier(old_file, old_imports[0])
        .expect("resolved dep.js");
    assert!(resolved.is_resolved());
    let type_ref = {
        let nodes = p.arena_of(old_file);
        nodes[old_file].as_source_file().type_reference_directives[0].clone()
    };
    let resolved_type_ref = p
        .get_resolved_type_reference_directive_from_type_reference_directive(&type_ref, old_file)
        .expect("resolved dep types");
    assert!(resolved_type_ref.is_resolved());

    let mut new_files = files.clone();
    new_files[1].1 = format!("\n{}", files[1].1);
    new_files.push((
        "/probe/package.json".to_string(),
        r#"{"name":"new-host"}"#.to_string(),
    ));
    let new_host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
        vfstest::from_map(new_files.clone(), CaseSensitivity::CaseSensitive),
        rooted_directory_path_from_normalized("/"),
        None,
        None,
        None,
    ));
    let index_key = {
        let f = rooted_file_path_from_normalized("/src/index.ts");
        fs.case_sensitivity().path_key(&f.as_path())
    };
    let pools_c2 = pools.clone();
    let new_host_c = new_host.clone();
    let expected_text = new_files[1].1.clone();
    let (cloned, changed, reused) = crate::program::reuse_program(
        &p,
        &index_key,
        new_host.clone(),
        Some(Arc::new(move |p: &Rc<Program>| {
            pools_c2.set(pools_c2.get() + 1);
            assert!(std::ptr::eq(
                Arc::as_ptr(&p.hosts.host),
                Arc::as_ptr(&new_host_c)
            ));
            assert!(p.tracing().is_none());
            let f = p
                .get_source_file(&rooted_file_path_from_normalized("/src/index.ts"))
                .expect("index.ts");
            let nodes = p.arena_of(f);
            assert_eq!(nodes[f].as_source_file().text, expected_text);
            drop(nodes);
            Rc::new(new_checker_pool_with_tracing(p, p.tracing())) as Rc<dyn CheckerPool>
        })),
    );
    assert!(reused);
    let cloned = cloned.expect("cloned program");
    let changed = changed.expect("changed file");
    assert!(cloned.tracing().is_none());
    assert!(p.tracing().is_some_and(|t| Arc::ptr_eq(&t, &tr)));
    let changed_id = changed.file;
    assert_eq!(
        Some(changed_id),
        cloned.get_source_file(&rooted_file_path_from_normalized("/src/index.ts"))
    );
    // Go compares shared cache pointers; the port stores `Option<ResolvedModule>`
    // values, so compare the resolved identity fields instead.
    let resolved2 = cloned
        .get_resolved_module_from_module_specifier(changed_id, {
            let nodes = cloned.arena_of(changed_id);
            nodes[changed_id].as_source_file().imports()[0]
        })
        .expect("resolved dep.js");
    assert_eq!(resolved2.resolved_path, resolved.resolved_path);
    assert_eq!(resolved2.resolved_file_name, resolved.resolved_file_name);
    let type_ref2 = {
        let nodes = cloned.arena_of(changed_id);
        nodes[changed_id].as_source_file().type_reference_directives[0].clone()
    };
    let resolved_type_ref2 = cloned
        .get_resolved_type_reference_directive_from_type_reference_directive(&type_ref2, changed_id)
        .expect("resolved dep types");
    assert_eq!(
        resolved_type_ref2.resolved_path,
        resolved_type_ref.resolved_path
    );
    assert!(!Rc::ptr_eq(&cloned.resolution_data, &p.resolution_data));
    assert!(!Rc::ptr_eq(
        &cloned.get_checker_pool(),
        &p.get_checker_pool()
    ));
    assert!(
        cloned
            .get_package_json_info(&rooted_file_path_from_normalized("/probe/package.json"))
            .is_some()
    );
    // new lazy lookups must not populate the old generation's cache
    assert!(
        p.get_package_json_info(&rooted_file_path_from_normalized("/probe/package.json"))
            .is_none()
    );
    assert_eq!(pools.get(), 2);
    assert_eq!(resolvers.get(), 1);

    let (defaults, _f, reused) =
        crate::program::reuse_program(&cloned, &index_key, new_host.clone(), None);
    assert!(reused);
    let defaults = defaults.expect("defaults program");
    assert!(defaults.compiler_checker_pool.borrow().is_some());
    assert!(defaults.tracing().is_none());
    assert_eq!(pools.get(), 2);

    let traced = new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: config.clone(),
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: new_host.clone(),
            tracing: Some(tr.clone()),
        },
        factories: ProgramFactories::default(),
    });
    assert!(traced.tracing().is_some_and(|t| Arc::ptr_eq(&t, &tr)));

    // Rebuild: a new import forces a full (non-reuse) program.
    let mut rebuild_files = new_files.clone();
    rebuild_files[1].1 = "import \"./other.js\";".to_string();
    rebuild_files.push(("/src/other.ts".to_string(), "export {};".to_string()));
    let rebuild_host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
        vfstest::from_map(rebuild_files, CaseSensitivity::CaseSensitive),
        rooted_directory_path_from_normalized("/"),
        None,
        None,
        None,
    ));
    let (rebuilt, _f, reused) = update_program(&p, &index_key, rebuild_host.clone(), None, None);
    assert!(!reused);
    assert!(rebuilt.compiler_checker_pool.borrow().is_some());
    assert!(std::ptr::eq(
        Arc::as_ptr(&rebuilt.hosts.host),
        Arc::as_ptr(&rebuild_host)
    ));
    assert!(rebuilt.tracing().is_none());
    assert!(
        rebuilt
            .get_source_file(&rooted_file_path_from_normalized("/src/other.ts"))
            .is_some()
    );
    assert_eq!(pools.get(), 2);
    assert_eq!(resolvers.get(), 1);
}

/// `TestClonedProgramProjectReferenceResolution`.
#[test]
fn test_cloned_program_project_reference_resolution() {
    for preserve_symlinks in [false, true] {
        let files: Vec<(String, tsc_vfs::vfstest::TestFile)> = vec![
            (
                "/src/tsconfig.json".to_string(),
                r#"{"compilerOptions":{"noLib":true,"module":"nodenext"},"files":["index.ts"],"references":[{"path":"../reference"}]}"#.into(),
            ),
            (
                "/src/index.ts".to_string(),
                "import { value } from \"reference\"; export const result = value;".into(),
            ),
            (
                "/src/node_modules/reference".to_string(),
                tsc_vfs::vfstest::symlink("/reference").into(),
            ),
            (
                "/reference/tsconfig.json".to_string(),
                r#"{"compilerOptions":{"composite":true,"outDir":"dist"},"files":["index.ts"]}"#.into(),
            ),
            (
                "/reference/package.json".to_string(),
                r#"{"name":"reference","version":"1.0.0","types":"dist/index.d.ts"}"#.into(),
            ),
            (
                "/reference/index.ts".to_string(),
                "export const value = 1;".into(),
            ),
        ];
        let fs = vfstest::from_map(files.clone(), CaseSensitivity::CaseSensitive);
        let host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            fs.clone(),
            rooted_directory_path_from_normalized("/"),
            None,
            None,
            None,
        ));
        let opts = CompilerOptions {
            preserve_symlinks: bool_to_tristate(preserve_symlinks),
            ..Default::default()
        };
        let config = tsc_tsoptions::tsconfigparsing::get_parsed_command_line_of_config_file(
            rooted_file_path_from_normalized("/src/tsconfig.json"),
            Some(&opts),
            None,
            &fs,
            None,
        )
        .unwrap_or_else(|d| panic!("config diagnostics: {}", d.len()));
        let p = new_program(ProgramOptions {
            config: Rc::new(ProgramConfig {
                config: Arc::new(config),
                use_source_of_project_reference: true,
                ..Default::default()
            }),
            hosts: ProgramHosts {
                host: host.clone(),
                tracing: None,
            },
            factories: ProgramFactories::default(),
        });
        assert!(
            p.get_source_file(&rooted_file_path_from_normalized("/reference/index.ts"))
                .is_some(),
            "preserveSymlinks={}",
            preserve_symlinks
        );
        assert!(
            !host.fs().file_exists(&rooted_file_path_from_normalized(
                "/reference/dist/index.d.ts"
            )),
            "preserveSymlinks={}",
            preserve_symlinks
        );
        let mut new_files = files.clone();
        new_files[1].1 = "\nimport { value } from \"reference\"; export const result = value;"
            .to_string()
            .into();
        new_files.push((
            "/probe/package.json".to_string(),
            r#"{"name":"new-host"}"#.into(),
        ));
        let new_host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            vfstest::from_map(new_files, CaseSensitivity::CaseSensitive),
            rooted_directory_path_from_normalized("/"),
            None,
            None,
            None,
        ));
        let index_key = {
            let f = rooted_file_path_from_normalized("/src/index.ts");
            fs.case_sensitivity().path_key(&f.as_path())
        };
        let (cloned, _f, reused) =
            crate::program::reuse_program(&p, &index_key, new_host.clone(), None);
        assert!(reused, "preserveSymlinks={}", preserve_symlinks);
        let cloned = cloned.expect("cloned program");
        assert!(
            Arc::ptr_eq(
                cloned
                    .project_reference_file_mapper
                    .as_ref()
                    .expect("mapper"),
                p.project_reference_file_mapper.as_ref().expect("mapper")
            ),
            "preserveSymlinks={}",
            preserve_symlinks
        );
        assert!(
            cloned
                .get_source_file(&rooted_file_path_from_normalized("/reference/index.ts"))
                .is_some(),
            "preserveSymlinks={}",
            preserve_symlinks
        );
        assert!(
            cloned
                .get_package_json_info(&rooted_file_path_from_normalized("/probe/package.json"))
                .is_some(),
            "preserveSymlinks={}",
            preserve_symlinks
        );
        // Resolve again to exercise the new .d.ts-faking host.
        let (resolved, _diags) = cloned.new_resolver().resolve_module_name(
            "reference",
            &rooted_file_path_from_normalized("/src/nested/probe.ts"),
            RESOLUTION_MODE_COMMON_JS,
            None,
        );
        let resolved = resolved.expect("resolved reference");
        assert!(
            resolved.is_resolved(),
            "preserveSymlinks={}",
            preserve_symlinks
        );
        assert!(
            resolved
                .resolved_file_name
                .as_string()
                .ends_with("/dist/index.d.ts"),
            "preserveSymlinks={} resolved={}",
            preserve_symlinks,
            resolved.resolved_file_name.as_string()
        );
    }
}
