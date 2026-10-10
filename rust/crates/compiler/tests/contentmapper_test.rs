// Ported from contentmapper_test.go @ ec47d33c (external test —
// `package compiler_test`).

use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic};
use tsc_ast::{MappedDiagnosticDirective, MappedDiagnosticDirectivePolicy};
use tsc_compiler::file_loader::content_mapper_project_error_diagnostic;
use tsc_compiler::host::new_compiler_host;
use tsc_compiler::program::{
    Program, ProgramConfig, ProgramFactories, ProgramHosts, ProgramOptions, new_program,
};
use tsc_contentmapper::Mapper;
use tsc_contentmapper::host::{
    Error as ContentMapperError, OptionDiagnostic, Project, ProjectError, ProjectErrorKind,
    Request, Result, TransformError, TransformErrorKind,
};
use tsc_core::compileroptions::RESOLUTION_MODE_ESM;
use tsc_core::context::Context;
use tsc_core::options_generated::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use tsc_core::text::{TextPos, TextRange};
use tsc_core::tristate::TS_TRUE;
use tsc_spanmap::{Feature, Kind, Segment, SpanMap};
use tsc_tspath::{
    CaseSensitivity, RootedFilePath, rooted_directory_path_from_normalized,
    rooted_file_path_from_normalized,
};
use tsc_vfs::vfstest;

/// `fakeContentMapperHost` — a `contentmapper.Project` that runs a test
/// transform in-process.
struct FakeContentMapperHost {
    transform: Box<
        dyn Fn(&RootedFilePath, &str) -> std::result::Result<Result, ContentMapperError>
            + Send
            + Sync,
    >,
}

impl Project for FakeContentMapperHost {
    fn refresh(&self) -> std::result::Result<(), ContentMapperError> {
        Ok(())
    }
    fn identities(&self) -> std::result::Result<Vec<String>, ContentMapperError> {
        Ok(Vec::new())
    }
    fn identity(&self, _mapper: &Arc<Mapper>) -> std::result::Result<String, ContentMapperError> {
        Ok("test".to_string())
    }
    fn watched_files(&self) -> std::result::Result<Vec<RootedFilePath>, ContentMapperError> {
        Ok(Vec::new())
    }
    fn diagnostics(&self) -> Vec<OptionDiagnostic> {
        Vec::new()
    }
    fn transform(
        &self,
        _mapper: &Arc<Mapper>,
        request: &Request,
    ) -> std::result::Result<Result, ContentMapperError> {
        (self.transform)(&request.file_name, &request.content)
    }
    fn close(&self) -> std::result::Result<(), ContentMapperError> {
        Ok(())
    }
}

fn test_file_names(file_names: &[&str]) -> Vec<RootedFilePath> {
    file_names
        .iter()
        .map(|f| rooted_file_path_from_normalized(f))
        .collect()
}

/// `newContentMapperProgram`.
fn new_content_mapper_program(
    content_mapper_project: Arc<dyn Project>,
    files: Vec<(&str, &str)>,
    root_files: &[&str],
) -> Rc<Program> {
    new_content_mapper_program_with_options(
        content_mapper_project,
        files,
        root_files,
        CompilerOptions {
            skip_lib_check: TS_TRUE,
            module: ModuleKind::ESNext,
            module_resolution: ModuleResolutionKind::Bundler,
            ..Default::default()
        },
    )
}

/// `newContentMapperProgramWithOptions`.
fn new_content_mapper_program_with_options(
    content_mapper_project: Arc<dyn Project>,
    files: Vec<(&str, &str)>,
    root_files: &[&str],
    options: CompilerOptions,
) -> Rc<Program> {
    let fs = vfstest::from_map(
        std::iter::empty::<(String, String)>(),
        CaseSensitivity::CaseInsensitive,
    );
    let fs = tsc_bundled::wrap_fs(fs);
    for (name, content) in &files {
        fs.write_file(&rooted_file_path_from_normalized(name), content)
            .expect("write test file");
    }

    let mut config = tsc_tsoptions::parsedcommandline::new_parsed_command_line(
        options,
        test_file_names(root_files),
        Vec::new(),
        rooted_directory_path_from_normalized("/"),
        fs.case_sensitivity(),
    );
    // `set_parsed_options` recomputes the content-mapper extension cache
    // (Go mutates `ParsedConfig.ContentMappers` directly, where
    // `ContentMapperExtensions()` is a lazy pure function).
    let mut parsed = config.parsed_config.clone().expect("parsed config");
    parsed.content_mappers = vec![Arc::new(Mapper {
        package: "vue".to_string(),
        extensions: Some(vec![".vue".to_string()]),
        name: "vue-mapper".to_string(),
        version: "1.0.0".to_string(),
        ..Default::default()
    })];
    config.set_parsed_options(parsed);
    new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: Arc::new(config),
            // Load files on the calling thread for deterministic diagnostics
            // ordering.
            single_threaded: TS_TRUE,
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: Arc::new(new_compiler_host(
                fs,
                tsc_bundled::lib_path(),
                None,
                None,
                Some(content_mapper_project),
            )),
            tracing: None,
        },
        factories: ProgramFactories::default(),
    })
}

/// `collectContentMapperDiagnostics`.
fn collect_content_mapper_diagnostics(program: &Program) -> Vec<DiagnosticRef> {
    let ctx = Context::default();
    let mut all = program.get_syntactic_diagnostics(ctx.clone(), None);
    all.extend(program.get_semantic_diagnostics(ctx, None));
    all.extend(program.get_program_diagnostics());
    all
}

/// `TestContentMapperVirtualExtensionSetsImpliedNodeFormat`.
#[test]
fn test_content_mapper_virtual_extension_sets_implied_node_format() {
    let program = new_content_mapper_program_with_options(
        Arc::new(FakeContentMapperHost {
            transform: Box::new(|_file_name, _content| {
                Ok(Result {
                    text: "export {};".to_string(),
                    virtual_extension: ".mts".to_string(),
                    mappings: Some(Arc::new(SpanMap::new(&[]))),
                    ..Default::default()
                })
            }),
        }),
        vec![("/src/Component.vue", "<template />")],
        &["/src/Component.vue"],
        CompilerOptions {
            skip_lib_check: TS_TRUE,
            module: ModuleKind::NodeNext,
            module_resolution: ModuleResolutionKind::NodeNext,
            ..Default::default()
        },
    );

    let file = program
        .get_source_file(&rooted_file_path_from_normalized("/src/Component.vue"))
        .expect("Component.vue");
    let path_key = {
        let nodes = program.arena_of(file);
        nodes[file].as_source_file().path_key().clone()
    };
    assert_eq!(
        program
            .get_source_file_meta_data(&path_key)
            .implied_node_format,
        RESOLUTION_MODE_ESM
    );
}

/// `TestContentMapperDirectivesPreserveIncrementalGlobals`.
#[test]
fn test_content_mapper_directives_preserve_incremental_globals() {
    for policy in [
        MappedDiagnosticDirectivePolicy::Ignore,
        MappedDiagnosticDirectivePolicy::Expect,
    ] {
        let name = if policy == MappedDiagnosticDirectivePolicy::Expect {
            "expect"
        } else {
            "ignore"
        };
        const TEXT: &str = "export function values() { function* generator() { yield 1; } }";
        let program = new_content_mapper_program_with_options(
            Arc::new(FakeContentMapperHost {
                transform: Box::new(move |_file_name, content| {
                    // The virtual source is unchanged; the directive covers the entire file,
                    // including offset zero.
                    Ok(Result {
                        text: content.to_string(),
                        virtual_extension: ".ts".to_string(),
                        mappings: Some(Arc::new(SpanMap::new(&[Segment {
                            original_end: content.len() as TextPos,
                            virtual_end: content.len() as TextPos,
                            kind: Kind::Verbatim,
                            features: Feature::All,
                            ..Default::default()
                        }]))),
                        diagnostic_directives: vec![MappedDiagnosticDirective {
                            virtual_range: TextRange::new(0, content.len() as i32),
                            original_range: TextRange::new(0, content.len() as i32),
                            policy,
                            source: "vue".to_string(),
                            unused_code: 2578,
                            unused_message_text: "Unused mapped expect directive.".to_string(),
                        }],
                        ..Default::default()
                    })
                }),
            }),
            vec![("/src/Component.vue", TEXT)],
            &["/src/Component.vue"],
            CompilerOptions {
                lib: Some(vec!["lib.es5.d.ts".to_string()]),
                skip_lib_check: TS_TRUE,
                module: ModuleKind::ESNext,
                module_resolution: ModuleResolutionKind::Bundler,
                ..Default::default()
            },
        );
        assert_eq!(
            program.get_global_diagnostics(Context::default()).len(),
            0,
            "{name}"
        );
        let file = program
            .get_source_file(&rooted_file_path_from_normalized("/src/Component.vue"))
            .expect("Component.vue");
        let diags = program
            .get_semantic_diagnostics_for_incremental(Context::default(), &[file])
            .get(&file)
            .cloned()
            .unwrap_or_default();
        let mut globals = 0;
        let mut unused = 0;
        for diag in &diags {
            let d = lock_diagnostic(diag);
            if d.file().is_none() {
                assert_eq!(d.code(), tsc_diagnostics::Cannot_find_global_type_0.code());
                assert_eq!(d.message_args()[0], "IterableIterator");
                globals += 1;
            } else {
                assert_eq!(d.file().and_then(|f| f.node), Some(file), "{name}");
                assert_eq!(d.source(), "vue");
                assert_eq!(d.code(), 2578);
                unused += 1;
            }
        }
        assert_eq!(globals, 1, "{name}");
        assert_eq!(
            unused,
            if policy == MappedDiagnosticDirectivePolicy::Expect {
                1
            } else {
                0
            },
            "{name}"
        );
    }
}

/// `TestCompositeProjectContentMapperSupplementalRoots`.
#[test]
fn test_composite_project_content_mapper_supplemental_roots() {
    let make_host = || {
        Arc::new(FakeContentMapperHost {
            transform: Box::new(|_file_name, _content| {
                Ok(Result {
                    text: "export {};".to_string(),
                    virtual_extension: ".ts".to_string(),
                    mappings: Some(Arc::new(SpanMap::new(&[]))),
                    supplemental: vec![tsc_contentmapper::host::MappedResult {
                        text: "export {};".to_string(),
                        virtual_extension: ".mts".to_string(),
                        mappings: Some(Arc::new(SpanMap::new(&[]))),
                        ..Default::default()
                    }],
                    ..Default::default()
                })
            }),
        })
    };
    let options = || CompilerOptions {
        composite: TS_TRUE,
        skip_lib_check: TS_TRUE,
        module: ModuleKind::ESNext,
        module_resolution: ModuleResolutionKind::Bundler,
        ..Default::default()
    };

    // "listed canonical root"
    {
        let program = new_content_mapper_program_with_options(
            make_host(),
            vec![("/src/Component.vue", "<template />")],
            &["/src/Component.vue"],
            options(),
        );
        let program_diagnostics = collect_content_mapper_diagnostics(&program);
        let has_unlisted_file_diagnostic = program_diagnostics.iter().any(|d| {
            lock_diagnostic(d).code()
                == tsc_diagnostics::File_0_is_not_listed_within_the_file_list_of_project_1_Projects_must_list_all_files_or_use_an_include_pattern
                    .code()
        });
        assert!(
            !has_unlisted_file_diagnostic,
            "supplemental output should be covered by its listed canonical root: {:?}",
            program_diagnostics.len()
        );
    }

    // "imported canonical file"
    {
        let program = new_content_mapper_program_with_options(
            make_host(),
            vec![
                ("/src/index.ts", "import \"./Component.vue\";"),
                ("/src/Component.vue", "<template />"),
            ],
            &["/src/index.ts"],
            options(),
        );
        let mut unlisted_file_diagnostic_count = 0;
        for diagnostic in collect_content_mapper_diagnostics(&program) {
            if lock_diagnostic(&diagnostic).code()
                == tsc_diagnostics::File_0_is_not_listed_within_the_file_list_of_project_1_Projects_must_list_all_files_or_use_an_include_pattern
                    .code()
            {
                unlisted_file_diagnostic_count += 1;
            }
        }
        assert_eq!(unlisted_file_diagnostic_count, 2);
    }
}

/// `TestContentMapperInvalidMappings`.
#[test]
fn test_content_mapper_invalid_mappings() {
    const TRANSFORMED: &str = "export const x = 1;\n";
    const ORIGINAL: &str = "<template>x</template>\n";
    let mappings = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 0,
            original_end: 0,
            kind: Kind::Atom,
            ..Default::default()
        },
        Segment {
            virtual_start: 5,
            virtual_end: TRANSFORMED.len() as TextPos,
            original_start: 0,
            original_end: 0,
            kind: Kind::Atom,
            ..Default::default()
        },
    ]);
    let files = vec![
        ("/src/app.ts", "import \"./Component.vue\";"),
        ("/src/Component.vue", ORIGINAL),
    ];
    let mappings = Arc::new(mappings);
    let program = new_content_mapper_program(
        Arc::new(FakeContentMapperHost {
            transform: Box::new(move |_file_name, _content| {
                Ok(Result {
                    text: TRANSFORMED.to_string(),
                    virtual_extension: ".ts".to_string(),
                    mappings: Some(mappings.clone()),
                    ..Default::default()
                })
            }),
        }),
        files,
        &["/src/app.ts"],
    );
    let program_diagnostics = collect_content_mapper_diagnostics(&program);
    let found = program_diagnostics.iter().any(|d| {
        lock_diagnostic(d).code()
            == tsc_diagnostics::The_content_mapper_0_produced_overlapping_or_out_of_order_position_mappings_near_virtual_offset_1
                .code()
    });
    assert!(
        found,
        "expected an invalid mapping diagnostic, got: {:?}",
        program_diagnostics.len()
    );
}

/// `TestContentMapperSourceFileState`.
#[test]
fn test_content_mapper_source_file_state() {
    // "successful synthesized empty file"
    {
        let program = new_content_mapper_program(
            Arc::new(FakeContentMapperHost {
                transform: Box::new(|_file_name, _content| {
                    Ok(Result {
                        text: "export {};".to_string(),
                        virtual_extension: ".ts".to_string(),
                        mappings: Some(Arc::new(SpanMap::new(&[]))),
                        ..Default::default()
                    })
                }),
            }),
            vec![("/src/empty.vue", "")],
            &["/src/empty.vue"],
        );
        let file = program
            .get_source_file(&rooted_file_path_from_normalized("/src/empty.vue"))
            .expect("empty.vue");
        let nodes = program.arena_of(file);
        let sf = nodes[file].as_source_file();
        assert_eq!(sf.original_text(), "");
        assert_eq!(sf.content_mapper(), "vue-mapper@1.0.0");
        assert!(!sf.is_content_mapper_failure_stub());
    }

    // "failed transform"
    {
        let program = new_content_mapper_program(
            Arc::new(FakeContentMapperHost {
                transform: Box::new(|_file_name, _content| {
                    Err(ContentMapperError::Message("failed".to_string()))
                }),
            }),
            vec![("/src/fail.vue", "original")],
            &["/src/fail.vue"],
        );
        let file = program
            .get_source_file(&rooted_file_path_from_normalized("/src/fail.vue"))
            .expect("fail.vue");
        let nodes = program.arena_of(file);
        let sf = nodes[file].as_source_file();
        assert_eq!(sf.original_text(), "original");
        assert_eq!(sf.content_mapper(), "vue-mapper@1.0.0");
        assert!(sf.is_content_mapper_failure_stub());
    }

    // "project error is localized"
    {
        let program = new_content_mapper_program(
            Arc::new(FakeContentMapperHost {
                transform: Box::new(|_file_name, _content| {
                    Err(ContentMapperError::Transform(TransformError::new(
                        TransformErrorKind::Project,
                        Some(ContentMapperError::Project(ProjectError {
                            kind: ProjectErrorKind::MalformedResponse,
                        })),
                    )))
                }),
            }),
            vec![("/src/fail.vue", "original")],
            &["/src/fail.vue"],
        );
        let program_diagnostics = collect_content_mapper_diagnostics(&program);
        let found = program_diagnostics.iter().any(|d| {
            lock_diagnostic(d).message_chain().iter().any(|message| {
                lock_diagnostic(message).code()
                    == tsc_diagnostics::The_content_mapper_returned_a_project_response_that_could_not_be_decoded
                        .code()
            })
        });
        assert!(
            found,
            "expected a localized project response diagnostic, got: {:?}",
            program_diagnostics.len()
        );
    }
}

/// `TestContentMapperProjectErrorDiagnostics`.
#[test]
fn test_content_mapper_project_error_diagnostics() {
    struct Case {
        kind: ProjectErrorKind,
        code: i32,
        message: &'static str,
    }
    let tests = [
        Case {
            kind: ProjectErrorKind::MissingConfigIdentity,
            code: tsc_diagnostics::The_content_mapper_did_not_return_configIdentity_which_is_required_when_the_content_mapper_has_dynamicConfig_Colon_true_in_its_package_json
                .code(),
            message: "The content mapper did not return 'configIdentity', which is required when the content mapper has '\"dynamicConfig\": true' in its package.json.",
        },
        Case {
            kind: ProjectErrorKind::UnexpectedConfigIdentity,
            code: tsc_diagnostics::The_content_mapper_returned_configIdentity_which_is_only_allowed_when_it_declares_dynamicConfig_Colon_true_in_its_package_json
                .code(),
            message: "The content mapper returned 'configIdentity', which is only allowed when it declares '\"dynamicConfig\": true' in its package.json.",
        },
        Case {
            kind: ProjectErrorKind::UnexpectedWatchedFiles,
            code: tsc_diagnostics::The_content_mapper_returned_watchedFiles_which_is_only_allowed_when_it_declares_dynamicConfig_Colon_true_in_its_package_json
                .code(),
            message: "The content mapper returned 'watchedFiles', which is only allowed when it declares '\"dynamicConfig\": true' in its package.json.",
        },
    ];
    for test in &tests {
        let message =
            content_mapper_project_error_diagnostic(&ContentMapperError::Project(ProjectError {
                kind: test.kind,
            }));
        assert_eq!(message.code(), test.code, "{}", test.message);
        assert_eq!(
            tsc_diagnostics::localize(&tsc_locale::DEFAULT, Some(message), message.key(), &[]),
            test.message
        );
    }
}
