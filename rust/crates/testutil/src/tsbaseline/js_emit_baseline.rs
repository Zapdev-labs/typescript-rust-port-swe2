// Ported from tsc/internal/testutil/tsbaseline/js_emit_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt::Write as _;
use std::sync::Arc;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_diagnosticwriter as diagnosticwriter;
use tsc_tsoptions::parsedcommandline::{self, ParsedCommandLine};
use tsc_tsoptions::parsedoptions::ParsedOptions;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath};

use super::error_baseline::get_error_baseline;
use super::util::remove_test_path_prefixes;
use crate::baseline;
use crate::harnessutil::{
    self as harnessutil, CompilationResult, HarnessOptions, TestConfiguration, TestFile,
};

/// `DoJSEmitBaseline`.
#[allow(clippy::too_many_arguments)]
pub fn do_js_emit_baseline(
    baseline_path: &str,
    header: &str,
    options: &CompilerOptions,
    result: &CompilationResult,
    ts_config_files: &[TestFile],
    to_be_compiled: &[TestFile],
    other_files: &[TestFile],
    harness_settings: &HarnessOptions,
    opts: baseline::Options,
) {
    if !options.no_emit.is_true()
        && !options.emit_declaration_only.is_true()
        && result.js.size() == 0
        && result.diagnostics.is_empty()
    {
        panic!("Expected at least one js file to be emitted or at least one error to be created.");
    }

    // check js output
    let mut ts_code = String::new();
    let ts_sources: Vec<&TestFile> = other_files.iter().chain(to_be_compiled.iter()).collect();
    let _ = write!(ts_code, "//// [{header}] ////\r\n\r\n");

    for (i, file) in ts_sources.iter().enumerate() {
        let _ = write!(
            ts_code,
            "//// [{}]\r\n{}",
            tspath::get_base_file_name(&file.unit_name),
            file.content
        );
        if i < ts_sources.len() - 1 {
            ts_code.push_str("\r\n");
        }
    }

    let mut js_code = String::new();
    for file in result.js.values() {
        if !js_code.is_empty() && !js_code.ends_with('\n') {
            js_code.push_str("\r\n");
        }
        if result.diagnostics.is_empty() && file.unit_name.ends_with(tspath::EXTENSION_JSON) {
            let file_name =
                tspath::to_rooted_file_path(&file.unit_name, result.current_directory());
            let (file_parse_result, nodes) = tsc_parser::parse_source_file(
                SourceFileParseOptions {
                    file_name: file_name.clone(),
                    path_key: tspath::CaseSensitivity::CaseSensitive
                        .path_key(&tspath::RootedPath::from(file_name)),
                    ..Default::default()
                },
                &file.content,
                ScriptKind::Json,
            );
            let diagnostics: Vec<DiagnosticRef> = nodes[file_parse_result]
                .as_source_file()
                .diagnostics()
                .to_vec();
            if !diagnostics.is_empty() {
                js_code.push_str(&get_error_baseline(
                    std::slice::from_ref(&**file),
                    &diagnosticwriter::wrap_ast_diagnostics(&diagnostics, &nodes),
                    diagnosticwriter::compare_ast_diagnostics,
                    false, // pretty
                ));
                continue;
            }
        }
        js_code.push_str(&file_output(file, harness_settings));
    }

    if result.dts.size() > 0 {
        js_code.push_str("\r\n\r\n");
        for decl_file in result.dts.values() {
            js_code.push_str(&file_output(decl_file, harness_settings));
        }
    }

    let decl_file_context = prepare_declaration_compilation_context(
        to_be_compiled,
        other_files,
        result,
        harness_settings,
        options,
        "", /*currentDirectory*/
    );
    let decl_file_compilation_result =
        decl_file_context.map(|ctx| compile_declaration_files(&ctx, &result.symlinks));

    if let Some(decl_result) = &decl_file_compilation_result
        && !decl_result.decl_result.diagnostics.is_empty()
    {
        js_code.push_str("\r\n\r\n//// [DtsFileErrors]\r\n");
        js_code.push_str("\r\n\r\n");
        let decl_files: Vec<TestFile> = ts_config_files
            .iter()
            .chain(decl_result.decl_input_files.iter())
            .chain(decl_result.decl_other_files.iter())
            .cloned()
            .collect();
        js_code.push_str(&get_error_baseline(
            &decl_files,
            &decl_result
                .decl_result
                .diagnostics
                .iter()
                .map(|d| super::error_baseline::SnapshotDiagnostic {
                    diagnostic: d.clone(),
                })
                .collect::<Vec<_>>(),
            super::error_baseline::compare_snapshot_diagnostics,
            false, // pretty
        ));
    }

    if !options.no_check.is_true() && !options.no_emit.is_true() {
        let mut test_config: TestConfiguration = TestConfiguration::default();
        test_config.insert("noCheck".to_string(), "true".to_string());
        let without_checking =
            result.repeat.as_ref().expect("CompilationResult::repeat")(test_config);
        let compare_result_file_sets =
            |a: &OrderedMap<RootedFilePath, Arc<TestFile>>,
             b: &OrderedMap<RootedFilePath, Arc<TestFile>>,
             js_code: &mut String| {
                for (key, doc) in a.entries() {
                    let original = b.get(key);
                    if let Some(original) = original {
                        if original.content != doc.content {
                            js_code.push_str("\r\n\r\n!!!! File ");
                            js_code.push_str(&remove_test_path_prefixes(&doc.unit_name, false));
                            js_code.push_str(" differs from original emit in noCheck emit\r\n");
                            let file_name = if harness_settings.full_emit_paths {
                                remove_test_path_prefixes(&doc.unit_name, false)
                            } else {
                                tspath::get_base_file_name(&doc.unit_name).into_owned()
                            };
                            let _ = write!(js_code, "//// [{file_name}]\r\n");
                            let expected = &original.content;
                            let actual = &doc.content;
                            js_code.push_str(&String::from_utf8_lossy(&baseline::diff_text(
                                "Expected\tThe full check baseline",
                                "Actual\twith noCheck set",
                                expected.as_bytes(),
                                actual.as_bytes(),
                            )));
                        }
                    } else {
                        js_code.push_str("\r\n\r\n!!!! File ");
                        js_code.push_str(&remove_test_path_prefixes(&doc.unit_name, false));
                        js_code.push_str(
                            " missing from original emit, but present in noCheck emit\r\n",
                        );
                        js_code.push_str(&file_output(doc, harness_settings));
                    }
                }
            };
        compare_result_file_sets(&without_checking.dts, &result.dts, &mut js_code);
        compare_result_file_sets(&without_checking.js, &result.js, &mut js_code);
    }

    let mut baseline_path = baseline_path.to_string();
    if tspath::file_extension_is_one_of(
        &baseline_path,
        &[tspath::EXTENSION_TS, tspath::EXTENSION_TSX],
    ) {
        baseline_path = tspath::change_extension(&baseline_path, tspath::EXTENSION_JS).into_owned();
    }

    let actual = if !js_code.is_empty() {
        format!("{}\r\n\r\n{}", ts_code, js_code)
    } else {
        baseline::NO_CONTENT.to_string()
    };

    baseline::run(&baseline_path, &actual, &opts).unwrap_or_else(|e| panic!("{e}"));
}

/// `fileOutput`.
pub(crate) fn file_output(file: &TestFile, settings: &HarnessOptions) -> String {
    let file_name = if settings.full_emit_paths {
        remove_test_path_prefixes(&file.unit_name, false)
    } else {
        tspath::get_base_file_name(&file.unit_name).into_owned()
    };
    format!("//// [{file_name}]\r\n{}", file.content)
}

/// `declarationCompilationContext`.
struct DeclarationCompilationContext {
    decl_input_files: Vec<TestFile>,
    decl_other_files: Vec<TestFile>,
    harness_settings: HarnessOptions,
    options: CompilerOptions,
    current_directory: RootedDirectoryPath,
    /// `config *tsoptions.ParsedCommandLine` — `Option<Arc<..>>` since Go's
    /// field is nilable.
    config: Option<Arc<ParsedCommandLine>>,
}

/// `prepareDeclarationCompilationContext`.
fn prepare_declaration_compilation_context(
    input_files: &[TestFile],
    other_files: &[TestFile],
    result: &CompilationResult,
    harness_settings: &HarnessOptions,
    options: &CompilerOptions,
    // Current directory is needed for rwcRunner to be able to use currentDirectory defined in json file
    current_directory: &str,
) -> Option<DeclarationCompilationContext> {
    if options.declaration.is_true() && result.diagnostics.is_empty() {
        if options.emit_declaration_only.is_true() {
            if result.js.size() > 0 {
                panic!("Only declaration files should be generated when emitDeclarationOnly:true");
            }
            if result.dts.size() == 0 && !options.no_emit.is_true() {
                panic!(
                    "Expected at least one declaration file to be emitted when emitDeclarationOnly:true and no errors were generated"
                );
            }
        } else {
            let program = result.program.program();
            let has_content_mapper = result
                .program
                .get_source_files()
                .iter()
                .any(|file| program.get_content_mapper(*file).is_some());
            if !has_content_mapper
                && result.dts.size() != result.get_number_of_js_files(false /*include_json*/)
            {
                panic!(
                    "There were no errors and declFiles generated did not match number of js files generated"
                );
            }
        }
    }

    let mut decl_input_files: Vec<TestFile> = Vec::new();
    let mut decl_other_files: Vec<TestFile> = Vec::new();

    fn find_unit<'a>(file_name: &str, units: &'a [TestFile]) -> Option<&'a TestFile> {
        units.iter().find(|unit| unit.unit_name == file_name)
    }

    // `findResultCodeFile` — the emitted .d.ts for an input file.
    fn find_result_code_file(
        file_name: &str,
        result: &CompilationResult,
        options: &CompilerOptions,
    ) -> Option<Arc<TestFile>> {
        let source_file = result
            .program
            .get_source_file(&tspath::to_rooted_file_path(
                file_name,
                result.current_directory(),
            ))
            .unwrap_or_else(|| panic!("Program has no source file with name '{file_name}'"));
        // Is this file going to be emitted separately
        let mut source_file_name = {
            let prog = result.program.program();
            let nodes = prog.arena_of(source_file);
            nodes[source_file].as_source_file().file_name().clone()
        };

        if !options.out_dir.is_empty() {
            if let Some(relative_path) = result
                .host
                .fs()
                .case_sensitivity()
                .relative_path_from_directory(
                    &result.program.common_source_directory(),
                    &source_file_name,
                )
            {
                source_file_name = options.out_dir.resolve_relative_file(&relative_path);
            }
        }

        let dts_file_name = tsc_outputpaths::change_to_declaration_extension(
            &source_file_name,
            result.program.program(),
        );
        result.dts.get(&dts_file_name).cloned()
    }

    // `addDtsFile` — appends the file (or its emitted .d.ts) when it is
    // declaration-eligible.
    fn add_dts_file(
        file: &TestFile,
        dts_files: &mut Vec<TestFile>,
        decl_other: &[TestFile],
        result: &CompilationResult,
        options: &CompilerOptions,
    ) {
        if tspath::is_declaration_file_name(&file.unit_name)
            || tspath::has_json_file_extension(&file.unit_name)
        {
            dts_files.push(file.clone());
        } else {
            let source_file = result.program.get_source_file(&tspath::to_rooted_file_path(
                &file.unit_name,
                result.current_directory(),
            ));
            if let Some(source_file) = source_file {
                let has_mapper = {
                    let prog = result.program.program();
                    prog.get_content_mapper(source_file).is_some()
                };
                if tspath::has_ts_file_extension(&file.unit_name)
                    || (tspath::has_js_file_extension(&file.unit_name) && options.get_allow_js())
                    || has_mapper
                {
                    if let Some(decl_file) = find_result_code_file(&file.unit_name, result, options)
                        && find_unit(&decl_file.unit_name, dts_files).is_none()
                        && find_unit(&decl_file.unit_name, decl_other).is_none()
                    {
                        dts_files.push(TestFile {
                            unit_name: decl_file.unit_name.clone(),
                            content: decl_file.content.trim_start_matches('\u{feff}').to_string(),
                        });
                    }
                }
            }
        }
    }

    // if the .d.ts is non-empty, confirm it compiles correctly as well
    if options.declaration.is_true() && result.diagnostics.is_empty() && result.dts.size() > 0 {
        let mut declaration_current_directory = harness_settings.current_directory.clone();
        if !current_directory.is_empty() {
            declaration_current_directory = tspath::to_rooted_directory_path(
                current_directory,
                &harness_settings.current_directory,
            );
        }
        for file in input_files {
            add_dts_file(
                file,
                &mut decl_input_files,
                &decl_other_files,
                result,
                options,
            );
        }
        for file in other_files {
            add_dts_file(
                file,
                &mut decl_other_files,
                &decl_input_files,
                result,
                options,
            );
        }
        return Some(DeclarationCompilationContext {
            decl_input_files,
            decl_other_files,
            harness_settings: harness_settings.clone(),
            options: options.clone(),
            current_directory: declaration_current_directory,
            config: Some(result.program.program().command_line().clone()),
        });
    }
    None
}

/// `declarationCompilationResult`.
struct DeclarationCompilationResult {
    decl_input_files: Vec<TestFile>,
    decl_other_files: Vec<TestFile>,
    decl_result: CompilationResult,
}

/// `compileDeclarationFiles`.
fn compile_declaration_files(
    context: &DeclarationCompilationContext,
    symlinks: &rustc_hash::FxHashMap<String, String>,
) -> DeclarationCompilationResult {
    let tsconfig: Option<ParsedCommandLine> = context.config.as_ref().and_then(|config| {
        config.config_file.as_ref().map(|config_file| {
            let mut c = parsedcommandline::new_parsed_command_line(
                CompilerOptions::default(),
                Vec::new(),
                Vec::new(),
                config.base_directory().clone(),
                config.case_sensitivity(),
            );
            c.parsed_config = Some(ParsedOptions {
                content_mappers: config.content_mappers().to_vec(),
                ..Default::default()
            });
            c.config_file = Some(config_file.clone());
            c
        })
    });
    let decl_file_compilation_result = harnessutil::compile_files_ex(
        &context.decl_input_files,
        &context.decl_other_files,
        &context.harness_settings,
        context.options.clone(),
        &context.current_directory,
        symlinks,
        tsconfig.as_ref(),
    );
    DeclarationCompilationResult {
        decl_input_files: context.decl_input_files.clone(),
        decl_other_files: context.decl_other_files.clone(),
        decl_result: decl_file_compilation_result,
    }
}
