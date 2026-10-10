// Ported from tsc/internal/execute/tsc.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `tsc.System` is `Arc<dyn tsc::System>`; `CommandLineResult` is the real
//   `tsc::CommandLineResult` (`ExitStatus` + `Option<Arc<dyn Watcher>>`) —
//   the skeleton's duplicate `status: i32` struct is removed.
// - `CommandLine` is `command_line`; there is no `ExecuteAndGetResult` in Go
//   (`tsc/cmd/tsc/main.go` calls `CommandLine` directly), so the skeleton's
//   second entry point is dropped.
// - `*tsoptions.ParsedCommandLine` becomes `Arc<ParsedCommandLine>` where it
//   is shared into `ProgramConfig`; plain borrows elsewhere.
// - `*tsc.CompileTimes` becomes `Rc<RefCell<CompileTimes>>` (EmitInput's
//   shape already made that choice).
// - `incremental::`/`build::` names below assume the natural sibling ports:
//   `incremental::{new_program, read_build_info_program, new_build_info_reader,
//   create_host, Program, Host}` and `build::{Options, new_orchestrator}` with
//   `Orchestrator::start(&Context) -> tsc::CommandLineResult`.
// - `stop_tracing`: Go's `DumpTypes` reaches the checker's arenas through
//   `*ast.Node`/`*ast.Symbol` pointers; Rust's `TypeTracer::dump_types` takes
//   a single `&[Node]`/`&[Symbol]` arena pair, but recorded `NodeId`s are
//   `local_index`-relative to their own file's arena. We supply the
//   program-global symbol arena plus the first source file's node arena, and
//   guard the dump with `catch_unwind` so a cross-arena `NodeId` misindex
//   degrades to a warning instead of crashing. PORT(deferred): locations in
//   `types_N.json` for nodes outside that arena can be wrong until the
//   tracing port grows a per-node arena lookup.

use std::io::Write as _;
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::Node;
use tsc_ast::diagnostic::new_compiler_diagnostic;
use tsc_collections::OrderedMap;
use tsc_compiler::host::{CompilerHost, new_cached_fs_compiler_host};
use tsc_compiler::program::{Program, ProgramConfig, ProgramHosts, ProgramOptions, new_program};
use tsc_core::context::Context;
use tsc_diagnostics as diagnostics;
use tsc_locale::Locale;
use tsc_tracing::tracing::{Tracing, start_tracing};
use tsc_tsoptions::commandlineparser::{parse_build_command_line, parse_command_line};
use tsc_tsoptions::generated::declarations::build_opts;
use tsc_tsoptions::parsedbuildcommandline::ParsedBuildCommandLine;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::tsconfigparsing;
use tsc_tsoptions::value::Value;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath};

use crate::tsc::{
    self, CommandLineResult, CommandLineTesting, CompileTimes, DiagnosticReporter,
    DiagnosticsReporter, ExitStatus, ExtendedConfigCache, System,
};
use crate::util::Defer;

/// `startTracingIfNeeded`.
fn start_tracing_if_needed(
    sys: &Arc<dyn System>,
    config: &ParsedCommandLine,
    testing: Option<&Arc<dyn CommandLineTesting>>,
) -> Option<Arc<Tracing>> {
    let options = config.compiler_options().expect("compiler_options");
    let trace_dir = options.generate_trace.clone();
    if trace_dir.as_string().is_empty() {
        return None;
    }
    let mut config_file_path = String::new();
    if let Some(config_file) = &config.config_file {
        config_file_path = config_file.file_name().as_string().to_string();
    }
    match start_tracing(
        sys.fs(),
        trace_dir,
        &config_file_path,
        // Go passes `testing != nil` — deterministic output in test mode.
        testing.is_some(),
    ) {
        Ok(tr) => Some(tr),
        Err(err) => {
            let _ = writeln!(
                sys.writer().guard(),
                "Warning: Failed to start tracing: {err}"
            );
            None
        }
    }
}

/// `stopTracing`.
fn stop_tracing(sys: &Arc<dyn System>, tr: Option<&Arc<Tracing>>, program: &Rc<Program>) {
    let Some(tr) = tr else { return };
    // `tracer.DumpTypes()` — supply the arenas; see the file header for the
    // per-file-arena caveat and the `catch_unwind` guard.
    let nodes_handle = program
        .source_files_slice()
        .first()
        .map(|file| program.nodes_handle(file.file_index()));
    let nodes_ref = nodes_handle.as_ref().map(|h| h.borrow());
    let empty_nodes: &[Node] = &[];
    let nodes: &[Node] = nodes_ref
        .as_ref()
        .map(|r| r.as_slice())
        .unwrap_or(empty_nodes);
    let symbols = program.symbols.borrow();
    let result = tr.stop_tracing(|tracer| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tracer.dump_types(nodes, &symbols)
        }))
        .unwrap_or_else(|_| {
            Err(tsc_tracing::tracing::Error(
                "type dump failed: node arena mismatch".to_string(),
            ))
        })
    });
    if let Err(err) = result {
        let _ = writeln!(
            sys.writer().guard(),
            "Warning: Failed to stop tracing: {err}"
        );
    }
}

/// `CommandLine`.
pub fn command_line(
    ctx: &Context,
    sys: &Arc<dyn System>,
    command_line_args: &[String],
    testing: Option<Arc<dyn CommandLineTesting>>,
) -> CommandLineResult {
    if let Some(first) = command_line_args.first() {
        match first.to_lowercase().as_str() {
            "-b" | "--b" | "-build" | "--build" => {
                return tsc_build_compilation(
                    ctx,
                    sys,
                    parse_build_command_line(command_line_args, &sys.fs(), sys.current_directory()),
                    testing,
                );
                // case "-f":
                // 	return fmtMain(sys, commandLineArgs[1], commandLineArgs[1])
            }
            _ => {}
        }
    }

    tsc_compilation(
        ctx,
        sys,
        parse_command_line(command_line_args, &sys.fs(), sys.current_directory()),
        testing,
    )
}

/// `fmtMain` — dead code in Go (the `-f` dispatch is commented out); ported
/// for completeness.
#[allow(dead_code)]
fn fmt_main(sys: &Arc<dyn System>, input: &str, output: &str) -> ExitStatus {
    let ctx = tsc_format::with_format_code_settings(
        &Context::background(),
        tsc_lsutil::get_default_format_code_settings(),
        "\n",
    );
    let file_name = tspath::to_rooted_file_path(input, &sys.current_directory());
    let input = file_name.as_string().to_string();
    let output_file_name = tspath::to_rooted_file_path(output, &sys.current_directory());
    let Some(text) = sys.fs().read_file(&file_name) else {
        let _ = writeln!(sys.writer().guard(), "File not found: {input}");
        return ExitStatus::NotImplemented;
    };
    let pathified = tspath::CaseSensitivity::CaseSensitive.path_key(&file_name.as_path());
    let script_kind = tsc_core::core::get_script_kind_from_file_name(&file_name);
    let (source_file, mut nodes) = tsc_parser::parse_source_file(
        tsc_ast::parseoptions::SourceFileParseOptions {
            file_name,
            path_key: pathified,
            ..Default::default()
        },
        &text,
        script_kind,
    );
    let edits = tsc_format::format_document(&ctx, source_file, &mut nodes);
    let new_text = tsc_core::textchange::apply_bulk_edits(&text, &edits);

    if let Err(err) = sys.fs().write_file(&output_file_name, &new_text) {
        let _ = writeln!(sys.writer().guard(), "{}", err);
        return ExitStatus::NotImplemented;
    }
    ExitStatus::Success
}

/// `tscBuildCompilation`.
fn tsc_build_compilation(
    ctx: &Context,
    sys: &Arc<dyn System>,
    build_command: ParsedBuildCommandLine,
    testing: Option<Arc<dyn CommandLineTesting>>,
) -> CommandLineResult {
    let locale = build_command.locale().clone();
    let report_diagnostic = tsc::create_diagnostic_reporter(
        sys,
        sys.writer(),
        locale.clone(),
        build_command.compiler_options.as_ref(),
    );

    if !build_command.errors.is_empty() {
        for err in &build_command.errors {
            report_diagnostic(err);
        }
        return CommandLineResult {
            status: ExitStatus::DiagnosticsPresentOutputsSkipped,
            watcher: None,
        };
    }

    // `defer profileSession.Stop()` — the guard runs when this function
    // returns.
    let _profile_guard = build_command
        .compiler_options
        .as_ref()
        .filter(|o| !o.pprof_dir.as_string().is_empty())
        .map(|o| {
            // !!! stderr?
            let session =
                tsc_pprof::begin_profiling(o.pprof_dir.as_string(), Box::new(sys.writer()));
            Defer::new(move || {
                let mut session = session;
                session.stop();
            })
        });

    if build_command
        .compiler_options
        .as_ref()
        .is_some_and(|o| o.help.is_true())
    {
        tsc::print_version(sys, &locale);
        tsc::print_build_help(sys, &locale, &build_opts().collect::<Vec<_>>());
        return CommandLineResult {
            status: ExitStatus::Success,
            watcher: None,
        };
    }

    let orchestrator = crate::build::new_orchestrator(crate::build::Options {
        sys: sys.clone(),
        command: Arc::new(build_command),
        testing,
    });
    orchestrator.start(ctx)
}

/// `tscCompilation`.
fn tsc_compilation(
    ctx: &Context,
    sys: &Arc<dyn System>,
    command_line: ParsedCommandLine,
    testing: Option<Arc<dyn CommandLineTesting>>,
) -> CommandLineResult {
    let mut config_file_name = RootedFilePath::default();
    let locale = command_line.locale().clone();
    let mut report_diagnostic = tsc::create_diagnostic_reporter(
        sys,
        sys.writer(),
        locale.clone(),
        command_line.compiler_options(),
    );

    {
        let errors = command_line
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if !errors.is_empty() {
            for e in errors.iter() {
                report_diagnostic(e);
            }
            return CommandLineResult {
                status: ExitStatus::DiagnosticsPresentOutputsSkipped,
                watcher: None,
            };
        }
    }

    // `defer profileSession.Stop()` — see `tscBuildCompilation`.
    let _profile_guard = command_line
        .compiler_options()
        .filter(|o| !o.pprof_dir.as_string().is_empty())
        .map(|o| {
            let session =
                tsc_pprof::begin_profiling(o.pprof_dir.as_string(), Box::new(sys.writer()));
            Defer::new(move || {
                let mut session = session;
                session.stop();
            })
        });

    let options = command_line.compiler_options().expect("compiler_options");

    if options.init.is_true() {
        let raw = match command_line.raw.as_ref() {
            // `commandLine.Raw.(*collections.OrderedMap[string, any])` — Go's
            // single-return assertion panics on other types.
            Some(Value::Map(m)) => m,
            _ => panic!("commandLine.Raw is not an OrderedMap"),
        };
        tsc::write_config_file(sys, &locale, &report_diagnostic, raw);
        return CommandLineResult {
            status: ExitStatus::Success,
            watcher: None,
        };
    }

    if options.version.is_true() {
        tsc::print_version(sys, &locale);
        return CommandLineResult {
            status: ExitStatus::Success,
            watcher: None,
        };
    }

    if options.help.is_true() || options.all.is_true() {
        tsc::print_help(sys, &locale, &command_line);
        return CommandLineResult {
            status: ExitStatus::Success,
            watcher: None,
        };
    }

    if options.watch.is_true() && options.list_files_only.is_true() {
        report_diagnostic(&new_compiler_diagnostic(
            &diagnostics::Options_0_and_1_cannot_be_combined,
            &["watch", "listFilesOnly"],
        ));
        return CommandLineResult {
            status: ExitStatus::DiagnosticsPresentOutputsSkipped,
            watcher: None,
        };
    }

    if !options.project.as_string().is_empty() {
        if !command_line.file_names().is_empty() {
            report_diagnostic(&new_compiler_diagnostic(
                &diagnostics::Option_project_cannot_be_mixed_with_source_files_on_a_command_line,
                &[] as &[String],
            ));
            return CommandLineResult {
                status: ExitStatus::DiagnosticsPresentOutputsSkipped,
                watcher: None,
            };
        }

        let file_or_directory = options.project.clone();
        let directory = tspath::rooted_directory_path_from_path(file_or_directory.clone());
        if sys.fs().directory_exists(&directory) {
            config_file_name = directory.resolve_file("tsconfig.json");
            if !sys.fs().file_exists(&config_file_name) {
                report_diagnostic(&new_compiler_diagnostic(
                    &diagnostics::Cannot_find_a_tsconfig_json_file_at_the_current_directory_Colon_0,
                    &[config_file_name.as_string()],
                ));
                return CommandLineResult {
                    status: ExitStatus::DiagnosticsPresentOutputsSkipped,
                    watcher: None,
                };
            }
        } else {
            config_file_name = tspath::rooted_file_path_from_path(file_or_directory.clone());
            if !sys.fs().file_exists(&config_file_name) {
                report_diagnostic(&new_compiler_diagnostic(
                    &diagnostics::The_specified_path_does_not_exist_Colon_0,
                    &[file_or_directory.as_string()],
                ));
                return CommandLineResult {
                    status: ExitStatus::DiagnosticsPresentOutputsSkipped,
                    watcher: None,
                };
            }
        }
    } else if !options.ignore_config.is_true() || command_line.file_names().is_empty() {
        let found_config_file_name = find_config_file(
            &sys.current_directory(),
            |file| sys.fs().file_exists(file),
            "tsconfig.json",
        );
        if !found_config_file_name.as_string().is_empty() {
            config_file_name = found_config_file_name;
        }
        if !command_line.file_names().is_empty() {
            if !config_file_name.as_string().is_empty() {
                // Error to not specify config file
                report_diagnostic(&new_compiler_diagnostic(
                    &diagnostics::X_tsconfig_json_is_present_but_will_not_be_loaded_if_files_are_specified_on_commandline_Use_ignoreConfig_to_skip_this_error,
                    &[] as &[String],
                ));
                return CommandLineResult {
                    status: ExitStatus::DiagnosticsPresentOutputsSkipped,
                    watcher: None,
                };
            }
        } else if config_file_name.as_string().is_empty() {
            if options.show_config.is_true() {
                report_diagnostic(&new_compiler_diagnostic(
                    &diagnostics::Cannot_find_a_tsconfig_json_file_at_the_current_directory_Colon_0,
                    &[sys.current_directory().as_string()],
                ));
            } else {
                tsc::print_version(sys, &locale);
                tsc::print_help(sys, &locale, &command_line);
            }
            return CommandLineResult {
                status: ExitStatus::DiagnosticsPresentOutputsSkipped,
                watcher: None,
            };
        }
    }

    // !!! convert to options with absolute paths is usually done here, but for ease of implementation, it's done in `tsoptions.ParseCommandLine()`
    let compiler_options_from_command_line = command_line.compiler_options().cloned();
    let mut config_for_compilation: Option<Arc<ParsedCommandLine>> = None;
    let extended_config_cache = Arc::new(ExtendedConfigCache::default());
    let compile_times = Rc::new(std::cell::RefCell::new(CompileTimes::default()));
    let mut command_line_raw: Option<OrderedMap<String, Value>> = None;
    if !config_file_name.as_string().is_empty() {
        let config_start = sys.now();
        if let Some(Value::Map(raw)) = command_line.raw.as_ref() {
            // Wrap command line options in a "compilerOptions" key to match tsconfig.json structure
            let mut wrapped = OrderedMap::new();
            wrapped.set("compilerOptions".to_string(), Value::Map(raw.clone()));
            command_line_raw = Some(wrapped);
        }
        let path = sys
            .fs()
            .case_sensitivity()
            .path_key(&config_file_name.as_path());
        let config_parse_result = tsconfigparsing::get_parsed_command_line_of_config_file_path(
            config_file_name.clone(),
            path,
            compiler_options_from_command_line.as_ref(),
            command_line_raw.as_ref(),
            &sys.fs(),
            Some(&*extended_config_cache),
        );
        compile_times.borrow_mut().config_time =
            sys.now().duration_since(config_start).unwrap_or_default();
        match config_parse_result {
            Err(errors) => {
                // these are unrecoverable errors--exit to report them as diagnostics
                for e in &errors {
                    report_diagnostic(e);
                }
                return CommandLineResult {
                    status: ExitStatus::DiagnosticsPresentOutputsGenerated,
                    watcher: None,
                };
            }
            Ok(parsed) => config_for_compilation = Some(Arc::new(parsed)),
        }
        // Updater to reflect pretty
        report_diagnostic = tsc::create_diagnostic_reporter(
            sys,
            sys.writer(),
            locale.clone(),
            compiler_options_from_command_line.as_ref(),
        );
    }
    let config_for_compilation = config_for_compilation.unwrap_or_else(|| Arc::new(command_line));

    let report_error_summary = tsc::create_report_error_summary(
        sys,
        locale.clone(),
        config_for_compilation.compiler_options(),
    );
    if compiler_options_from_command_line
        .as_ref()
        .is_some_and(|o| o.show_config.is_true())
    {
        show_config(sys, &config_for_compilation, &config_file_name);
        return CommandLineResult {
            status: ExitStatus::Success,
            watcher: None,
        };
    }
    if config_for_compilation
        .compiler_options()
        .is_some_and(|o| o.watch.is_true())
    {
        let watcher = crate::watcher::create_watcher(
            sys,
            config_for_compilation,
            compiler_options_from_command_line.as_ref(),
            command_line_raw,
            report_diagnostic,
            report_error_summary,
            testing,
        );
        watcher.start(ctx);
        let watcher: Arc<dyn tsc::Watcher> = watcher;
        return CommandLineResult {
            status: ExitStatus::Success,
            watcher: Some(watcher),
        };
    } else if config_for_compilation
        .compiler_options()
        .is_some_and(|o| o.is_incremental())
    {
        return perform_incremental_compilation(
            ctx,
            sys,
            &config_for_compilation,
            report_diagnostic,
            report_error_summary,
            &compile_times,
            testing,
        );
    }
    perform_compilation(
        ctx,
        sys,
        &config_for_compilation,
        report_diagnostic,
        report_error_summary,
        &compile_times,
        testing,
    )
}

/// `findConfigFile`.
fn find_config_file(
    search_path: &RootedDirectoryPath,
    file_exists: impl Fn(&RootedFilePath) -> bool,
    config_name: &str,
) -> RootedFilePath {
    search_path
        .for_each_ancestor_directory(|ancestor| {
            let full_config_name = ancestor.resolve_file(config_name);
            let found = file_exists(&full_config_name);
            (full_config_name, found)
        })
        .unwrap_or_default()
}

/// `getTraceFromSys`.
pub(crate) fn get_trace_from_sys(
    sys: &Arc<dyn System>,
    locale: Locale,
    testing: Option<&Arc<dyn CommandLineTesting>>,
) -> tsc_compiler::host::TraceFn {
    tsc::get_trace_with_writer_from_sys(sys.writer(), locale, testing)
}

/// `performIncrementalCompilation`.
fn perform_incremental_compilation(
    ctx: &Context,
    sys: &Arc<dyn System>,
    config: &Arc<ParsedCommandLine>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    compile_times: &Rc<std::cell::RefCell<CompileTimes>>,
    testing: Option<Arc<dyn CommandLineTesting>>,
) -> CommandLineResult {
    let content_mapper_host = tsc::new_content_mapper_host(
        ctx,
        sys,
        config.compiler_options().expect("compiler_options"),
    );
    let content_mapper_project = get_content_mapper_project(content_mapper_host.as_ref(), config);
    // `defer contentMapperProject.Close()`.
    let _project_guard = content_mapper_project.clone().map(|project| {
        Defer::new(move || {
            let _ = project.close();
        })
    });
    let host: Arc<dyn CompilerHost> = Arc::new(new_cached_fs_compiler_host(
        sys.fs(),
        sys.default_library_path(),
        // PORT(deferred): Go passes `extendedConfigCache` — the host field
        // requires `Arc<dyn ExtendedConfigCache + Send + Sync>`, but
        // `ExtendedConfigCacheEntry` holds `Cell`/`Rc` config ASTs and
        // `unsafe_code` is forbidden, so the bound is unmeetable. The cache
        // still serves the top-level config parse; project-reference
        // extended configs reparse instead (memoization lost, semantics
        // kept).
        None,
        Some(get_trace_from_sys(
            sys,
            config.locale().clone(),
            testing.as_ref(),
        )),
        content_mapper_project.clone(),
    ));
    let build_info_read_start = sys.now();
    let old_program = crate::incremental::read_build_info_program(
        config,
        crate::incremental::new_build_info_reader(host.clone()),
        &host,
    );
    compile_times.borrow_mut().build_info_read_time = sys
        .now()
        .duration_since(build_info_read_start)
        .unwrap_or_default();

    let tr = start_tracing_if_needed(sys, config, testing.as_ref());

    let parse_start = sys.now();
    let program = new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: config.clone(),
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: host.clone(),
            tracing: tr.clone(),
        },
        factories: Default::default(),
    });
    compile_times.borrow_mut().parse_time =
        sys.now().duration_since(parse_start).unwrap_or_default();
    let changes_compute_start = sys.now();
    let incremental_program = crate::incremental::new_program(
        program,
        old_program,
        Some(crate::incremental::create_host(host)),
        {
            let sys = sys.clone();
            Arc::new(move || sys.now())
        },
        testing.is_some(),
    );
    compile_times.borrow_mut().changes_compute_time = sys
        .now()
        .duration_since(changes_compute_start)
        .unwrap_or_default();
    if let Some(host) = &content_mapper_host {
        compile_times.borrow_mut().content_mapper_times = host.timings();
    }
    let incremental_program_for_nested = incremental_program.clone();
    let (result, _statistics) = tsc::emit_and_report_statistics(&mut tsc::EmitInput {
        sys,
        program_like: &*incremental_program,
        program: incremental_program.get_program(),
        config,
        report_diagnostic,
        report_error_summary,
        writer: sys.writer(),
        write_file: None,
        compile_times: compile_times.clone(),
        testing: testing.as_ref(),
        testing_mtimes_cache: None,
        tracing: tr.as_ref(),
        // `input.ProgramLike.(*incremental.Program).TakeNestedEmitTime`.
        take_nested_emit_time: Some(Box::new(move || {
            incremental_program_for_nested.take_nested_emit_time()
        })),
    });

    stop_tracing(sys, tr.as_ref(), incremental_program.get_program());

    if let Some(testing) = &testing {
        testing.on_program(&incremental_program);
    }
    CommandLineResult {
        status: result.status,
        watcher: None,
    }
}

/// `performCompilation`.
fn perform_compilation(
    ctx: &Context,
    sys: &Arc<dyn System>,
    config: &Arc<ParsedCommandLine>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    compile_times: &Rc<std::cell::RefCell<CompileTimes>>,
    testing: Option<Arc<dyn CommandLineTesting>>,
) -> CommandLineResult {
    let content_mapper_host = tsc::new_content_mapper_host(
        ctx,
        sys,
        config.compiler_options().expect("compiler_options"),
    );
    let content_mapper_project = get_content_mapper_project(content_mapper_host.as_ref(), config);
    let _project_guard = content_mapper_project.clone().map(|project| {
        Defer::new(move || {
            let _ = project.close();
        })
    });
    let host: Arc<dyn CompilerHost> = Arc::new(new_cached_fs_compiler_host(
        sys.fs(),
        sys.default_library_path(),
        // PORT(deferred): Go passes `extendedConfigCache` — the host field
        // requires `Arc<dyn ExtendedConfigCache + Send + Sync>`, but
        // `ExtendedConfigCacheEntry` holds `Cell`/`Rc` config ASTs and
        // `unsafe_code` is forbidden, so the bound is unmeetable. The cache
        // still serves the top-level config parse; project-reference
        // extended configs reparse instead (memoization lost, semantics
        // kept).
        None,
        Some(get_trace_from_sys(
            sys,
            config.locale().clone(),
            testing.as_ref(),
        )),
        content_mapper_project.clone(),
    ));

    let tr = start_tracing_if_needed(sys, config, testing.as_ref());

    let parse_start = sys.now();
    let program = new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: config.clone(),
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: host.clone(),
            tracing: tr.clone(),
        },
        factories: Default::default(),
    });
    compile_times.borrow_mut().parse_time =
        sys.now().duration_since(parse_start).unwrap_or_default();
    if let Some(host) = &content_mapper_host {
        compile_times.borrow_mut().content_mapper_times = host.timings();
    }
    let (result, _statistics) = tsc::emit_and_report_statistics(&mut tsc::EmitInput {
        sys,
        program_like: &*program,
        program: &program,
        config,
        report_diagnostic,
        report_error_summary,
        writer: sys.writer(),
        write_file: None,
        compile_times: compile_times.clone(),
        testing: testing.as_ref(),
        testing_mtimes_cache: None,
        tracing: tr.as_ref(),
        take_nested_emit_time: None,
    });

    stop_tracing(sys, tr.as_ref(), &program);

    CommandLineResult {
        status: result.status,
        watcher: None,
    }
}

/// `getContentMapperProject`.
fn get_content_mapper_project(
    host: Option<&Arc<dyn tsc_contentmapper::host::Host>>,
    config: &ParsedCommandLine,
) -> Option<Arc<dyn tsc_contentmapper::host::Project>> {
    let host = host?;
    if config.content_mappers().is_empty() {
        return None;
    }
    host.project(&tsc_contentmapper::host::ProjectSpec {
        config_file_name: config.config_name().clone(),
        mappers: config.content_mappers().to_vec(),
        compiler_options: config.compiler_options().cloned().map(Arc::new),
    })
}

/// `showConfig`.
fn show_config(
    sys: &Arc<dyn System>,
    config: &ParsedCommandLine,
    config_file_name: &RootedFilePath,
) {
    let ts_config =
        tsc_tsoptions::showconfig::convert_to_ts_config(config, config_file_name.clone());
    let writer = sys.writer();
    let mut g = writer.guard();
    let _ = tsc_json::marshal_indent_write(&mut *g, &ts_config, "", "    ");
}
