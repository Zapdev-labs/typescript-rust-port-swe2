// Ported from tsc/internal/execute/tsc/emit.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io::Write;
use std::rc::Rc;
use std::sync::Arc;
use std::time::SystemTime;

use tsc_collections::SyncMap;
use tsc_compiler::emit_host::{EmitOptions, EmitResult, WriteFileFn};
use tsc_compiler::program::{
    Program, ProgramLike, get_diagnostics_of_any_program, sort_and_deduplicate_diagnostics,
};
use tsc_core::context::Context;
use tsc_diagnostics::Message;
use tsc_locale::Locale;
use tsc_tracing::tracing::{PHASE_BIND, PHASE_CHECK, Tracing};
use tsc_tspath::PathKey;

use crate::tsc::compile::{
    CommandLineTesting, CompileAndEmitResult, CompileTimes, ExitStatus, SharedWriter, System,
};
use crate::tsc::diagnostics::{DiagnosticReporter, DiagnosticsReporter};
use crate::tsc::statistics::Statistics;

/// `GetTraceWithWriterFromSys`.
pub fn get_trace_with_writer_from_sys(
    w: SharedWriter,
    locale: Locale,
    testing: Option<&Arc<dyn CommandLineTesting>>,
) -> Box<dyn Fn(&'static Message, &[String]) + Send + Sync> {
    match testing {
        None => Box::new(move |msg: &'static Message, args: &[String]| {
            let text = msg.localize(&locale, args);
            let _ = writeln!(w.guard(), "{}", text);
        }),
        Some(testing) => testing.get_trace(w, locale),
    }
}

/// `type EmitInput struct`.
pub struct EmitInput<'a> {
    pub sys: &'a Arc<dyn System>,
    pub program_like: &'a dyn ProgramLike,
    /// `Program *compiler.Program` — the inner program for `listFiles`.
    pub program: &'a Rc<Program>,
    pub config: &'a tsc_tsoptions::parsedcommandline::ParsedCommandLine,
    pub report_diagnostic: DiagnosticReporter,
    pub report_error_summary: DiagnosticsReporter,
    pub writer: SharedWriter,
    /// `WriteFile compiler.WriteFile` — `None` is Go's nil.
    pub write_file: Option<WriteFileFn<'a>>,
    /// `CompileTimes *CompileTimes`.
    pub compile_times: Rc<std::cell::RefCell<CompileTimes>>,
    pub testing: Option<&'a Arc<dyn CommandLineTesting>>,
    /// `TestingMTimesCache *collections.SyncMap[tspath.PathKey, time.Time]`.
    pub testing_mtimes_cache: Option<&'a SyncMap<PathKey, SystemTime>>,
    /// `Tracing *tracing.Tracing`.
    pub tracing: Option<&'a Arc<Tracing>>,
    /// `program.(*incremental.Program).TakeNestedEmitTime` — set when the
    /// program is an `incremental::Program` (see `EmitFilesAndReportErrors`).
    pub take_nested_emit_time: Option<Box<dyn Fn() -> std::time::Duration + 'a>>,
}

/// `EmitAndReportStatistics`.
pub fn emit_and_report_statistics(
    input: &mut EmitInput<'_>,
) -> (CompileAndEmitResult, Option<Statistics>) {
    let mut result = emit_files_and_report_errors(input);
    if result.status != ExitStatus::Success {
        // compile exited early
        return (result, None);
    }
    result.times.borrow_mut().total_time = input.sys.since_start();

    let mut statistics = None;
    let options = input.config.compiler_options().expect("compiler_options");
    if options.diagnostics.is_true() || options.extended_diagnostics.is_true() {
        // Go runs `runtime.GC()` twice and reads `runtime.MemStats`; Rust has
        // no GC stats, so memory counters report 0 (see `statisticsFromProgram`).
        statistics = Some(Statistics::from_program(input));
        if let Some(stats) = &statistics {
            let mut g = input.writer.guard();
            stats.report(&mut *g, input.testing);
        }
    }

    if result.emit_result.emit_skipped && !result.diagnostics.is_empty() {
        result.status = ExitStatus::DiagnosticsPresentOutputsSkipped;
    } else if !result.diagnostics.is_empty() {
        result.status = ExitStatus::DiagnosticsPresentOutputsGenerated;
    }
    (result, statistics)
}

/// `EmitFilesAndReportErrors`.
pub fn emit_files_and_report_errors(input: &mut EmitInput<'_>) -> CompileAndEmitResult {
    let result_times = input.compile_times.clone();
    let ctx = Context::background();

    // `input.ProgramLike` is `&dyn ProgramLike`; the closures below need it
    // copied in — it's a reference, fine to copy.
    let program_like = input.program_like;
    let tracing = input.tracing.cloned();
    let sys = input.sys.clone();
    let times_for_bind = result_times.clone();
    let times_for_check = result_times.clone();
    let take_nested = input.take_nested_emit_time.take();

    let mut all_diagnostics = get_diagnostics_of_any_program(
        &ctx,
        program_like,
        None,
        false,
        &move |p: &dyn ProgramLike, ctx: Context, file: Option<tsc_ast::NodeId>| {
            // Options diagnostics include global diagnostics (even though we collect them separately),
            // and global diagnostics create checkers, which then bind all of the files. Do this binding
            // early so we can track the time.
            // `defer tr.Push(...)()` — the returned closure emits the end
            // event; `Defer` invokes it on drop.
            let _guard = tracing.as_ref().map(|tr| {
                crate::util::Defer::new(tr.push(
                    PHASE_BIND,
                    "bindSourceFiles",
                    Default::default(),
                    true,
                ))
            });
            let bind_start = sys.now();
            let diags = p.get_bind_diagnostics(ctx, file);
            times_for_bind.borrow_mut().bind_time =
                sys.now().duration_since(bind_start).unwrap_or_default();
            diags
        },
        &{
            let tracing = input.tracing.cloned();
            let sys = input.sys.clone();
            move |p: &dyn ProgramLike, ctx: Context, file: Option<tsc_ast::NodeId>| {
                let _guard = tracing.as_ref().map(|tr| {
                    crate::util::Defer::new(tr.push(
                        PHASE_CHECK,
                        "checkSourceFiles",
                        Default::default(),
                        true,
                    ))
                });
                let check_start = sys.now();
                let diags = p.get_semantic_diagnostics(ctx, file);
                let mut check_time = sys.now().duration_since(check_start).unwrap_or_default();
                if let Some(take_nested) = &take_nested {
                    let nested_emit_time = take_nested();
                    if nested_emit_time > check_time {
                        check_time = std::time::Duration::ZERO;
                    } else {
                        check_time -= nested_emit_time;
                    }
                    times_for_check.borrow_mut().emit_time += nested_emit_time;
                }
                times_for_check.borrow_mut().check_time = check_time;
                diags
            }
        },
    );

    let mut emit_result = EmitResult {
        emit_skipped: true,
        diagnostics: Vec::new(),
        ..Default::default()
    };
    if !input.program_like.options().list_files_only.is_true() {
        let emit_start = input.sys.now();
        emit_result = input.program_like.emit(
            ctx.clone(),
            &mut EmitOptions {
                write_file: input.write_file.take(),
                ..Default::default()
            },
        );
        result_times.borrow_mut().emit_time += input
            .sys
            .now()
            .duration_since(emit_start)
            .unwrap_or_default();
    }
    all_diagnostics.extend(emit_result.diagnostics.iter().cloned());
    if let Some(testing) = input.testing {
        if let Some(cache) = input.testing_mtimes_cache {
            testing.on_emitted_files(&emit_result, cache);
        }
    }

    let all_diagnostics = sort_and_deduplicate_diagnostics(all_diagnostics);
    for diagnostic in &all_diagnostics {
        (input.report_diagnostic)(diagnostic);
    }

    list_files(input, &emit_result);

    (input.report_error_summary)(&all_diagnostics);
    CompileAndEmitResult {
        diagnostics: all_diagnostics,
        emit_result,
        status: ExitStatus::Success,
        times: result_times,
    }
}

/// `listFiles`.
fn list_files(input: &EmitInput<'_>, emit_result: &EmitResult) {
    let writer = input.writer.clone();
    let mut g = writer.guard();
    if let Some(testing) = input.testing {
        testing.on_list_files_start(&mut *g);
    }
    let options = input.program.options();
    if options.list_emitted_files.is_true() {
        for file in &emit_result.emitted_files {
            let _ = writeln!(g, "TSFILE: {}", file.as_string());
        }
    }
    if options.explain_files.is_true() {
        input.program.explain_files(
            &mut *g,
            input.config.locale(),
            input.sys.current_directory(),
        );
    } else if options.list_files.is_true() || options.list_files_only.is_true() {
        for &file in &input.program.source_files() {
            let nodes = input.program.arena_of(file);
            let file_name = nodes[file].as_source_file().file_name().clone();
            let _ = writeln!(g, "{}", file_name.as_string());
        }
    }
    if let Some(testing) = input.testing {
        testing.on_list_files_end(&mut *g);
    }
}
