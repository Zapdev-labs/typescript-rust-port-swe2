// Ported from tsc/internal/execute/tsc @ ec47d33c23e464a17cdf2475632cba629bee8763

mod compile;
mod diagnostics;
mod emit;
mod extendedconfigcache;
mod help;
mod init;
mod statistics;

pub use compile::{
    CommandLineResult, CommandLineTesting, CompileAndEmitResult, CompileTimes, ExitStatus,
    SharedWriter, System, Watcher, new_content_mapper_host,
};
pub use diagnostics::{
    CliDiagnostic, Colors, DiagnosticRegistry, DiagnosticReporter, DiagnosticsReporter,
    create_builder_status_reporter, create_colors, create_diagnostic_reporter,
    create_report_error_summary, create_watch_status_reporter, default_is_pretty,
    format_status_time, get_format_opts_of_sys, quiet_diagnostic_reporter_fn,
    quiet_diagnostics_reporter_fn, should_be_pretty, wrap_cli_diagnostics,
};
pub use emit::{
    EmitInput, emit_and_report_statistics, emit_files_and_report_errors,
    get_trace_with_writer_from_sys,
};
pub use extendedconfigcache::ExtendedConfigCache;
pub use help::{print_build_help, print_help, print_version};
pub use init::write_config_file;
pub use statistics::Statistics;
