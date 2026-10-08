// Ported from tsc/internal/tsoptions/diagnostics.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::LazyLock;

use tsc_diagnostics::{self as diagnostics, Message};

use crate::commandlineoption::CommandLineOptionRef;
use crate::namemap::NameMap;

/// `type DidYouMeanOptionsDiagnostics struct`.
pub struct DidYouMeanOptionsDiagnostics {
    pub alternate_mode: Option<&'static AlternateModeDiagnostics>,
    /// `OptionDeclarations` — an `Arc` closure so test workers can capture a
    /// custom declaration list (Go stores a plain slice).
    pub option_declarations:
        std::sync::Arc<dyn Fn() -> Box<dyn Iterator<Item = CommandLineOptionRef>> + Send + Sync>,
    pub unknown_option_diagnostic: &'static Message,
    pub unknown_did_you_mean_diagnostic: &'static Message,
}

/// `type AlternateModeDiagnostics struct`.
pub struct AlternateModeDiagnostics {
    pub diagnostic: &'static Message,
    pub options_name_map: fn() -> &'static NameMap,
}

/// `type ParseCommandLineWorkerDiagnostics struct`.
///
/// PORT: Go computes `optionsNameMap` lazily in `commandLineParser` via
/// `sync.Once`; the Rust parser calls `get_name_map_from_list` on
/// `option_declarations()` directly at construction, which is equivalent and
/// matches Go's lazy semantics (the map is only built when a parser runs).
pub struct ParseCommandLineWorkerDiagnostics {
    pub did_you_mean: DidYouMeanOptionsDiagnostics,
    pub option_type_mismatch_diagnostic: &'static Message,
}

/// `var CompilerOptionsDidYouMeanDiagnostics = getParseCommandLineWorkerDiagnostics(OptionsDeclarations)`.
pub fn compiler_options_did_you_mean_diagnostics() -> &'static ParseCommandLineWorkerDiagnostics {
    static D: LazyLock<ParseCommandLineWorkerDiagnostics> =
        LazyLock::new(get_parse_command_line_worker_diagnostics);
    &D
}

/// `getParseCommandLineWorkerDiagnostics` — only used for `compiler` mode
/// diagnostics in Go too; factored identically for tests.
fn get_parse_command_line_worker_diagnostics() -> ParseCommandLineWorkerDiagnostics {
    static ALT: AlternateModeDiagnostics = AlternateModeDiagnostics {
        diagnostic: &diagnostics::Compiler_option_0_may_only_be_used_with_build,
        options_name_map: crate::namemap::build_name_map,
    };
    ParseCommandLineWorkerDiagnostics {
        did_you_mean: DidYouMeanOptionsDiagnostics {
            alternate_mode: Some(&ALT),
            option_declarations: std::sync::Arc::new(|| {
                Box::new(crate::generated::declarations::options_declarations())
            }),
            unknown_option_diagnostic: &diagnostics::Unknown_compiler_option_0,
            unknown_did_you_mean_diagnostic: &diagnostics::Unknown_compiler_option_0_Did_you_mean_1,
        },
        option_type_mismatch_diagnostic: &diagnostics::Compiler_option_0_expects_an_argument,
    }
}

/// `var buildOptionsDidYouMeanDiagnostics`.
pub fn build_options_did_you_mean_diagnostics() -> &'static ParseCommandLineWorkerDiagnostics {
    static ALT: AlternateModeDiagnostics = AlternateModeDiagnostics {
        diagnostic: &diagnostics::Compiler_option_0_may_not_be_used_with_build,
        options_name_map: crate::namemap::compiler_name_map,
    };
    static D: LazyLock<ParseCommandLineWorkerDiagnostics> =
        LazyLock::new(|| ParseCommandLineWorkerDiagnostics {
            did_you_mean: DidYouMeanOptionsDiagnostics {
                alternate_mode: Some(&ALT),
                option_declarations: std::sync::Arc::new(|| {
                    Box::new(crate::generated::declarations::build_opts())
                }),
                unknown_option_diagnostic: &diagnostics::Unknown_build_option_0,
                unknown_did_you_mean_diagnostic:
                    &diagnostics::Unknown_build_option_0_Did_you_mean_1,
            },
            option_type_mismatch_diagnostic:
                &diagnostics::Build_option_0_requires_a_value_of_type_1,
        });
    &D
}

/// `getParseCommandLineWorkerDiagnostics(decls)` — the test-worker variant
/// (`ParseCommandLineTestWorker`) that captures a custom declaration list.
#[cfg(test)]
pub(crate) fn parse_command_line_worker_diagnostics_from_decls(
    decls: Vec<CommandLineOptionRef>,
) -> ParseCommandLineWorkerDiagnostics {
    static ALT: AlternateModeDiagnostics = AlternateModeDiagnostics {
        diagnostic: &diagnostics::Compiler_option_0_may_only_be_used_with_build,
        options_name_map: crate::namemap::build_name_map,
    };
    ParseCommandLineWorkerDiagnostics {
        did_you_mean: DidYouMeanOptionsDiagnostics {
            alternate_mode: Some(&ALT),
            option_declarations: std::sync::Arc::new(move || {
                let decls = decls.clone();
                Box::new(decls.into_iter()) as Box<dyn Iterator<Item = CommandLineOptionRef>>
            }),
            unknown_option_diagnostic: &diagnostics::Unknown_compiler_option_0,
            unknown_did_you_mean_diagnostic: &diagnostics::Unknown_compiler_option_0_Did_you_mean_1,
        },
        option_type_mismatch_diagnostic: &diagnostics::Compiler_option_0_expects_an_argument,
    }
}
