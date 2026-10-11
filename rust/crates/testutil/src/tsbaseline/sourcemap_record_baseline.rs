// Ported from tsc/internal/testutil/tsbaseline/sourcemap_record_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::options_generated::CompilerOptions;
use tsc_tspath as tspath;

use super::util::remove_test_path_prefixes;
use crate::baseline;
use crate::harnessutil::{CompilationResult, HarnessOptions};

/// `DoSourcemapRecordBaseline`.
pub fn do_sourcemap_record_baseline(
    baseline_path: &str,
    header: &str,
    options: &CompilerOptions,
    result: &CompilationResult,
    harness_settings: &HarnessOptions,
    opts: baseline::Options,
) {
    let _ = (header, harness_settings);
    let mut actual = baseline::NO_CONTENT.to_string();
    if options.source_map.is_true()
        || options.inline_source_map.is_true()
        || options.declaration_map.is_true()
    {
        let record = remove_test_path_prefixes(&result.get_source_map_record(), false);
        if !(options.no_emit_on_error.is_true() && !result.diagnostics.is_empty())
            && !record.is_empty()
        {
            actual = record;
        }
    }

    let mut baseline_path = baseline_path.to_string();
    if tspath::file_extension_is_one_of(
        &baseline_path,
        &[tspath::EXTENSION_TS, tspath::EXTENSION_TSX],
    ) {
        baseline_path = tspath::change_extension(&baseline_path, ".sourcemap.txt").into_owned();
    }

    baseline::run(&baseline_path, &actual, &opts).unwrap_or_else(|e| panic!("{e}"));
}
