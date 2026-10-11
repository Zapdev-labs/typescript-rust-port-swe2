// Ported from tsc/internal/testutil/tsbaseline/module_resolution_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::baseline;

/// `DoModuleResolutionBaseline`.
pub fn do_module_resolution_baseline(baseline_path: &str, trace: &str, opts: baseline::Options) {
    let baseline_path = super::error_baseline::ts_extension_replace(baseline_path, ".trace.json");
    let error_baseline = if !trace.is_empty() {
        trace.to_string()
    } else {
        baseline::NO_CONTENT.to_string()
    };
    baseline::run(&baseline_path, &error_baseline, &opts).unwrap_or_else(|e| panic!("{e}"));
}
