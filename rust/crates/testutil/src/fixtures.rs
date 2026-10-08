// Ported from tsc/internal/testutil/fixtures/benchfixtures.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's `var BenchFixtures` is initialized at package load; the Rust
// port is a `LazyLock` static — same lazily-materialized contents (file
// fixtures don't read until first use either way).

use std::sync::{Arc, LazyLock};

use tsc_repo::test_data_path;

use crate::filefixture::{self, Fixture};

/// BenchFixtures is the standard set of benchmark fixture files.
pub static BENCH_FIXTURES: LazyLock<Vec<Arc<dyn Fixture>>> = LazyLock::new(|| {
    let test_data = test_data_path();
    vec![
        // Go: filefixture.FromString("empty.ts", "empty.ts", "")
        filefixture::from_string("empty.ts", "empty.ts", ""),
        filefixture::from_file(
            "checker.ts",
            format!("{test_data}/fixtures/compiler/checker.ts"),
        ),
        filefixture::from_file(
            "dom.generated.d.ts",
            format!("{test_data}/fixtures/lib/dom.generated.d.ts"),
        ),
        filefixture::from_file(
            "Herebyfile.mjs",
            format!("{test_data}/fixtures/typescript/Herebyfile.mjs"),
        ),
        filefixture::from_file(
            "jsxComplexSignatureHasApplicabilityError.tsx",
            format!(
                "{test_data}/fixtures/testcases/compiler/jsxComplexSignatureHasApplicabilityError.tsx"
            ),
        ),
    ]
});

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bench_fixtures_names() {
        let names: Vec<&str> = BENCH_FIXTURES.iter().map(|f| f.name()).collect();
        assert_eq!(
            names,
            [
                "empty.ts",
                "checker.ts",
                "dom.generated.d.ts",
                "Herebyfile.mjs",
                "jsxComplexSignatureHasApplicabilityError.tsx",
            ]
        );
    }
}
