// Ported from tsc/internal/testrunner/runner.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `Runner` is the Go `Runner` interface.
///
/// PORT: `RunTests(t *testing.T)` loses the `*testing.T` receiver — see the
/// crate docs for the `testing.T` mapping.
pub trait Runner {
    /// `EnumerateTestFiles`.
    fn enumerate_test_files(&mut self) -> Vec<String>;
    /// `RunTests`.
    fn run_tests(&mut self);
}

/// `runTests`.
pub fn run_tests(runners: &mut [&mut dyn Runner]) {
    for runner in runners.iter_mut() {
        runner.run_tests();
    }
}
