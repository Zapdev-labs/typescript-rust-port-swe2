// Ported from tsc/internal/testrunner @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// tsc-testrunner — port of tsc/internal/testrunner: the compiler/conformance
// and transpile baseline test runners plus the `// @Filename`/`// @option`
// test-case directive parser.
//
// PORT: Go's `testing.T` has no Rust equivalent. The mapping used here (and
// in tsc-testutil) is: `t.Run(name, f)` becomes a plain function call,
// `t.Parallel()` is dropped (Rust's harness parallelizes #[test]s),
// `t.Skip` becomes an early return, and `t.Error`/`t.Fatal` become panics.
// Go's `defer testutil.RecoverAndFail(t, msg)` becomes
// `catch_unwind` + [tsc_testutil::recover_and_fail].
//
// PORT(deferred): `tsc_testutil::harnessutil` and `tsc_testutil::tsbaseline`
// are still being ported in parallel. The code that calls them is written
// against their natural names and gated behind the crate feature `harness`
// (see Cargo.toml) until they land.

pub mod compiler_runner;
pub mod compiler_test_filter;
pub mod options_generated;
pub mod runner;
pub mod test_case_parser;
pub mod transpile_runner;
