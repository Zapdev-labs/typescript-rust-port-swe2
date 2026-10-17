// Shared prelude for the generated fourslash suite (tools/genfourslash).
// Provides the `testing.T` analog and the run_test/run_subtest wrappers the
// generated code calls; re-exports the crates the generated tests name by
// full path so `use crate::gen_support::*` is sufficient.

pub use rustc_hash::FxHashMap;
pub use tsc_core as core_;
pub use tsc_ls as ls;
pub use tsc_lsproto as lsproto;
pub use tsc_lsutil as lsutil;
pub use tsc_testutil as testutil;

use std::panic::{AssertUnwindSafe, catch_unwind};

/// `testing.T` stand-in — carries the test name and any per-test context the
/// fourslash harness needs. Filled out once the harness API lands.
pub struct TestHandle {
    name: String,
}

impl TestHandle {
    pub fn new(name: &str) -> TestHandle {
        TestHandle { name: name.to_string() }
    }

    /// `t.Name()`.
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// `t.Name()`.
pub fn t_name() -> String {
    // Rust tests don't expose their own names; the generator only uses this
    // to build subtest labels, so the current subtest label suffices.
    "subtest".to_string()
}

/// Wraps a test body in `catch_unwind` and routes a panic through
/// `testutil::recover_and_fail` — Go's `defer testutil.RecoverAndFail(t, ...)`.
pub fn run_test(f: impl FnOnce(&mut TestHandle)) {
    let mut t = TestHandle::new("fourslash");
    if let Err(payload) = catch_unwind(AssertUnwindSafe(|| f(&mut t))) {
        tsc_testutil::recover_and_fail("Panic on fourslash test", &payload);
    }
}

/// `t.Run(name, func(t){...})` — runs the subtest body inline (Go subtests
//  share the parent test's parallel slot; sequential execution is faithful).
pub fn run_subtest(_t: &mut TestHandle, _name: String, f: impl FnOnce(&mut TestHandle)) {
    let mut t = TestHandle::new(&_name);
    if let Err(payload) = catch_unwind(AssertUnwindSafe(|| f(&mut t))) {
        tsc_testutil::recover_and_fail(&format!("Panic on fourslash subtest {_name}"), &payload);
    }
}

/// `stringtestutil.Dedent` — string in, string out (Go strings are UTF-8).
pub fn dedent(text: &str) -> String {
    String::from_utf8(tsc_testutil::stringtestutil::dedent(text.as_bytes())).unwrap()
}

fn noop_done() {}

/// `newContentMapperFourslash` — builds a fourslash test whose tsconfig wires
/// the given content-mapper package for `extensions`.
pub fn new_content_mapper_fourslash(
    _t: &mut TestHandle,
    content: &str,
    mapper: &str,
    extensions: &[&str],
) -> (tsc_fourslash::FourslashTest, fn()) {
    let quoted: Vec<String> = extensions.iter().map(|e| format!("{:?}", e)).collect();
    let content = format!(
        "// @Filename: /tsconfig.json\n{{\n\t\"compilerOptions\": {{\n\t\t\"target\": \"es2020\",\n\t\t\"module\": \"esnext\",\n\t\t\"moduleResolution\": \"bundler\",\n\t\t\"strict\": true\n\t}},\n\t\"contentMappers\": [\n\t\t{{ \"package\": \"mapper\", \"extensions\": [{}] }}\n\t]\n}}\n\n// @Filename: /node_modules/mapper/package.json\n{}\n\n{}",
        quoted.join(", "),
        tsc_testutil::contentmappertest::package_json(mapper),
        content
    );
    (
        tsc_fourslash::new_fourslash_with_options(
            &t_name(),
            "",
            &content,
            tsc_fourslash::FourslashOptions {
                content_mapper_spawner: Some(tsc_testutil::contentmappertest::new_spawner()),
                run_external_code: true,
                ..Default::default()
            },
        ),
        noop_done,
    )
}
