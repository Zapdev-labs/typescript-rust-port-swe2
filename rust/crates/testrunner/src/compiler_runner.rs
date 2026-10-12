// Ported from tsc/internal/testrunner/compiler_runner.go @ ec47d33c23e464a17cdf2475632cba629bee8763

#[cfg(feature = "harness")]
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use tsc_repo::test_data_path;
use tsc_tspath::{RootedDirectoryPath, rooted_directory_path_from_normalized};

#[cfg(feature = "harness")]
use tsc_tspath::CaseSensitivity;

#[cfg(feature = "harness")]
use crate::runner::Runner;
#[cfg(feature = "harness")]
use crate::test_case_parser::{
    TestCaseContent, TestUnit, extract_compiler_settings, make_units_from_test,
};
#[cfg(feature = "harness")]
use rustc_hash::FxHashSet;
#[cfg(feature = "harness")]
use tsc_testutil::harnessutil;

// PORT(deferred): `tsc_testutil::harnessutil` and `tsc_testutil::tsbaseline`
// are still being ported. Every item gated on `feature = "harness"` below is
// written against their natural names — `harnessutil::X` / `tsbaseline::X` —
// with signatures mirroring the Go ones (minus the `*testing.T` receiver,
// per the crate-level PORT note). Field/method spellings on
// `harnessutil::CompilationResult` (`program`, `options`, `harness_options`,
// `diagnostics`, `trace`) are best-guess snake_case of the Go fields; adjust
// when the real module lands.

/// `srcFolder` — posix-style path to sources under test.
pub(crate) fn src_folder() -> &'static RootedDirectoryPath {
    static SRC_FOLDER: LazyLock<RootedDirectoryPath> =
        LazyLock::new(|| rooted_directory_path_from_normalized("/.src"));
    &SRC_FOLDER
}

/// `compilerBaselineRegex` — `\.tsx?$`.
fn is_compiler_baseline_file(path: &str) -> bool {
    path.ends_with(".ts") || path.ends_with(".tsx")
}

/// `requireStr`.
#[cfg(feature = "harness")]
const REQUIRE_STR: &str = "require(";

/// `referencesRegex` — `reference\spath` (`\s` = Go regexp `[\t\n\f\r ]`).
#[cfg(feature = "harness")]
fn references_path(content: &str) -> bool {
    content.match_indices("reference").any(|(i, _)| {
        let rest = &content[i + "reference".len()..];
        let mut chars = rest.chars();
        matches!(chars.next(), Some(c) if matches!(c, ' ' | '\t' | '\n' | '\x0c' | '\r'))
            && chars.as_str().starts_with("path")
    })
}

/// `localBasePath`.
#[cfg(feature = "harness")]
pub(crate) fn local_base_path() -> &'static Path {
    static LOCAL_BASE_PATH: LazyLock<PathBuf> =
        LazyLock::new(|| Path::new(test_data_path()).join("baselines").join("local"));
    &LOCAL_BASE_PATH
}

/// `harnessutil.EnumerateFiles` — walks `folder` (relative to the repo
/// testdata root), returning files whose rooted path matches `spec`.
///
/// PORT(deferred): mirrored locally until `tsc_testutil::harnessutil` lands;
/// Go's `*regexp.Regexp` spec is replaced by a `&str -> bool` predicate since
/// both callers only use `MatchString`.
pub(crate) fn enumerate_files(
    folder: &str,
    spec: fn(&str) -> bool,
    recursive: bool,
) -> std::io::Result<Vec<String>> {
    let test_data_directory = tsc_tspath::rooted_directory_path_from_absolute(test_data_path());
    let folder = tsc_tspath::to_rooted_directory_path(folder, &test_data_directory);
    list_files_worker(spec, recursive, &folder)
}

fn list_files_worker(
    spec: fn(&str) -> bool,
    recursive: bool,
    folder: &RootedDirectoryPath,
) -> std::io::Result<Vec<String>> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(folder.as_string())? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            if !recursive {
                continue;
            }
            paths.extend(list_files_worker(
                spec,
                recursive,
                &folder.resolve_directory(&entry.file_name().to_string_lossy()),
            )?);
            continue;
        }
        let path = folder.resolve_file(&entry.file_name().to_string_lossy());
        if spec(path.as_string()) {
            paths.push(path.as_string().to_string());
        }
    }
    Ok(paths)
}

/// `CompilerTestType`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CompilerTestType {
    Conformance,
    Regression,
}

impl CompilerTestType {
    /// `(*CompilerTestType) String`.
    pub fn as_str(&self) -> &'static str {
        match self {
            CompilerTestType::Regression => "compiler",
            CompilerTestType::Conformance => "conformance",
        }
    }
}

/// `CompilerBaselineRunner`.
pub struct CompilerBaselineRunner {
    test_files: Vec<String>,
    base_path: String,
    /// `testSuitName` — read only under `feature = "harness"`.
    #[cfg_attr(not(feature = "harness"), allow(dead_code))]
    test_suit_name: String,
    /// Failed test names. In Go each file runs as a `t.Run` subtest whose
    /// panic is recovered into `t.Fail`, so one failing file never aborts
    /// the rest of the suite.
    #[cfg(feature = "harness")]
    pub failures: std::cell::RefCell<Vec<String>>,
}

/// `NewCompilerBaselineRunner`.
pub fn new_compiler_baseline_runner(test_type: CompilerTestType) -> CompilerBaselineRunner {
    let test_suit_name = test_type.as_str();
    CompilerBaselineRunner {
        test_files: Vec::new(),
        base_path: format!("tests/cases/{test_suit_name}"),
        test_suit_name: test_suit_name.to_string(),
        #[cfg(feature = "harness")]
        failures: std::cell::RefCell::new(Vec::new()),
    }
}

impl CompilerBaselineRunner {
    /// `EnumerateTestFiles`.
    pub fn enumerate_test_files(&mut self) -> Vec<String> {
        if !self.test_files.is_empty() {
            return self.test_files.clone();
        }
        let files = enumerate_files(&self.base_path, is_compiler_baseline_file, true)
            .unwrap_or_else(|e| panic!("Could not read compiler test files: {e}"));
        self.test_files = files.clone();
        files
    }

    /// `cleanUpLocal`.
    #[cfg(feature = "harness")]
    fn clean_up_local(&self) {
        let local_path = local_base_path().join(&self.test_suit_name);
        if let Err(e) = std::fs::remove_dir_all(&local_path) {
            if e.kind() != std::io::ErrorKind::NotFound {
                panic!("Could not clean up local compiler tests: {e}");
            }
        }
    }
}

/// `skippedTests`.
#[cfg(feature = "harness")]
const SKIPPED_TESTS: &[&str] = &[
    // Tests that depended on typescript.d.ts in built.
    "APILibCheck.ts",
    "APISample_Watch.ts",
    "APISample_WatchWithDefaults.ts",
    "APISample_WatchWithOwnWatchHost.ts",
    "APISample_compile.ts",
    "APISample_jsdoc.ts",
    "APISample_linter.ts",
    "APISample_parseConfig.ts",
    "APISample_transform.ts",
    "APISample_watcher.ts",
    // These tests contain options that have been completely removed, so fail
    // to parse.
    "preserveUnusedImports.ts",
    "noCrashWithVerbatimModuleSyntaxAndImportsNotUsedAsValues.ts",
    "verbatimModuleSyntaxCompat.ts",
    "verbatimModuleSyntaxCompat2.ts",
    "verbatimModuleSyntaxCompat3.ts",
    "verbatimModuleSyntaxCompat4.ts",
    "preserveValueImports.ts",
    "preserveValueImports_importsNotUsedAsValues.ts",
    "preserveValueImports_errors.ts",
    "preserveValueImports_mixedImports.ts",
    "preserveValueImports_module.ts",
    "importsNotUsedAsValues_error.ts",
    "alwaysStrictNoImplicitUseStrict.ts",
    "nonPrimitiveIndexingWithForInSupressError.ts",
    "parameterInitializerBeforeDestructuringEmit.ts",
    "mappedTypeUnionConstraintInferences.ts",
    "lateBoundConstraintTypeChecksCorrectly.ts",
    "keyofDoesntContainSymbols.ts",
    "noStrictGenericChecks.ts",
    "noImplicitUseStrict_umd.ts",
    "noImplicitUseStrict_system.ts",
    "noImplicitUseStrict_es6.ts",
    "noImplicitUseStrict_commonjs.ts",
    "noImplicitAnyIndexingSuppressed.ts",
    "excessPropertyErrorsSuppressed.ts",
    "moduleNoneDynamicImport.ts",
    "moduleNoneErrors.ts",
    "noErrorUsingImportExportModuleAugmentationInDeclarationFile1.ts",
    "noErrorUsingImportExportModuleAugmentationInDeclarationFile2.ts",
    "noErrorUsingImportExportModuleAugmentationInDeclarationFile3.ts",
    "requireOfJsonFileWithModuleEmitNone.ts",
    "requireOfJsonFileWithModuleNodeResolutionEmitNone.ts",
];

/// Go: `flag.Lookup("test.run").Value.String()` — the `-test.run` pattern.
///
/// PORT: Rust's test harness takes the name filter as a bare positional
/// argument to the test binary rather than a flag, so scan argv for the first
/// non-flag argument. `TSC_TEST_FILTER` wins — `cargo test <pat>` already
/// consumes positionals for test-name filtering, so the file filter needs a
/// separate channel.
#[cfg(feature = "harness")]
fn test_run_flag() -> String {
    if let Ok(filter) = std::env::var("TSC_TEST_FILTER") {
        return filter;
    }
    let mut args = std::env::args();
    args.next(); // binary name
    args.find(|a| !a.starts_with('-')).unwrap_or_default()
}

/// `TSC_TEST_LIST` names a file containing one test basename per line; when
/// set, only those files run. Lets callers sweep the suite in bounded chunks
/// so a single process never accumulates state across thousands of tests.
#[cfg(feature = "harness")]
fn test_list_filter() -> Option<std::collections::HashSet<String>> {
    let path = std::env::var("TSC_TEST_LIST").ok()?;
    let contents = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Could not read TSC_TEST_LIST {path}: {e}"));
    Some(
        contents
            .lines()
            .map(|l| l.trim().to_string())
            .filter(|l| !l.is_empty())
            .collect(),
    )
}

// ---------------------------------------------------------------------------
// Everything below requires `tsc_testutil::harnessutil` / `tsbaseline`, which
// are still being ported — gated behind `feature = "harness"`.
// ---------------------------------------------------------------------------

#[cfg(feature = "harness")]
impl Runner for CompilerBaselineRunner {
    fn enumerate_test_files(&mut self) -> Vec<String> {
        CompilerBaselineRunner::enumerate_test_files(self)
    }

    /// `RunTests`.
    fn run_tests(&mut self) {
        self.clean_up_local();
        let files = self.enumerate_test_files();
        let filter = crate::compiler_test_filter::compiler_test_file_filter(&test_run_flag());
        let list = test_list_filter();
        for filename in files {
            let base_name = tsc_tspath::get_base_file_name(&filename);
            if SKIPPED_TESTS.contains(&base_name.as_ref()) {
                continue;
            }
            if !filter(&base_name) {
                continue;
            }
            if let Some(list) = &list {
                if !list.contains(base_name.as_ref()) {
                    continue;
                }
            }
            self.run_test(&filename);
        }
    }
}

#[cfg(feature = "harness")]
impl CompilerBaselineRunner {
    /// `runTest`.
    fn run_test(&self, filename: &str) {
        let test = get_compiler_file_based_test(filename);
        let basename = tsc_tspath::get_base_file_name(filename);
        eprintln!("[run] {basename}");
        if !test.configurations.is_empty() {
            for config in &test.configurations {
                let mut test_name = basename.to_string();
                if !config.name.is_empty() {
                    test_name += " ";
                    test_name += &config.name;
                }
                self.run_single_config_test(&test_name, &test, Some(config));
            }
        } else {
            self.run_single_config_test(&basename, &test, None);
        }
    }

    /// `runSingleConfigTest` — `t.Run(testName, ...)` inlined; `t.Parallel()`
    /// dropped; `defer testutil.RecoverAndFail` becomes `catch_unwind`.
    fn run_single_config_test(
        &self,
        test_name: &str,
        test: &CompilerFileBasedTest,
        config: Option<&harnessutil::NamedTestConfiguration>,
    ) {
        let filename = test.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let payload = make_units_from_test(&test.content, &test.filename);
            let compiler_test = CompilerTest::new(test_name, &test.filename, &payload, config);

            // `harnessutil.SkipUnsupportedCompilerOptions` — `t.Skip` becomes
            // an early return; verify signature when harnessutil lands.
            if let Some(_skip_reason) =
                harnessutil::skip_unsupported_compiler_options(&compiler_test.options)
            {
                return;
            }

            compiler_test.verify_diagnostics(&self.test_suit_name);
            compiler_test.verify_content_mapper(&self.test_suit_name);
            compiler_test.verify_java_script_output(&self.test_suit_name);
            compiler_test.verify_source_map_output(&self.test_suit_name);
            compiler_test.verify_source_map_record(&self.test_suit_name);
            compiler_test.verify_types_and_symbols(&self.test_suit_name);
            compiler_test.verify_module_resolution(&self.test_suit_name);
            compiler_test.verify_union_ordering();
            compiler_test.verify_parent_pointers();
        }));
        if let Err(payload) = result {
            let msg = tsc_testutil::describe_payload(&payload);
            eprintln!("[FAIL] {test_name}: {msg}");
            self.failures.borrow_mut().push(format!("{test_name} ({filename})"));
        }
    }
}

/// `compilerFileBasedTest`.
#[cfg(feature = "harness")]
struct CompilerFileBasedTest {
    filename: String,
    content: String,
    configurations: Vec<harnessutil::NamedTestConfiguration>,
}

/// `getCompilerFileBasedTest`.
#[cfg(feature = "harness")]
fn get_compiler_file_based_test(filename: &str) -> CompilerFileBasedTest {
    let Some(content) =
        tsc_vfs::osvfs::fs().read_file(&tsc_tspath::rooted_file_path_from_normalized(filename))
    else {
        panic!("Could not read test file: {filename}");
    };
    let settings = extract_compiler_settings(&content);
    // `harnessutil.GetFileBasedTestConfigurations`.
    let configurations = harnessutil::get_file_based_test_configurations(
        &settings,
        crate::options_generated::compiler_vary_by(),
    );
    CompilerFileBasedTest {
        filename: filename.to_string(),
        content,
        configurations,
    }
}

/// `compilerTest`.
#[cfg(feature = "harness")]
struct CompilerTest {
    /// `testName` — kept for parity with Go; nothing in the runner reads it
    /// back (it's the `t.Run` subtest name there).
    #[allow(dead_code)]
    test_name: String,
    filename: String,
    basename: String,
    /// name with configuration description, e.g. `file`
    configured_name: String,
    current_directory: RootedDirectoryPath,
    /// `*core.CompilerOptions` — `Rc` mirrors Go's shared pointer (the natural
    /// shape for the ported `CompilationResult`).
    options: std::rc::Rc<tsc_core::options_generated::CompilerOptions>,
    harness_options: harnessutil::HarnessOptions,
    result: harnessutil::CompilationResult,
    ts_config_files: Vec<harnessutil::TestFile>,
    /// equivalent to the files that will be passed on the command line
    to_be_compiled: Vec<harnessutil::TestFile>,
    /// equivalent to other files on the file system not directly passed to
    /// the compiler (ie things that are referenced by other files)
    other_files: Vec<harnessutil::TestFile>,
    has_non_dts_files: bool,
}

/// `testCaseContentWithConfig` — inlined at `new_compiler_test`.
#[cfg(feature = "harness")]
impl CompilerTest {
    /// `newCompilerTest`.
    fn new(
        test_name: &str,
        filename: &str,
        test_content: &TestCaseContent,
        named_configuration: Option<&harnessutil::NamedTestConfiguration>,
    ) -> CompilerTest {
        let basename = tsc_tspath::get_base_file_name(filename).into_owned();
        let mut configured_name = basename.clone();
        if let Some(config) = named_configuration
            && !config.name.is_empty()
        {
            let extname = tsc_tspath::get_any_extension_from_path(
                &basename,
                &[],
                CaseSensitivity::CaseSensitive,
            );
            let extensionless_basename = &basename[..basename.len() - extname.len()];
            configured_name = format!("{extensionless_basename}({}){extname}", config.name);
        }

        // `configuration` — Go's map reference copy; we clone since each
        // named configuration is consumed exactly once.
        let mut harness_config: harnessutil::TestConfiguration = named_configuration
            .map(|c| c.config.clone())
            .unwrap_or_default();

        let mut current_directory = src_folder().clone();
        if let Some(raw_current_directory) = harness_config.get("currentdirectory")
            && !raw_current_directory.is_empty()
        {
            current_directory =
                tsc_tspath::to_rooted_directory_path(raw_current_directory, src_folder());
        }

        let units = &test_content.test_unit_data;
        let mut to_be_compiled: Vec<harnessutil::TestFile> = Vec::new();
        let mut other_files: Vec<harnessutil::TestFile> = Vec::new();
        let mut ts_config_files: Vec<harnessutil::TestFile> = Vec::new();
        let has_non_dts_files = tsc_core::core::some(units, |unit| {
            !tsc_tspath::file_extension_is(&unit.name, tsc_tspath::EXTENSION_DTS)
        });
        if let Some(ts_config) = &test_content.ts_config {
            ts_config_files.push(create_harness_test_file(
                test_content.ts_config_file_unit_data.as_ref().unwrap(),
                &current_directory,
            ));
            for unit in units {
                if ts_config.parsed_config.as_ref().is_some_and(|pc| {
                    pc.file_names.contains(&tsc_tspath::to_rooted_file_path(
                        &unit.name,
                        &current_directory,
                    ))
                }) {
                    to_be_compiled.push(create_harness_test_file(unit, &current_directory));
                } else {
                    other_files.push(create_harness_test_file(unit, &current_directory));
                }
            }
        } else {
            if let Some(base_url) = harness_config.get("baseurl").cloned()
                && !tsc_tspath::is_rooted_disk_path(&base_url)
            {
                harness_config.insert(
                    "baseurl".to_string(),
                    tsc_tspath::to_rooted_directory_path(&base_url, &current_directory)
                        .as_string()
                        .to_string(),
                );
            }

            let last_unit = units.last().unwrap();
            // We need to assemble the list of input files for the compiler
            // and other related files on the 'filesystem' (ie in a multi-file
            // test). If the last file in a test uses require or a triple slash
            // reference we'll assume all other files will be brought in via
            // references, otherwise, assume all files are just meant to be in
            // the same compilation session without explicit references to one
            // another.
            if harness_config
                .get("noimplicitreferences")
                .is_some_and(|v| !v.is_empty())
                || last_unit.content.contains(REQUIRE_STR)
                || references_path(&last_unit.content)
            {
                to_be_compiled.push(create_harness_test_file(last_unit, &current_directory));
                for unit in &units[..units.len() - 1] {
                    other_files.push(create_harness_test_file(unit, &current_directory));
                }
            } else {
                to_be_compiled = tsc_core::core::map(units, |unit| {
                    create_harness_test_file(unit, &current_directory)
                });
            }
        }

        let result = harnessutil::compile_files(
            &to_be_compiled,
            &other_files,
            &harness_config,
            test_content.ts_config.as_ref(),
            &current_directory,
            &test_content.symlinks,
        );

        // Content-mapped files are transformed during program construction;
        // the transformed text is what the compiler actually parses and
        // reports positions against. Baseline that text (rather than the
        // original foreign source) so the type, symbol, and error baselines
        // line up with the compiler's positions.
        for file in to_be_compiled.iter_mut().chain(other_files.iter_mut()) {
            let path = tsc_tspath::to_rooted_file_path(&file.unit_name, &current_directory);
            if let Some(sf) = result.program.get_source_file(&path) {
                let program = result.program.program();
                let nodes = program.arena_of(sf);
                let sf_data = nodes[sf].as_source_file();
                if !sf_data.content_mapper().is_empty() {
                    file.content = sf_data.text().to_string();
                }
            }
        }

        CompilerTest {
            test_name: test_name.to_string(),
            filename: filename.to_string(),
            basename,
            configured_name,
            current_directory,
            options: result.options.clone(),
            harness_options: result.harness_options.clone(),
            ts_config_files,
            to_be_compiled,
            other_files,
            has_non_dts_files,
            result,
        }
    }

    /// `verifyDiagnostics` — `t.Run("error", ...)`.
    fn verify_diagnostics(&self, suite_name: &str) {
        let filename = self.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut files = tsc_core::core::concatenate(
                &self.ts_config_files,
                &tsc_core::core::concatenate(&self.to_be_compiled, &self.other_files),
            )
            .into_owned();
            let mut diagnostics = self.result.diagnostics.clone();
            // Content-mapped files' diagnostics are baselined separately (see
            // verifyContentMapper), where they can be rendered against the
            // correct text; the squiggle renderer here assumes a single
            // coordinate space.
            let content_mapped = self.content_mapped_file_names();
            if !content_mapped.is_empty() {
                files = tsc_core::core::filter(&files, |f| !content_mapped.contains(&f.unit_name))
                    .into_owned();
                diagnostics = tsc_core::core::filter(&diagnostics, |d| {
                    let d = tsc_ast::diagnostic::lock_diagnostic(d);
                    d.file()
                        .is_none_or(|f| !content_mapped.contains(f.file_name.as_string()))
                })
                .into_owned();
            }
            tsc_testutil::tsbaseline::do_error_baseline(
                &self.configured_name,
                &files,
                &diagnostics,
                self.result.options.pretty.is_true(),
                tsc_testutil::baseline::Options {
                    subfolder: suite_name.to_string(),
                    diff_fixup_old: Some(Box::new(|old: &str| {
                        let mut sb = String::with_capacity(old.len());
                        for line in old.split('\n') {
                            // `==== ./x` -> `==== x`
                            match line.strip_prefix("==== ./") {
                                Some(rest) => {
                                    sb.push_str("==== ");
                                    sb.push_str(rest);
                                }
                                None => sb.push_str(line),
                            }
                            sb.push('\n');
                        }
                        sb.pop();
                        sb
                    })),
                    ..Default::default()
                },
            );
        }));
        if let Err(payload) = result {
            tsc_testutil::recover_and_fail(
                &format!("Panic on creating error baseline for test {filename}"),
                &payload,
            );
        }
    }

    /// `verifyContentMapper` — `t.Run("content mapper", ...)`.
    fn verify_content_mapper(&self, suite_name: &str) {
        let filename = self.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tsc_testutil::tsbaseline::do_content_mapper_baseline(
                &self.configured_name,
                &self.result.program,
                &self.result.diagnostics,
                tsc_testutil::baseline::Options {
                    subfolder: suite_name.to_string(),
                    ..Default::default()
                },
            );
        }));
        if let Err(payload) = result {
            tsc_testutil::recover_and_fail(
                &format!("Panic on creating content mapper baseline for test {filename}"),
                &payload,
            );
        }
    }

    /// `contentMappedFileNames` — the set of absolute file names that were
    /// produced by a content mapper.
    fn content_mapped_file_names(&self) -> FxHashSet<String> {
        let program = self.result.program.program();
        let mut mapped = FxHashSet::default();
        for file in self.result.program.get_source_files() {
            if program.get_content_mapper(file).is_some() {
                let nodes = program.arena_of(file);
                mapped.insert(
                    nodes[file]
                        .as_source_file()
                        .file_name()
                        .as_string()
                        .to_string(),
                );
            }
        }
        mapped
    }

    /// `verifyJavaScriptOutput` — `t.Run("output", ...)`.
    fn verify_java_script_output(&self, suite_name: &str) {
        if !self.has_non_dts_files {
            return;
        }
        // `skippedEmitTests`.
        let skip_reason = match self.basename.as_str() {
            "filesEmittingIntoSameOutput.ts"
            | "jsFileCompilationWithJsEmitPathSameAsInput.ts"
            | "grammarErrors.ts"
            | "jsFileCompilationEmitBlockedCorrectly.ts" => Some(
                "Output order nondeterministic due to collision on filename during parallel emit.",
            ),
            "jsDeclarationsReexportAliasesEsModuleInterop.ts" => {
                Some("cls.d.ts is missing statements when run concurrently.")
            }
            "jsFileCompilationWithoutJsExtensions.ts" => Some("No files are emitted."),
            "typeOnlyMerge2.ts" | "typeOnlyMerge3.ts" => {
                Some("Nondeterministic contents when run concurrently.")
            }
            _ => None,
        };
        if skip_reason.is_some() {
            return; // t.Skip
        }

        let filename = self.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let header_components = tsc_tspath::get_path_components_relative_to(
                test_data_path(),
                &self.filename,
                CaseSensitivity::CaseInsensitive,
            );
            let header = tsc_tspath::get_path_from_path_components(&header_components);
            tsc_testutil::tsbaseline::do_js_emit_baseline(
                &self.configured_name,
                &header,
                &self.options,
                &self.result,
                &self.ts_config_files,
                &self.to_be_compiled,
                &self.other_files,
                &self.harness_options,
                tsc_testutil::baseline::Options {
                    subfolder: suite_name.to_string(),
                    ..Default::default()
                },
            );
        }));
        if let Err(payload) = result {
            tsc_testutil::recover_and_fail(
                &format!("Panic on creating js output for test {filename}"),
                &payload,
            );
        }
    }

    /// `verifySourceMapOutput` — `t.Run("sourcemap", ...)`.
    fn verify_source_map_output(&self, suite_name: &str) {
        let filename = self.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let header_components = tsc_tspath::get_path_components_relative_to(
                test_data_path(),
                &self.filename,
                CaseSensitivity::CaseInsensitive,
            );
            let header = tsc_tspath::get_path_from_path_components(&header_components);
            tsc_testutil::tsbaseline::do_sourcemap_baseline(
                &self.configured_name,
                &header,
                &self.options,
                &self.result,
                &self.harness_options,
                tsc_testutil::baseline::Options {
                    subfolder: suite_name.to_string(),
                    ..Default::default()
                },
            );
        }));
        if let Err(payload) = result {
            tsc_testutil::recover_and_fail(
                &format!("Panic on creating source map output for test {filename}"),
                &payload,
            );
        }
    }

    /// `verifySourceMapRecord` — `t.Run("sourcemap record", ...)`.
    fn verify_source_map_record(&self, suite_name: &str) {
        let filename = self.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let header_components = tsc_tspath::get_path_components_relative_to(
                test_data_path(),
                &self.filename,
                CaseSensitivity::CaseInsensitive,
            );
            let header = tsc_tspath::get_path_from_path_components(&header_components);
            tsc_testutil::tsbaseline::do_sourcemap_record_baseline(
                &self.configured_name,
                &header,
                &self.options,
                &self.result,
                &self.harness_options,
                tsc_testutil::baseline::Options {
                    subfolder: suite_name.to_string(),
                    ..Default::default()
                },
            );
        }));
        if let Err(payload) = result {
            tsc_testutil::recover_and_fail(
                &format!("Panic on creating source map record for test {filename}"),
                &payload,
            );
        }
    }

    /// `verifyTypesAndSymbols`.
    fn verify_types_and_symbols(&self, suite_name: &str) {
        if self.harness_options.no_types_and_symbols {
            return;
        }
        let program = &self.result.program;
        let combined = tsc_core::core::concatenate(&self.to_be_compiled, &self.other_files);
        let all_files = tsc_core::core::filter(&combined, |f| {
            program
                .get_source_file(&tsc_tspath::to_rooted_file_path(
                    &f.unit_name,
                    &self.current_directory,
                ))
                .is_some()
        });

        let header_components = tsc_tspath::get_path_components_relative_to(
            test_data_path(),
            &self.filename,
            CaseSensitivity::CaseInsensitive,
        );
        let header = tsc_tspath::get_path_from_path_components(&header_components);
        tsc_testutil::tsbaseline::do_type_and_symbol_baseline(
            &self.configured_name,
            &header,
            program,
            &all_files,
            tsc_testutil::baseline::Options {
                subfolder: suite_name.to_string(),
                ..Default::default()
            },
            false,
            false,
            !self.result.diagnostics.is_empty(),
        );
    }

    /// `verifyModuleResolution` — `t.Run("module resolution", ...)`.
    fn verify_module_resolution(&self, suite_name: &str) {
        if !self.options.trace_resolution.is_true() {
            return;
        }
        let filename = self.filename.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tsc_testutil::tsbaseline::do_module_resolution_baseline(
                &self.configured_name,
                &self.result.trace,
                tsc_testutil::baseline::Options {
                    subfolder: suite_name.to_string(),
                    skip_diff_with_old: true,
                    ..Default::default()
                },
            );
        }));
        if let Err(payload) = result {
            tsc_testutil::recover_and_fail(
                &format!("Panic on creating module resolution baseline for test {filename}"),
                &payload,
            );
        }
    }

    /// `verifyUnionOrdering` — `t.Run("union ordering", ...)`.
    ///
    /// PORT(deferred): `Checker::union_types_iter` and `Checker::types_handle`
    /// are `pub(crate)` in tsc-checker — a public accessor is needed before
    /// this compiles. `compare_types` lives at `tsc_checker::utilities`.
    fn verify_union_ordering(&self) {
        let p = self.result.program.program();
        p.for_each_checker_parallel(&mut |_, checker| {
            let checker = checker.borrow();
            let types = checker.types_handle();
            for union in checker.union_types_iter() {
                // PORT: `types.get` returns a `TypeReadGuard`; `to_vec` up
                // front so the borrow doesn't outlive the temporary.
                let union_types = types.get(union).types().to_vec();

                let mut reversed = union_types.clone();
                reversed.reverse();
                reversed
                    .sort_by(|a, b| tsc_checker::utilities::compare_types(&types, checker.symbol_arena.as_ref(), &checker.type_mappers, *a, *b).cmp(&0));
                assert_eq!(
                    reversed, union_types,
                    "compareTypes does not sort union types consistently"
                );

                let mut shuffled = union_types.clone();
                let mut rng = Pcg::new(1234, 5678);
                for _ in 0..10 {
                    rng.shuffle(&mut shuffled);
                    shuffled.sort_by(|a, b| {
                        tsc_checker::utilities::compare_types(&types, checker.symbol_arena.as_ref(), &checker.type_mappers, *a, *b).cmp(&0)
                    });
                    assert_eq!(
                        shuffled, union_types,
                        "compareTypes does not sort union types consistently"
                    );
                }
            }
        });
    }

    /// `verifyParentPointers` — `t.Run("source file parent pointers", ...)`.
    fn verify_parent_pointers(&self) {
        fn verify_node(node: tsc_ast::NodeId, parent: tsc_ast::NodeId, nodes: &[tsc_ast::Node]) {
            let n = &nodes[node];
            assert!(n.parent.is_some(), "parent node does not exist");
            assert!(
                n.parent == Some(parent),
                "parent node does not match traversed parent: {}: {}",
                n.kind.kind_string(),
                if !tsc_ast::utilities::node_is_synthesized(n) {
                    let sf = tsc_ast::utilities::get_source_file_of_node(Some(node), nodes)
                        .expect("source file");
                    nodes[sf].as_source_file().text()[n.loc.pos() as usize..n.loc.end() as usize]
                        .to_string()
                } else {
                    "!synthetic! no text available".to_string()
                }
            );
            n.for_each_child(nodes, &mut |child| {
                verify_node(child, node, nodes);
                false
            });
        }

        let program = self.result.program.program();
        for f in self.result.program.get_source_files() {
            let nodes = program.arena_of(f);
            let path_key = nodes[f].as_source_file().path_key();
            if self.result.program.is_source_file_default_library(path_key) {
                continue;
            }
            nodes[f].for_each_child(&nodes, &mut |child| {
                verify_node(child, f, &nodes);
                false
            });
        }
    }
}

/// `createHarnessTestFile`.
#[cfg(feature = "harness")]
fn create_harness_test_file(
    unit: &TestUnit,
    current_directory: &RootedDirectoryPath,
) -> harnessutil::TestFile {
    harnessutil::TestFile {
        unit_name: tsc_tspath::to_rooted_file_path(&unit.name, current_directory)
            .as_string()
            .to_string(),
        content: unit.content.clone(),
    }
}

/// Deterministic PRNG for the union-ordering shuffle — Go's
/// `math/rand/v2` `rand.New(rand.NewPCG(1234, 5678))`. The exact shuffle
/// sequence does not matter to the assertion, so a small PCG32 stands in.
#[cfg(feature = "harness")]
struct Pcg {
    state: u64,
    inc: u64,
}

#[cfg(feature = "harness")]
impl Pcg {
    fn new(seed: u64, seq: u64) -> Pcg {
        let mut rng = Pcg {
            state: 0,
            inc: (seq << 1) | 1,
        };
        rng.next_u32();
        rng.state = rng.state.wrapping_add(seed);
        rng.next_u32();
        rng
    }

    fn next_u32(&mut self) -> u32 {
        let old = self.state;
        self.state = old.wrapping_mul(6364136223846793005).wrapping_add(self.inc);
        let xorshifted = (((old >> 18) ^ old) >> 27) as u32;
        let rot = (old >> 59) as u32;
        xorshifted.rotate_right(rot)
    }

    /// `rng.Shuffle` — Fisher–Yates.
    fn shuffle<T>(&mut self, slice: &mut [T]) {
        for i in (1..slice.len()).rev() {
            let j = (self.next_u32() as usize) % (i + 1);
            slice.swap(i, j);
        }
    }
}

/// `runCompilerTests` (compiler_runner_test.go `TestLocal`).
#[cfg(all(test, feature = "harness"))]
#[test]
fn test_local() {
    if !tsc_bundled::EMBEDDED {
        return; // t.Skip: "bundled files are not embedded"
    }
    let _guard = test_main();
    // Go's runtime grows goroutine stacks up to `TS_GO_DEBUG_STACK_LIMIT`
    // (default 1GB); Rust test threads get a fixed ~2MB, which
    // deep-recursion stress tests (e.g. binderBinaryExpressionStressJs)
    // overflow. Run the suite on a thread with a comparably-sized stack.
    let stack_size = tsc_core::core::debug_stack_limit()
        .unwrap_or(0)
        .max(1 << 30);
    std::thread::Builder::new()
        .stack_size(stack_size)
        .spawn(test_local_inner)
        .expect("spawn test_local worker")
        .join()
        .expect("test_local worker panicked");
}

#[cfg(all(test, feature = "harness"))]
fn test_local_inner() {
    let mut runners: Vec<CompilerBaselineRunner> = vec![
        new_compiler_baseline_runner(CompilerTestType::Regression),
        new_compiler_baseline_runner(CompilerTestType::Conformance),
    ];
    let mut seen_tests = tsc_collections::Set::<String>::new();
    for runner in &mut runners {
        for test in runner.enumerate_test_files() {
            let test = tsc_tspath::get_base_file_name(&test).into_owned();
            assert!(!seen_tests.has(&test), "Duplicate test file: {test}");
            seen_tests.add(test);
        }
    }
    for runner in &mut runners {
        runner.run_tests();
    }
    let failures: Vec<String> = runners
        .iter()
        .flat_map(|r| r.failures.borrow().clone())
        .collect();
    if !failures.is_empty() {
        panic!("{} compiler baseline test(s) failed:\n{}", failures.len(), failures.join("\n"));
    }
}

// PORT: testmain_test.go `TestMain` — `core.ApplyDebugStackLimit()` +
// `baseline.Track()`. Rust has no TestMain hook for lib tests; call this at
// the top of each baseline-driving test and hold the guard.
#[allow(dead_code)]
pub(crate) fn test_main() -> tsc_testutil::baseline::TrackGuard {
    tsc_core::core::apply_debug_stack_limit();
    tsc_testutil::baseline::track()
}
