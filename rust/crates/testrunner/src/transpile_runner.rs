// Ported from tsc/internal/testrunner/transpile_runner.go @ ec47d33c23e464a17cdf2475632cba629bee8763

#[cfg(feature = "harness")]
use std::sync::LazyLock;

#[cfg(feature = "harness")]
use tsc_collections::{Set, new_set_from_items};

#[cfg(feature = "harness")]
use crate::runner::Runner;
#[cfg(feature = "harness")]
use crate::test_case_parser::{TestUnit, extract_compiler_settings, make_units_from_test};
#[cfg(feature = "harness")]
use tsc_testutil::harnessutil;
#[cfg(feature = "harness")]
use tsc_tspath::CaseSensitivity;

// PORT(deferred): `tsc_testutil::harnessutil` / `tsc_testutil::tsbaseline` are
// still being ported — see the note at the top of compiler_runner.rs.

/// `transpileBaselineRegex` — `\.[cm]?[tj]sx?$`.
fn is_transpile_baseline_file(path: &str) -> bool {
    [".ts", ".tsx", ".js", ".jsx", ".mts", ".mjs", ".cts", ".cjs"]
        .iter()
        .any(|ext| path.ends_with(ext))
}

/// `transpileVaryBy`.
#[cfg(feature = "harness")]
fn transpile_vary_by() -> &'static Set<String> {
    static TRANSPILE_VARY_BY: LazyLock<Set<String>> = LazyLock::new(|| {
        new_set_from_items(
            ["declarationmap", "sourcemap", "inlinesourcemap"]
                .into_iter()
                .map(str::to_string),
        )
    });
    &TRANSPILE_VARY_BY
}

/// `TranspileBaselineRunner`.
pub struct TranspileBaselineRunner {
    test_files: Vec<String>,
    base_path: String,
}

/// `NewTranspileBaselineRunner`.
pub fn new_transpile_baseline_runner() -> TranspileBaselineRunner {
    TranspileBaselineRunner {
        test_files: Vec::new(),
        base_path: "../testdata/tests/cases/transpile".to_string(),
    }
}

impl TranspileBaselineRunner {
    /// `EnumerateTestFiles`.
    pub fn enumerate_test_files(&mut self) -> Vec<String> {
        if !self.test_files.is_empty() {
            return self.test_files.clone();
        }
        let files = crate::compiler_runner::enumerate_files(
            &self.base_path,
            is_transpile_baseline_file,
            true,
        )
        .unwrap_or_else(|e| panic!("Could not read transpile test files: {e}"));
        self.test_files = files.clone();
        files
    }
}

/// `formatTranspileConfigurationName`.
#[cfg(feature = "harness")]
fn format_transpile_configuration_name(name: &str) -> String {
    let name = name.replace("declarationmap=", "declarationMap=");
    let name = name.replace("inlinesourcemap=", "inlineSourceMap=");
    name.replace("sourcemap=", "sourceMap=")
}

/// `appendTranspileSection`.
#[cfg(feature = "harness")]
fn append_transpile_section(result: &mut String, file_name: &str, content: &str) {
    result.push_str(&format!("//// [{file_name}] ////\r\n"));
    result.push_str(content);
    if !content.ends_with('\n') {
        result.push_str("\r\n");
    }
}

/// `cleanTranspileBaselines`.
#[cfg(feature = "harness")]
fn clean_transpile_baselines() {
    if let Err(e) =
        std::fs::remove_dir_all(crate::compiler_runner::local_base_path().join("transpile"))
        && e.kind() != std::io::ErrorKind::NotFound
    {
        panic!("Could not clean up transpile baselines: {e}");
    }
}

// ---------------------------------------------------------------------------
// Everything below requires `tsc_testutil::harnessutil` / `tsbaseline`, which
// are still being ported — gated behind `feature = "harness"`.
// ---------------------------------------------------------------------------

#[cfg(feature = "harness")]
impl Runner for TranspileBaselineRunner {
    fn enumerate_test_files(&mut self) -> Vec<String> {
        TranspileBaselineRunner::enumerate_test_files(self)
    }

    /// `RunTests`.
    fn run_tests(&mut self) {
        for file_name in self.enumerate_test_files() {
            self.run_test(&file_name);
        }
    }
}

#[cfg(feature = "harness")]
impl TranspileBaselineRunner {
    /// `runTest` — `t.Run(configuredName, ...)` inlined.
    fn run_test(&self, file_name: &str) {
        let Some(content) = tsc_vfs::osvfs::fs()
            .read_file(&tsc_tspath::rooted_file_path_from_normalized(file_name))
        else {
            panic!("Could not read transpile test file: {file_name}");
        };
        let settings = extract_compiler_settings(&content);
        let mut configurations =
            harnessutil::get_file_based_test_configurations(&settings, transpile_vary_by());
        if configurations.is_empty() {
            configurations = vec![harnessutil::NamedTestConfiguration {
                name: String::new(),
                config: settings,
            }];
        }

        let extension =
            tsc_tspath::get_any_extension_from_path(file_name, &[], CaseSensitivity::CaseSensitive)
                .into_owned();
        let base_name = tsc_tspath::get_base_file_name(file_name).into_owned();
        let just_name = base_name
            .strip_suffix(&extension)
            .unwrap_or(&base_name)
            .to_string();
        let units = make_units_from_test(&content, &base_name).test_unit_data;

        for configuration in &configurations {
            let mut configured_name = just_name.clone();
            if !configuration.name.is_empty() {
                configured_name += &format!(
                    "({})",
                    format_transpile_configuration_name(&configuration.name)
                );
            }
            // `t.Run(configuredName, ...)`.
            let mut options = tsc_core::options_generated::CompilerOptions::default();
            let mut harness_options = harnessutil::HarnessOptions::default();
            harnessutil::set_options_from_test_config(
                &configuration.config,
                &mut options,
                &mut harness_options,
                crate::compiler_runner::src_folder(),
                false,
            )
            .unwrap_or_else(|e| panic!("{e}"));

            if !options.emit_declaration_only.is_true() {
                self.run_kind(
                    &configured_name,
                    &extension,
                    &units,
                    &options,
                    &harness_options,
                    false,
                );
            }
            if options.declaration.is_true() {
                self.run_kind(
                    &configured_name,
                    &extension,
                    &units,
                    &options,
                    &harness_options,
                    true,
                );
            }
        }
    }

    /// `runKind`.
    fn run_kind(
        &self,
        configured_name: &str,
        extension: &str,
        units: &[TestUnit],
        options: &tsc_core::options_generated::CompilerOptions,
        harness_options: &harnessutil::HarnessOptions,
        declaration: bool,
    ) {
        let mut result = String::new();
        for unit in units {
            append_transpile_section(&mut result, &unit.name, &unit.content);
        }

        let ctx = tsc_core::context::Context::background(); // `t.Context()`
        for unit in units {
            let transpile_options = tsc_transpile::Options {
                compiler_options: Some(options.clone()),
                file_name: unit.name.clone(),
                report_diagnostics: harness_options.report_diagnostics,
            };
            let output = if declaration {
                tsc_transpile::transpile_declaration(&ctx, &unit.content, transpile_options)
            } else {
                tsc_transpile::transpile_module(&ctx, &unit.content, transpile_options)
            };
            let Some(output) = output else {
                panic!("transpilation was canceled"); // t.Fatal
            };

            let output_extension: std::borrow::Cow<'_, str> = if declaration {
                tsc_tspath::get_declaration_emit_extension_for_path(&unit.name)
            } else {
                std::borrow::Cow::Borrowed(tsc_outputpaths::get_output_extension(
                    &unit.name,
                    options.jsx,
                ))
            };
            let output_file_name = tsc_tspath::change_extension(&unit.name, &output_extension);
            append_transpile_section(&mut result, &output_file_name, &output.output_text);
            if !output.source_map_text.is_empty() {
                append_transpile_section(
                    &mut result,
                    &format!("{output_file_name}.map"),
                    &output.source_map_text,
                );
            }
            if !output.diagnostics.is_empty() {
                result.push_str("\r\n\r\n//// [Diagnostics reported]\r\n");
                let mut diagnostic_file_name = unit.name.clone();
                if let Some(file) =
                    tsc_ast::diagnostic::lock_diagnostic(&output.diagnostics[0]).file()
                {
                    diagnostic_file_name = file.file_name.as_string().to_string();
                }
                let error_baseline = tsc_testutil::tsbaseline::get_error_baseline(
                    &[harnessutil::TestFile {
                        unit_name: diagnostic_file_name.clone(),
                        content: unit.content.clone(),
                    }],
                    &tsc_diagnosticwriter::wrap_ast_diagnostics(
                        &output.diagnostics,
                        // PORT: the transpile Output drops its node arena;
                        // verify what tsbaseline needs when it lands.
                        &[],
                    ),
                    tsc_diagnosticwriter::compare_ast_diagnostics,
                    options.pretty.is_true(),
                );
                result.push_str(&error_baseline.replace(&diagnostic_file_name, &unit.name));
                if !result.ends_with('\n') {
                    result.push_str("\r\n");
                }
            }
        }

        let full_name = format!("{configured_name}{extension}");
        let baseline_extension: std::borrow::Cow<'_, str> = if declaration {
            tsc_tspath::get_declaration_emit_extension_for_path(&full_name)
        } else {
            std::borrow::Cow::Borrowed(tsc_outputpaths::get_output_extension(
                &full_name,
                options.jsx,
            ))
        };
        let baseline_name = format!("{configured_name}{baseline_extension}");
        if let Err(e) = tsc_testutil::baseline::run(
            &format!("transpile/{baseline_name}"),
            &result,
            &Default::default(),
        ) {
            panic!("{e}"); // t.Error
        }
    }
}

/// `RunTranspileTests`.
#[cfg(feature = "harness")]
pub fn run_transpile_tests() {
    clean_transpile_baselines();
    new_transpile_baseline_runner().run_tests();
}

/// `TestTranspile` (transpile_runner_test.go).
#[cfg(all(test, feature = "harness"))]
#[test]
fn test_transpile() {
    run_transpile_tests();
}
