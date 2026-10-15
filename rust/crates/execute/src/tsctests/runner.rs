// Ported from tsc/internal/execute/tsctests/runner.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `testing.T` follows the workspace convention (see tsc-testutil):
//   `t.Run(sub, func)` subtests flatten into `run` returning
//   `Result<(), Error>`; `t.Context()` becomes `Context::background()`
//   (test callers cancel on scope exit); `t.Parallel()` is dropped (cargo
//   runs `#[test]` fns in parallel already); `t.Errorf` returns `Err`.
// - `tscEdit.edit` is `func(*TestSys)` — `Option<Arc<dyn Fn(&TestSys)>>` so
//   `TscEdit` stays `Clone` and `Send` (the non-incremental half of an edit
//   runs on a `WorkGroup` thread).
// - Go runs the incremental-edit half and the clean rebuild half via
//   `wg.Queue` x2 + `RunAndWait`; `CommandLineResult.watcher` is
//   `Arc<dyn Watcher>` which is not `Send`, so the port queues only the
//   clean-rebuild half and runs the edit half inline — same concurrency,
//   same shared-mutation set (the queued half touches nothing shared but
//   its own `non_incremental_sys` slot).
// - `baseline.DiffText` works on bytes; its output joins `String` baselines
//   via `from_utf8_lossy` (diff content is UTF-8 in practice).
// - `filepath.Join` → plain `/` joining (baseline subfolders are always
//   forward-slash relative paths).

use std::fmt::Write as _;
use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;
use tsc_core::context::Context;
use tsc_core::workgroup::new_work_group;
use tsc_testutil::baseline;
use tsc_testutil::Error;
use tsc_tspath as tspath;

use crate::command_line;
use crate::tsc::{CommandLineResult, CommandLineTesting, ExitStatus, System};
use crate::tsctests::sys::{FileMap, TestSys, new_test_sys};

/// `type tscEdit struct`.
#[derive(Clone)]
pub struct TscEdit {
    /// `caption`.
    pub caption: String,
    /// `commandLineArgs` — `None` is Go's nil (use the input's args).
    pub command_line_args: Option<Vec<String>>,
    /// `edit` — `None` is Go's nil.
    pub edit: Option<Arc<dyn Fn(&TestSys) + Send + Sync>>,
    /// `expectedDiff`.
    pub expected_diff: String,
}

/// `var noChange = &tscEdit{caption: "no change"}`.
pub fn no_change() -> TscEdit {
    TscEdit {
        caption: "no change".to_string(),
        command_line_args: None,
        edit: None,
        expected_diff: String::new(),
    }
}

/// `var noChangeOnlyEdit = []*tscEdit{noChange}`.
pub fn no_change_only_edit() -> Vec<TscEdit> {
    vec![no_change()]
}

/// `type tscInput struct`.
#[derive(Clone, Default)]
pub struct TscInput {
    /// `subScenario`.
    pub sub_scenario: String,
    /// `commandLineArgs`.
    pub command_line_args: Vec<String>,
    /// `files`.
    pub files: FileMap,
    /// `cwd`.
    pub cwd: String,
    /// `edits`.
    pub edits: Vec<TscEdit>,
    /// `env`.
    pub env: FxHashMap<String, String>,
    /// `outputIsTTY` — `None` is Go's nil `*bool`.
    pub output_is_tty: Option<bool>,
    /// `ignoreCase`.
    pub ignore_case: bool,
    /// `windowsStyleRoot`.
    pub windows_style_root: String,
}

impl TscInput {
    /// `executeCommand`.
    pub fn execute_command(
        &self,
        ctx: &Context,
        sys: &Arc<TestSys>,
        baseline_builder: &mut String,
        command_line_args: &[String],
    ) -> CommandLineResult {
        let _ = write!(baseline_builder, "tsgo {}\n", command_line_args.join(" "));
        let sys_dyn: Arc<dyn System> = sys.clone();
        let testing: Arc<dyn CommandLineTesting> = sys.clone();
        let result = command_line(ctx, &sys_dyn, command_line_args, Some(testing));
        match result.status {
            ExitStatus::Success => baseline_builder.push_str("ExitStatus:: Success"),
            ExitStatus::DiagnosticsPresentOutputsSkipped => {
                baseline_builder.push_str("ExitStatus:: DiagnosticsPresent_OutputsSkipped")
            }
            ExitStatus::DiagnosticsPresentOutputsGenerated => {
                baseline_builder.push_str("ExitStatus:: DiagnosticsPresent_OutputsGenerated")
            }
            ExitStatus::InvalidProjectOutputsSkipped => {
                baseline_builder.push_str("ExitStatus:: InvalidProject_OutputsSkipped")
            }
            ExitStatus::ProjectReferenceCycleOutputsSkipped => {
                baseline_builder.push_str("ExitStatus:: ProjectReferenceCycle_OutputsSkipped")
            }
            ExitStatus::NotImplemented => {
                baseline_builder.push_str("ExitStatus:: NotImplemented")
            }
        }
        result
    }

    /// `run` — the `t.Run(subFolder + "/" + subScenario, ...)` subtest body.
    pub fn run(&self, scenario: &str) -> Result<(), Error> {
        let ctx = Context::background();
        // initial test tsc compile
        let mut baseline_builder = String::new();
        let sys = new_test_sys(self, false);
        let _ = write!(
            baseline_builder,
            "currentDirectory::{}\
             \nuseCaseSensitiveFileNames::{}\
             \nInput::\n",
            sys.current_directory().as_string(),
            sys.fs().case_sensitivity(),
        );
        sys.baseline_fs_with_diff(&mut baseline_builder);
        let result = self.execute_command(&ctx, &sys, &mut baseline_builder, &self.command_line_args);
        sys.serialize_state(&mut baseline_builder);
        if result.watcher.is_some() && sys.mock_watch_backend.has_watches() {
            baseline_builder.push_str(&sys.mock_watch_backend.watch_state());
        }
        let mut unexpected_diff = String::new();
        unexpected_diff.push_str(&sys.baseline_programs(&mut baseline_builder, "Initial build"));

        for (index, edit) in self.edits.iter().enumerate() {
            sys.clear_output();
            let non_incremental_sys_slot: Arc<Mutex<Option<Arc<TestSys>>>> =
                Arc::new(Mutex::new(None));
            let command_line_args = match &edit.command_line_args {
                None => self.command_line_args.clone(),
                Some(args) => args.clone(),
            };
            let wg = new_work_group(false);
            {
                // Compute build with all the edits
                let input = self.clone();
                let edits = self.edits[..=index].to_vec();
                let command_line_args = command_line_args.clone();
                let ctx = ctx.clone();
                let slot = non_incremental_sys_slot.clone();
                wg.queue(Box::new(move || {
                    let non_incremental_sys = new_test_sys(&input, true);
                    for e in &edits {
                        if let Some(edit) = &e.edit {
                            edit(&non_incremental_sys);
                        }
                    }
                    let sys_dyn: Arc<dyn System> = non_incremental_sys.clone();
                    let testing: Arc<dyn CommandLineTesting> = non_incremental_sys.clone();
                    command_line(&ctx, &sys_dyn, &command_line_args, Some(testing));
                    *slot.lock().unwrap_or_else(|e| e.into_inner()) = Some(non_incremental_sys);
                }));
            }
            {
                let _ = write!(
                    baseline_builder,
                    "\n\nEdit [{index}]:: {}\n",
                    edit.caption
                );
                if let Some(edit_fn) = &edit.edit {
                    edit_fn(&sys);
                }
                let changed_paths = sys
                    .fs_differ()
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .changed_paths();
                sys.baseline_fs_with_diff(&mut baseline_builder);

                if result.watcher.is_none() {
                    self.execute_command(&ctx, &sys, &mut baseline_builder, &command_line_args);
                } else {
                    sys.mock_watch_backend.send_changed_paths(changed_paths);
                    result.watcher.as_ref().expect("watcher").do_cycle();
                }
                sys.serialize_state(&mut baseline_builder);
                if result.watcher.is_some() && sys.mock_watch_backend.has_watches() {
                    baseline_builder.push_str(&sys.mock_watch_backend.watch_state());
                }
                unexpected_diff.push_str(&sys.baseline_programs(
                    &mut baseline_builder,
                    &format!("Edit [{index}]:: {}\n", edit.caption),
                ));
            }
            wg.run_and_wait();
            let non_incremental_sys = non_incremental_sys_slot
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .take()
                .expect("non-incremental sys");

            let diff = get_diff_for_incremental(&sys, &non_incremental_sys);
            if !diff.is_empty() {
                let explanation = if edit.expected_diff.is_empty() {
                    "!!! Unexpected diff, please review and either fix or write explanation as expectedDiff !!!"
                } else {
                    &edit.expected_diff
                };
                let _ = write!(baseline_builder, "\n\nDiff:: {explanation}\n{diff}");
                if edit.expected_diff.is_empty() {
                    let _ = write!(
                        unexpected_diff,
                        "Edit [{index}]:: {}\n!!! Unexpected diff, please review and either fix or write explanation as expectedDiff !!!\n{diff}\n",
                        edit.caption,
                    );
                }
            } else if !edit.expected_diff.is_empty() {
                let _ = write!(
                    baseline_builder,
                    "\n\nDiff:: {} !!! Diff not found but explanation present, please review and remove the explanation !!!\n",
                    edit.expected_diff,
                );
                let _ = write!(
                    unexpected_diff,
                    "Edit [{index}]:: {}\n!!! Diff not found but explanation present, please review and remove the explanation !!!\n",
                    edit.caption,
                );
            }
        }
        let baseline_result = baseline::run(
            &format!("{}.js", self.sub_scenario.replace(' ', "-")),
            &baseline_builder,
            &baseline::Options {
                subfolder: format!("{}/{}", self.get_baseline_sub_folder(), scenario),
                ..Default::default()
            },
        );
        if !unexpected_diff.is_empty() {
            return Err(Error::new(format!(
                "Test {} has unexpected diff {} with incremental build, please review the baseline file",
                self.sub_scenario, unexpected_diff,
            )));
        }
        baseline_result
    }

    /// `getBaselineSubFolder`.
    pub fn get_baseline_sub_folder(&self) -> String {
        let command_name = if self
            .command_line_args
            .iter()
            .any(|arg| matches!(arg.as_str(), "-b" | "--b" | "-build" | "--build"))
        {
            "tsbuild"
        } else {
            "tsc"
        };
        let w = if self
            .command_line_args
            .iter()
            .any(|arg| matches!(arg.as_str(), "-w" | "--w" | "-watch" | "--watch"))
        {
            "Watch"
        } else {
            ""
        };
        format!("{command_name}{w}")
    }
}

/// `getDiffForIncremental`.
pub fn get_diff_for_incremental(
    incremental_sys: &Arc<TestSys>,
    non_incremental_sys: &Arc<TestSys>,
) -> String {
    let mut diff_builder = String::new();

    let mut non_incremental_outputs = non_incremental_sys.fs.written_files.to_slice();
    non_incremental_outputs.sort();
    for non_incremental_output in &non_incremental_outputs {
        let non_incremental_output_text = non_incremental_output.as_string();
        if non_incremental_output.extension_is(tspath::EXTENSION_TS_BUILD_INFO)
            || non_incremental_output_text.ends_with(".readable.baseline.txt")
        {
            // Just check existence
            if !incremental_sys
                .fs_from_file_map()
                .file_exists(non_incremental_output)
            {
                diff_builder.push_str(&String::from_utf8_lossy(&baseline::diff_text(
                    &format!("nonIncremental {non_incremental_output_text}"),
                    &format!("incremental {non_incremental_output_text}"),
                    b"Exists",
                    b"",
                )));
                diff_builder.push('\n');
            }
        } else {
            let Some(non_incremental_text) = non_incremental_sys
                .fs_from_file_map()
                .read_file(non_incremental_output)
            else {
                panic!("Written file not found {non_incremental_output_text}");
            };
            let incremental_text = incremental_sys
                .fs_from_file_map()
                .read_file(non_incremental_output)
                .unwrap_or_default();
            if incremental_text != non_incremental_text {
                diff_builder.push_str(&String::from_utf8_lossy(&baseline::diff_text(
                    &format!("nonIncremental {non_incremental_output_text}"),
                    &format!("incremental {non_incremental_output_text}"),
                    non_incremental_text.as_bytes(),
                    incremental_text.as_bytes(),
                )));
                diff_builder.push('\n');
            }
        }
    }

    let incremental_output = incremental_sys.get_output(true);
    let non_incremental_output = non_incremental_sys.get_output(true);
    if incremental_output != non_incremental_output {
        diff_builder.push_str(&String::from_utf8_lossy(&baseline::diff_text(
            "nonIncremental.output.txt",
            "incremental.output.txt",
            non_incremental_output.as_bytes(),
            incremental_output.as_bytes(),
        )));
    }
    diff_builder
}
