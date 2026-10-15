// Ported from tsc/internal/fourslash/statebaseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// ASSUMPTIONS about the parallel fourslash.rs port (all `pub(crate)`):
//   - `FourslashTest` has fields `test_data: TestData`,
//     `state_baseline: Option<StateBaseline>`,
//     `open_files` (set of `RootedFilePath`, `.contains`),
//     `vfs: Arc<dyn Vfs>`, `client` with
//     `send_request(&self, &RequestInfo<P, R>, P) -> (_, R, bool)` and
//     `server() -> &Server` where `server().session().snapshot() -> Arc<project::Snapshot>`.
//   - `fourslash::is_lib_file(&str) -> bool`.
//   - Go's `t *testing.T` is dropped; `assert.Assert(t, x)` → `assert!(x)`.
//
// PORT notes:
//   - `stateBaseline.baseline` is `Vec<u8>` (FsDiffer writes raw bytes);
//     `addResultToBaseline`/`baselineState` append `&str` as bytes.
//   - `*project.TestConfigEntry` (iter.Seq fields) is snapshotted eagerly into
//     `OwnedConfigEntry` so diff closures can outlive registry borrows.
//   - Go compares `serializedConfigFileRegistry == configFileRegistry` by
//     pointer; the port stores the address of the `&ConfigFileRegistry` it
//     cloned (`RegistrySnapshot::source_addr`).

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, Write};
use std::rc::Rc;
use std::sync::Arc;

use serde::Serialize;

use tsc_collections::{OrderedMap, SyncSet};
use tsc_compiler::program::Program;
use tsc_json as json;
use tsc_lsconv::file_name_to_document_uri;
use tsc_lsproto::{HoverParams, Method, Position, TextDocumentIdentifier};
use tsc_project::configfileregistry::{
    ConfigFileRegistry, TestConfigEntry,
};
use tsc_project::snapshot::Snapshot;
use tsc_testutil::fsbaselineutil::FsDiffer;
use tsc_tspath::RootedFilePath;
use tsc_vfs::Vfs;
use tsc_vfs::iovfs::{self, FsWithSys};

use crate::fourslash::{FourslashTest, is_lib_file};

/// `type stateBaseline struct`.
pub(crate) struct StateBaseline {
    /// `baseline` is `RefCell<String>` — `verify_baselines` reads it via
    /// `&state_baseline.baseline.borrow()`.
    pub(crate) baseline: RefCell<String>,
    pub(crate) fs_differ: FsDiffer,
    is_initialized: bool,

    /// `serializedProjects` — `map[string]*compiler.Program`.
    serialized_projects: HashMap<String, Option<Rc<Program>>>,
    serialized_open_files: HashMap<RootedFilePath, OpenFileInfo>,
    serialized_config_file_registry: Option<RegistrySnapshot>,
}

/// A shallow `ConfigFileRegistry` clone plus the identity (`&` address) of the
/// registry it was cloned from — stands in for Go's stored `*ConfigFileRegistry`.
struct RegistrySnapshot {
    source_addr: usize,
    registry: ConfigFileRegistry,
}

/// `openFileInfo`.
#[derive(Clone, Default)]
struct OpenFileInfo {
    default_project_name: String,
    all_projects: Vec<String>,
}

/// `newStateBaseline` — `fsFromMap iovfs.FsWithSys`.
///
/// PORT: `FsDiffer` stores `Arc<dyn Vfs>` (to re-assert `FsWithSys` lazily),
/// so the `&dyn FsWithSys` is re-wrapped in `iovfs::from(fsys, case)` — the
/// inner `Arc<dyn Fs>` (the MapFS) is shared, preserving Go's identity.
pub(crate) fn new_state_baseline(fs_from_map: &dyn FsWithSys) -> StateBaseline {
    let fs = iovfs::from(fs_from_map.fsys(), fs_from_map.case_sensitivity());
    let mut state_baseline = StateBaseline {
        baseline: RefCell::new(String::new()),
        fs_differ: FsDiffer::new(fs, None, Arc::new(SyncSet::new())),
        is_initialized: false,
        serialized_projects: HashMap::new(),
        serialized_open_files: HashMap::new(),
        serialized_config_file_registry: None,
    };
    {
        let mut baseline = state_baseline.baseline.borrow_mut();
        baseline.push_str(&format!(
            "CaseSensitivity: {}\n",
            fs_from_map.case_sensitivity()
        ));
        let mut buf = Vec::new();
        state_baseline.fs_differ.baseline_fs_with_diff(&mut buf);
        baseline.push_str(&String::from_utf8_lossy(&buf));
    }
    state_baseline
}

/// `type requestOrMessage struct` — `params,omitzero` is emulated by
/// marshaling params to a `Value` and skipping `null`.
#[derive(Serialize)]
struct RequestOrMessage {
    method: Method,
    #[serde(skip_serializing_if = "serde_json::Value::is_null")]
    params: serde_json::Value,
}

impl FourslashTest {
    /// `baselineRequestOrNotification`.
    pub(crate) fn baseline_request_or_notification<P: Serialize>(
        &mut self,
        method: &Method,
        params: &P,
    ) {
        if !self.test_data.is_state_baselining_enabled() {
            return;
        }

        let request_or_message = RequestOrMessage {
            method: method.clone(),
            params: serde_json::to_value(params).unwrap_or(serde_json::Value::Null),
        };
        // Go: `res, _ := json.Marshal(...)` — errors yield no output.
        let res = json::marshal(&request_or_message, &[json::with_indent("  ")])
            .unwrap_or_default();
        let state_baseline = self
            .state_baseline
            .as_mut()
            .expect("state baselining enabled but stateBaseline is not initialized");
        let mut baseline = state_baseline.baseline.borrow_mut();
        baseline.push('\n');
        baseline.push_str(&String::from_utf8_lossy(&res));
        baseline.push('\n');
        drop(baseline);
        state_baseline.is_initialized = true;
    }

    /// `baselineProjectsAfterNotification`.
    pub(crate) fn baseline_projects_after_notification(&mut self, file_name: &RootedFilePath) {
        if !self.test_data.is_state_baselining_enabled() {
            return;
        }
        // Do hover so we have snapshot to check things on!!
        let (_res_msg, _result, ok) = self.client.send_request(
            &tsc_lsproto::TEXT_DOCUMENT_HOVER_INFO,
            Some(HoverParams {
                text_document: TextDocumentIdentifier {
                    uri: file_name_to_document_uri(file_name),
                },
                position: Position {
                    line: 0,
                    character: 0,
                },
                ..Default::default()
            }),
        );
        assert!(ok, "hover request failed");
        self.baseline_state();
    }

    /// `baselineState`.
    pub(crate) fn baseline_state(&mut self) {
        if !self.test_data.is_state_baselining_enabled() {
            return;
        }

        let serialized = self.serialized_state();
        if !serialized.is_empty() {
            let state_baseline = self
                .state_baseline
                .as_mut()
                .expect("state baselining enabled but stateBaseline is not initialized");
            state_baseline
                .baseline
                .borrow_mut()
                .push('\n');
            state_baseline
                .baseline
                .borrow_mut()
                .push_str(&String::from_utf8_lossy(&serialized));
        }
    }

    /// `serializedState`.
    fn serialized_state(&mut self) -> Vec<u8> {
        let mut builder: Vec<u8> = Vec::new();
        self.state_baseline
            .as_mut()
            .expect("state baselining enabled but stateBaseline is not initialized")
            .fs_differ
            .baseline_fs_with_diff(&mut builder);
        if builder.trim_ascii().is_empty() {
            builder.clear();
        }

        self.print_state_diff(&mut builder);
        builder
    }
}

/// `type projectInfo = *compiler.Program` — `Option<Rc<Program>>` (nil-able).
type ProjectInfo = Option<Rc<Program>>;

/// `diffTableOptions`.
#[derive(Clone)]
struct DiffTableOptions {
    indent: String,
    sort_keys: bool,
}

/// `diffTable`.
struct DiffTable {
    diff: OrderedMap<String, String>,
    options: DiffTableOptions,
}

impl DiffTable {
    fn new(options: DiffTableOptions) -> DiffTable {
        DiffTable {
            diff: OrderedMap::new(),
            options,
        }
    }

    fn add(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.diff.set(key.into(), value.into());
    }

    fn print(&self, w: &mut dyn io::Write, header: &str) {
        let count = self.diff.size();
        if count == 0 {
            return;
        }
        if !header.is_empty() {
            let _ = write!(w, "{}{}\n", self.options.indent, header);
        }
        let mut diff_keys = Vec::with_capacity(count);
        let mut key_width = 0;
        let indent = format!("{}  ", self.options.indent);
        for key in self.diff.keys() {
            key_width = key_width.max(key.len());
            diff_keys.push(key);
        }
        if self.options.sort_keys {
            diff_keys.sort();
        }

        for key in diff_keys {
            let value = self.diff.get_or_zero(key);
            // `%-*s` — left-align key in keyWidth+1.
            let _ = write!(w, "{indent}{key:<key_width$} {value}\n", key_width = key_width + 1);
        }
    }
}

/// `diffTableWriter[T ~string]` — Go keys are `~string`; the port keys by
/// `String` and sorts with BTreeMap, matching `slices.Sort(keys)`.
struct DiffTableWriter<'a> {
    has_change: bool,
    header: String,
    diffs: std::collections::BTreeMap<String, Box<dyn Fn(&mut dyn io::Write) + 'a>>,
}

impl<'a> DiffTableWriter<'a> {
    fn new(header: &str) -> DiffTableWriter<'a> {
        DiffTableWriter {
            has_change: false,
            header: header.to_string(),
            diffs: std::collections::BTreeMap::new(),
        }
    }

    fn set_has_change(&mut self) {
        self.has_change = true;
    }

    fn add(&mut self, key: String, f: impl Fn(&mut dyn io::Write) + 'a) {
        self.diffs.insert(key, Box::new(f));
    }

    fn print(&self, w: &mut dyn io::Write) {
        if self.has_change {
            let _ = write!(w, "{}::\n", self.header);
            for f in self.diffs.values() {
                f(w);
            }
        }
    }
}

/// `areIterSeqEqual` — collect + sort + equal.
fn are_iter_seq_equal<T: Ord + Clone>(
    a: impl IntoIterator<Item = T>,
    b: impl IntoIterator<Item = T>,
) -> bool {
    let mut a: Vec<T> = a.into_iter().collect();
    let mut b: Vec<T> = b.into_iter().collect();
    a.sort();
    b.sort();
    a == b
}

/// `printSlicesWithDiffTable`.
fn print_slices_with_diff_table(
    w: &mut dyn io::Write,
    header: &str,
    new_slice: &[String],
    get_old_slice: impl Fn() -> Vec<String>,
    options: &DiffTableOptions,
    top_change: &str,
    is_default: Option<&dyn Fn(&str) -> bool>,
) {
    let mut old_slice = Vec::new();
    if top_change == "*modified*" {
        old_slice = get_old_slice();
    }
    let mut table = DiffTable::new(options.clone());
    for entry in new_slice {
        let mut entry_change = "";
        if is_default.is_some_and(|is_default| is_default(entry)) {
            entry_change = "(default) ";
        }
        if top_change == "*modified*" && !old_slice.contains(entry) {
            entry_change = "*new*";
        }
        table.add(entry.clone(), entry_change);
    }
    if top_change == "*modified*" {
        for entry in &old_slice {
            if !new_slice.contains(entry) {
                table.add(entry.clone(), "*deleted*");
            }
        }
    }
    table.print(w, header);
}

/// `printStringIterSeqWithDiffTable` — `sliceFromIterSeqString` sorting folded in.
fn print_string_iter_seq_with_diff_table(
    w: &mut dyn io::Write,
    header: &str,
    new_slice: &[String],
    get_old_slice: impl Fn() -> Vec<String>,
    options: &DiffTableOptions,
    top_change: &str,
) {
    let mut new_sorted = new_slice.to_vec();
    new_sorted.sort();
    print_slices_with_diff_table(
        w,
        header,
        &new_sorted,
        || {
            let mut old = get_old_slice();
            old.sort();
            old
        },
        options,
        top_change,
        None,
    );
}

/// Go `*compiler.Program` pointer equality — `Rc` identity.
fn same_program(a: &ProjectInfo, b: &ProjectInfo) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => Rc::ptr_eq(a, b),
        (None, None) => true,
        _ => false,
    }
}

impl FourslashTest {
    /// `printStateDiff`.
    fn print_state_diff(&mut self, w: &mut dyn io::Write) {
        let Some(state_baseline) = self.state_baseline.as_ref() else {
            return;
        };
        if !state_baseline.is_initialized {
            return;
        }
        // ASSUMPTION: `client.server().session().snapshot()` mirrors
        // `f.client.Server.Session().Snapshot()` (`Server` is a pub field on
        // Go's `lsptestutil.LSPClient`; the Rust wrapper exposes `server()`).
        let snapshot = self.client.server().session().snapshot();

        self.print_projects_diff(&snapshot, w);
        self.print_open_files_diff(&snapshot, w);
        self.print_config_file_registry_diff(&snapshot, w);
    }

    /// `printProjectsDiff`.
    fn print_projects_diff(&mut self, snapshot: &Snapshot, w: &mut dyn io::Write) {
        let mut current_projects: HashMap<String, ProjectInfo> = HashMap::new();
        let options = DiffTableOptions {
            indent: "  ".to_string(),
            sort_keys: false,
        };
        let mut projects_diff_table = DiffTableWriter::new("Projects");

        for project in snapshot.project_collection.projects() {
            let program: ProjectInfo = project.get_program().cloned();
            let mut old_program: ProjectInfo = None;
            let project_id = project.id().0.clone();
            current_projects.insert(project_id.clone(), program.clone());
            let project_change = if let Some(existing) = self
                .state_baseline
                .as_ref()
                .expect("state baseline")
                .serialized_projects
                .get(&project_id)
            {
                old_program = existing.clone();
                if !same_program(&old_program, &program) {
                    projects_diff_table.set_has_change();
                    "*modified*"
                } else {
                    ""
                }
            } else {
                projects_diff_table.set_has_change();
                "*new*"
            };

            let project_change = project_change.to_string();
            let options_for_diff = options.clone();
            projects_diff_table.add(project_id.clone(), move |w| {
                let _ = write!(w, "  [{project_id}] {project_change}\n");
                let mut sub_diff = DiffTable::new(options_for_diff.clone());
                if let Some(program) = &program {
                    for file in program.source_files() {
                        let mut file_diff = "";
                        let arena = program.arena_of(file);
                        let source_file = arena[file].as_source_file();
                        let file_name = source_file.file_name();
                        // No need to write "*new*" for files as its obvious
                        if project_change == "*modified*" {
                            match &old_program {
                                None => {
                                    if !is_lib_file(file_name.as_string()) {
                                        file_diff = "*new*";
                                    }
                                }
                                Some(old_program) => {
                                    match old_program
                                        .get_source_file_by_path(source_file.path_key())
                                    {
                                        None => file_diff = "*new*",
                                        Some(old_file)
                                            if !(old_file == file
                                                && Rc::ptr_eq(
                                                    &old_program.arena_of(old_file),
                                                    &arena,
                                                )) =>
                                        {
                                            file_diff = "*modified*";
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                        if !file_diff.is_empty() || !is_lib_file(file_name.as_string()) {
                            sub_diff.add(file_name.as_string().to_string(), file_diff);
                        }
                    }
                }
                if !same_program(&old_program, &program)
                    && let Some(old_program) = &old_program
                {
                    for file in old_program.source_files() {
                        let old_arena = old_program.arena_of(file);
                        let old_source_file = old_arena[file].as_source_file();
                        if program.is_none()
                            || program
                                .as_ref()
                                .unwrap()
                                .get_source_file_by_path(old_source_file.path_key())
                                .is_none()
                        {
                            sub_diff.add(
                                old_source_file.file_name().as_string().to_string(),
                                "*deleted*",
                            );
                        }
                    }
                }
                sub_diff.print(w, "");
            });
        }

        let serialized_project_names: Vec<String> = self
            .state_baseline
            .as_ref()
            .expect("state baseline")
            .serialized_projects
            .keys()
            .cloned()
            .collect();
        for project_name in serialized_project_names {
            if !current_projects.contains_key(&project_name) {
                projects_diff_table.set_has_change();
                let info = self
                    .state_baseline
                    .as_ref()
                    .expect("state baseline")
                    .serialized_projects
                    .get(&project_name)
                    .cloned()
                    .expect("project name collected from map");
                let project_name_for_diff = project_name.clone();
                let options_for_diff = options.clone();
                projects_diff_table.add(project_name.clone(), move |w| {
                    let _ = write!(w, "  [{project_name_for_diff}] *deleted*\n");
                    let mut sub_diff = DiffTable::new(options_for_diff.clone());
                    if let Some(info) = &info {
                        for file in info.source_files() {
                            let arena = info.arena_of(file);
                            let source_file = arena[file].as_source_file();
                            if !is_lib_file(source_file.file_name().as_string()) {
                                sub_diff.add(
                                    source_file.file_name().as_string().to_string(),
                                    "",
                                );
                            }
                        }
                    }
                    sub_diff.print(w, "");
                });
            }
        }
        self.state_baseline
            .as_mut()
            .expect("state baseline")
            .serialized_projects = current_projects;
        projects_diff_table.print(w);
    }

    /// `printOpenFilesDiff`.
    fn print_open_files_diff(&mut self, snapshot: &Snapshot, w: &mut dyn io::Write) {
        let mut current_open_files: HashMap<RootedFilePath, OpenFileInfo> = HashMap::new();
        let mut files_diff_table = DiffTableWriter::new("Open Files");
        let options = DiffTableOptions {
            indent: "  ".to_string(),
            sort_keys: true,
        };
        for file_name in &self.open_files {
            let path = self.vfs.case_sensitivity().path_key(&file_name.as_path());
            let default_project = snapshot.project_collection.get_default_project(&path);
            let mut new_file_info = OpenFileInfo::default();
            if let Some(default_project) = &default_project {
                new_file_info.default_project_name = default_project.id().0.clone();
            }
            for project in snapshot.project_collection.projects() {
                if let Some(program) = project.get_program()
                    && program.get_source_file_by_path(&path).is_some()
                {
                    new_file_info.all_projects.push(project.id().0.clone());
                }
            }
            new_file_info.all_projects.sort();
            current_open_files.insert(file_name.clone(), new_file_info.clone());
            let open_file_change;
            let old_file_info;
            if let Some(existing) = self
                .state_baseline
                .as_ref()
                .expect("state baseline")
                .serialized_open_files
                .get(file_name)
            {
                if existing.default_project_name != new_file_info.default_project_name
                    || existing.all_projects != new_file_info.all_projects
                {
                    open_file_change = "*modified*";
                    files_diff_table.set_has_change();
                } else {
                    open_file_change = "";
                }
                old_file_info = Some(existing.clone());
            } else {
                open_file_change = "*new*";
                files_diff_table.set_has_change();
                old_file_info = None;
            }

            let file_name_str = file_name.as_string().to_string();
            let open_file_change = open_file_change.to_string();
            let new_file_info_for_diff = new_file_info.clone();
            let options_for_diff = options.clone();
            files_diff_table.add(file_name_str.clone(), move |w| {
                let _ = write!(w, "  [{file_name_str}] {open_file_change}\n");
                let old_file_info = old_file_info.clone();
                print_slices_with_diff_table(
                    w,
                    "",
                    &new_file_info_for_diff.all_projects,
                    move || {
                        old_file_info
                            .as_ref()
                            .map(|o| o.all_projects.clone())
                            .unwrap_or_default()
                    },
                    &options_for_diff,
                    &open_file_change,
                    Some(&|project_name: &str| {
                        project_name == new_file_info_for_diff.default_project_name
                    }),
                );
            });
        }
        let serialized_file_names: Vec<RootedFilePath> = self
            .state_baseline
            .as_ref()
            .expect("state baseline")
            .serialized_open_files
            .keys()
            .cloned()
            .collect();
        for file_name in serialized_file_names {
            if !current_open_files.contains_key(&file_name) {
                files_diff_table.set_has_change();
                let file_name_str = file_name.as_string().to_string();
                files_diff_table.add(file_name_str.clone(), move |w| {
                    let _ = write!(w, "  [{file_name_str}] *closed*\n");
                });
            }
        }
        self.state_baseline
            .as_mut()
            .expect("state baseline")
            .serialized_open_files = current_open_files;
        files_diff_table.print(w);
    }
}

/// `*project.TestConfigEntry` snapshotted eagerly — the iter.Seq fields
/// become sorted `Vec<String>` (`string(path)`/`string(id)` conversions
/// folded in, mirroring `sliceFromIterSeqString`).
#[derive(Clone)]
struct OwnedConfigEntry {
    file_name: RootedFilePath,
    retaining_projects: Vec<String>,
    retaining_open_files: Vec<String>,
    retaining_configs: Vec<String>,
}

fn owned_config_entry(entry: TestConfigEntry<'_>) -> OwnedConfigEntry {
    OwnedConfigEntry {
        file_name: entry.file_name,
        retaining_projects: entry.retaining_projects.map(|id| id.0.clone()).collect(),
        retaining_open_files: entry
            .retaining_open_files
            .map(|p| p.as_string().to_string())
            .collect(),
        retaining_configs: entry
            .retaining_configs
            .map(|p| p.as_string().to_string())
            .collect(),
    }
}

impl FourslashTest {
    /// `printConfigFileRegistryDiff`.
    fn print_config_file_registry_diff(&mut self, snapshot: &Snapshot, w: &mut dyn io::Write) {
        let config_file_registry = snapshot.project_collection.config_file_registry();

        let mut config_diffs_table = DiffTableWriter::new("Config");
        let mut config_file_names_diffs_table = DiffTableWriter::new("Config File Names");

        // `serializedConfigFileRegistry == configFileRegistry` — Go pointer
        // equality; the port compares registry addresses (see RegistrySnapshot).
        let current_addr = config_file_registry.map(|r| r as *const ConfigFileRegistry as usize);
        let serialized_addr = self
            .state_baseline
            .as_ref()
            .expect("state baseline")
            .serialized_config_file_registry
            .as_ref()
            .map(|s| s.source_addr);
        if current_addr.is_some() && current_addr == serialized_addr {
            return;
        }
        let options = DiffTableOptions {
            indent: "    ".to_string(),
            sort_keys: true,
        };
        let serialized_registry = self
            .state_baseline
            .as_ref()
            .expect("state baseline")
            .serialized_config_file_registry
            .as_ref();

        if let Some(registry) = config_file_registry {
            registry.for_each_test_config_entry(|path, entry| {
                let entry = owned_config_entry(entry);
                let mut config_change = "";
                let old_entry = serialized_registry
                    .and_then(|s| s.registry.get_test_config_entry(path))
                    .map(owned_config_entry);
                if old_entry.is_none() {
                    config_change = "*new*";
                    config_diffs_table.set_has_change();
                } else {
                    // NOTE: `oldEntry != entry` is always true in Go (both are
                    // fresh pointers), so only the seq equality check applies.
                    let old = old_entry.as_ref().unwrap();
                    if !are_iter_seq_equal(&old.retaining_projects, &entry.retaining_projects)
                        || !are_iter_seq_equal(
                            &old.retaining_open_files,
                            &entry.retaining_open_files,
                        )
                        || !are_iter_seq_equal(&old.retaining_configs, &entry.retaining_configs)
                    {
                        config_change = "*modified*";
                        config_diffs_table.set_has_change();
                    }
                }
                let config_change = config_change.to_string();
                let options_for_diff = options.clone();
                config_diffs_table.add(path.as_string().to_string(), move |w| {
                    let _ = write!(
                        w,
                        "  [{}] {}\n",
                        entry.file_name.as_string(),
                        config_change
                    );
                    // Print the details of the config entry
                    let mut retaining_projects_modified = "";
                    let mut retaining_open_files_modified = "";
                    let mut retaining_configs_modified = "";
                    if config_change == "*modified*" {
                        let old = old_entry.as_ref().unwrap();
                        if !are_iter_seq_equal(&entry.retaining_projects, &old.retaining_projects)
                        {
                            retaining_projects_modified = " *modified*";
                        }
                        if !are_iter_seq_equal(
                            &entry.retaining_open_files,
                            &old.retaining_open_files,
                        ) {
                            retaining_open_files_modified = " *modified*";
                        }
                        if !are_iter_seq_equal(&entry.retaining_configs, &old.retaining_configs)
                        {
                            retaining_configs_modified = " *modified*";
                        }
                    }
                    let old_for_projects = old_entry.clone();
                    let old_for_files = old_entry.clone();
                    let old_for_configs = old_entry.clone();
                    print_string_iter_seq_with_diff_table(
                        w,
                        &format!("RetainingProjects:{retaining_projects_modified}"),
                        &entry.retaining_projects,
                        move || {
                            old_for_projects
                                .as_ref()
                                .map(|o| o.retaining_projects.clone())
                                .unwrap_or_default()
                        },
                        &options_for_diff,
                        &config_change,
                    );
                    print_string_iter_seq_with_diff_table(
                        w,
                        &format!("RetainingOpenFiles:{retaining_open_files_modified}"),
                        &entry.retaining_open_files,
                        move || {
                            old_for_files
                                .as_ref()
                                .map(|o| o.retaining_open_files.clone())
                                .unwrap_or_default()
                        },
                        &options_for_diff,
                        &config_change,
                    );
                    print_string_iter_seq_with_diff_table(
                        w,
                        &format!("RetainingConfigs:{retaining_configs_modified}"),
                        &entry.retaining_configs,
                        move || {
                            old_for_configs
                                .as_ref()
                                .map(|o| o.retaining_configs.clone())
                                .unwrap_or_default()
                        },
                        &options_for_diff,
                        &config_change,
                    );
                });
            });
        }

        if let Some(registry) = config_file_registry {
            registry.for_each_test_config_file_names_entry(|path, entry| {
                let mut config_file_names_change = "";
                let old_entry = serialized_registry
                    .and_then(|s| s.registry.get_test_config_file_names_entry(path));
                if old_entry.is_none() {
                    config_file_names_change = "*new*";
                    config_file_names_diffs_table.set_has_change();
                } else {
                    let old = old_entry.as_ref().unwrap();
                    if old.nearest_config_file_name != entry.nearest_config_file_name
                        || old.ancestors != entry.ancestors
                    {
                        config_file_names_change = "*modified*";
                        config_file_names_diffs_table.set_has_change();
                    }
                }
                let config_file_names_change = config_file_names_change.to_string();
                let path_str = path.as_string().to_string();
                let entry = entry.clone();
                let options_for_diff = options.clone();
                config_file_names_diffs_table.add(path_str.clone(), move |w| {
                    let _ = write!(w, "  [{path_str}] {config_file_names_change}\n");
                    let mut nearest_config_file_name_modified = "";
                    let mut ancestor_diff_modified = "";
                    if config_file_names_change == "*modified*" {
                        let old = old_entry.as_ref().unwrap();
                        if old.nearest_config_file_name != entry.nearest_config_file_name {
                            nearest_config_file_name_modified = " *modified*";
                        }
                        if old.ancestors != entry.ancestors {
                            ancestor_diff_modified = " *modified*";
                        }
                    }
                    let _ = write!(
                        w,
                        "    NearestConfigFileName: {}{}\n",
                        entry.nearest_config_file_name.as_string(),
                        nearest_config_file_name_modified
                    );
                    let mut ancestor_diff = DiffTable::new(options_for_diff.clone());
                    for (config, ancestor_of_config) in &entry.ancestors {
                        let mut ancestor_change = "";
                        if config_file_names_change == "*modified*" {
                            let old = old_entry.as_ref().unwrap();
                            match old.ancestors.get(config) {
                                Some(old_config_file_name) => {
                                    if *old_config_file_name != *ancestor_of_config {
                                        ancestor_change = "*modified*";
                                    }
                                }
                                None => ancestor_change = "*new*",
                            }
                        }
                        ancestor_diff.add(
                            config.as_string().to_string(),
                            format!(
                                "{} {}",
                                ancestor_of_config.as_string(),
                                ancestor_change
                            ),
                        );
                    }
                    if config_file_names_change == "*modified*" {
                        let old = old_entry.as_ref().unwrap();
                        for (ancestor_path, old_config_file_name) in &old.ancestors {
                            if !entry.ancestors.contains_key(ancestor_path) {
                                ancestor_diff.add(
                                    ancestor_path.as_string().to_string(),
                                    format!(
                                        "{} *deleted*",
                                        old_config_file_name.as_string()
                                    ),
                                );
                            }
                        }
                    }
                    ancestor_diff.print(w, &format!("Ancestors:{ancestor_diff_modified}"));
                });
            });
        }

        if let Some(serialized) = serialized_registry {
            serialized.registry.for_each_test_config_entry(|path, entry| {
                if config_file_registry
                    .and_then(|r| r.get_test_config_entry(path))
                    .is_none()
                {
                    config_diffs_table.set_has_change();
                    let entry_file_name = entry.file_name.as_string().to_string();
                    config_diffs_table.add(path.as_string().to_string(), move |w| {
                        let _ = write!(w, "  [{entry_file_name}] *deleted*\n");
                    });
                }
            });
            serialized
                .registry
                .for_each_test_config_file_names_entry(|path, _entry| {
                    if config_file_registry
                        .and_then(|r| r.get_test_config_file_names_entry(path))
                        .is_none()
                    {
                        config_file_names_diffs_table.set_has_change();
                        let path_str = path.as_string().to_string();
                        config_file_names_diffs_table.add(path_str.clone(), move |w| {
                            let _ = write!(w, "  [{path_str}] *deleted*\n");
                        });
                    }
                });
        }
        self.state_baseline
            .as_mut()
            .expect("state baseline")
            .serialized_config_file_registry =
            config_file_registry.map(|registry| RegistrySnapshot {
                source_addr: registry as *const ConfigFileRegistry as usize,
                registry: registry.clone(),
            });
        config_diffs_table.print(w);
        config_file_names_diffs_table.print(w);
    }
}
