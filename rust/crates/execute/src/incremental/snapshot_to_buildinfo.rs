// Ported from tsc/internal/execute/incremental/snapshottobuildinfo.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::{RepopulateDiagnosticInfo, lock_diagnostic};
use tsc_ast::ids::NodeId;
use tsc_ast::utilities::is_json_source_file;
use tsc_collections::OrderedMap;
use tsc_compiler::program::Program as CompilerProgram;
use tsc_core::version::version as core_version;
use tsc_tsoptions::commandlineoption::{CommandLineOptionKind, CommandLineOptionRef};
use tsc_tsoptions::generated::options::for_each_compiler_option_affecting_build_info;
use tsc_tsoptions::value::Value;
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath,
    ensure_path_is_non_module_name, get_relative_path_from_directory, rooted_file_path_from_path,
};

use crate::incremental::build_info::{
    BuildInfo, BuildInfoDiagnostic, BuildInfoDiagnosticsOfFile, BuildInfoEmitSignature,
    BuildInfoFileId, BuildInfoFileIdListId, BuildInfoFilePendingEmit, BuildInfoPath,
    BuildInfoReferenceMapEntry, BuildInfoRepopulateInfo, BuildInfoResolvedRoot, BuildInfoRoot,
    BuildInfoSemanticDiagnostic, content_mapper_identities, new_build_info_file_info,
};
use crate::incremental::snapshot::{
    BuildInfoDiagnosticWithFileName, DiagnosticsOrBuildInfoDiagnosticsWithFileName, Snapshot,
    get_file_emit_kind,
};

/// `func snapshotToBuildInfo`.
pub(crate) fn snapshot_to_build_info(
    snapshot: &Rc<Snapshot>,
    program: &CompilerProgram,
    build_info_file_name: &RootedFilePath,
) -> Result<BuildInfo, tsc_contentmapper::host::Error> {
    let content_mapper_identities =
        content_mapper_identities(program.content_mapper_project().as_ref())?;
    let build_info = BuildInfo {
        version: core_version().to_string(),
        content_mapper_identities,
        ..Default::default()
    };
    let mut to = ToBuildInfo {
        snapshot,
        program,
        build_info,
        build_info_directory: build_info_file_name.directory(),
        case_sensitivity: program.case_sensitivity(),
        file_name_to_file_id: FxHashMap::default(),
        file_names_to_file_id_list_id: FxHashMap::default(),
        roots: FxHashMap::default(),
    };

    if snapshot.options.is_incremental() {
        to.collect_root_files();
        to.set_file_info_and_emit_signatures();
        to.set_root_of_incremental_program();
        to.set_compiler_options();
        to.set_referenced_map();
        to.set_change_file_set();
        to.set_semantic_diagnostics();
        to.set_emit_diagnostics();
        to.set_affected_files_pending_emit();
        let latest = to.snapshot.latest_changed_dts_file.borrow().clone();
        if !latest.as_string().is_empty() {
            to.build_info.latest_changed_dts_file = to.file_name_relative_to_build_info(&latest);
        }
    } else {
        to.set_root_of_non_incremental_program();
    }
    to.build_info.errors = to.snapshot.has_errors.get().is_true();
    to.build_info.semantic_errors = to.snapshot.has_semantic_errors.get();
    to.build_info.check_pending = to.snapshot.check_pending.get();
    to.set_package_jsons();
    Ok(to.build_info)
}

/// `type toBuildInfo struct`.
struct ToBuildInfo<'a> {
    snapshot: &'a Snapshot,
    program: &'a CompilerProgram,
    build_info: BuildInfo,
    build_info_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    file_name_to_file_id: FxHashMap<PathKey, BuildInfoFileId>,
    file_names_to_file_id_list_id: FxHashMap<String, BuildInfoFileIdListId>,
    /// Go `map[*ast.SourceFile]PathKey` — `NodeId` is the port's file identity.
    roots: FxHashMap<NodeId, PathKey>,
}

impl ToBuildInfo<'_> {
    /// `(*toBuildInfo) relativeToBuildInfo`.
    fn relative_to_build_info(&self, path: &RootedPath) -> String {
        if let Some(relative_path) = self.case_sensitivity.relative_path_from_directory(
            &self.build_info_directory,
            &rooted_file_path_from_path(path.clone()),
        ) {
            return relative_path.as_module_specifier().as_string().to_string();
        }
        path.as_string().to_string()
    }

    /// `(*toBuildInfo) fileNameRelativeToBuildInfo`.
    fn file_name_relative_to_build_info(&self, path: &RootedFilePath) -> BuildInfoPath {
        if let Some(relative_path) = self
            .case_sensitivity
            .relative_path_from_directory(&self.build_info_directory, path)
        {
            return BuildInfoPath(relative_path.as_module_specifier().as_string().to_string());
        }
        BuildInfoPath(path.as_string().to_string())
    }

    /// `(*toBuildInfo) serializedPathKeyRelativeToBuildInfo`.
    fn serialized_path_key_relative_to_build_info(&self, path: &PathKey) -> BuildInfoPath {
        BuildInfoPath(
            ensure_path_is_non_module_name(&get_relative_path_from_directory(
                self.build_info_directory.as_string(),
                path.as_string(),
                self.case_sensitivity,
            ))
            .into_owned(),
        )
    }

    /// `(*toBuildInfo) toFileId`.
    fn to_file_id(&mut self, path: &PathKey) -> BuildInfoFileId {
        if let Some(&file_id) = self.file_name_to_file_id.get(path) {
            return file_id;
        }
        if let Some(lib_file) = self.program.get_default_lib_file(path) {
            if !lib_file.replaced {
                self.build_info
                    .file_names
                    .push(BuildInfoPath(lib_file.name.clone()));
            } else {
                self.build_info
                    .file_names
                    .push(self.serialized_path_key_relative_to_build_info(path));
            }
        } else {
            self.build_info
                .file_names
                .push(self.serialized_path_key_relative_to_build_info(path));
        }
        let file_id = self.build_info.file_names.len() as BuildInfoFileId;
        self.file_name_to_file_id.insert(path.clone(), file_id);
        file_id
    }

    /// `(*toBuildInfo) toFileIdListId`.
    fn to_file_id_list_id(&mut self, set: &tsc_collections::Set<PathKey>) -> BuildInfoFileIdListId {
        let mut file_ids: Vec<BuildInfoFileId> = set
            .keys()
            .iter()
            .map(|path| self.to_file_id(path))
            .collect();
        file_ids.sort();
        let key = file_ids
            .iter()
            .map(|id| id.to_string())
            .collect::<Vec<_>>()
            .join(",");

        if let Some(&file_id_list_id) = self.file_names_to_file_id_list_id.get(&key) {
            return file_id_list_id;
        }
        self.build_info.file_ids_list.push(file_ids);
        let file_id_list_id = self.build_info.file_ids_list.len() as BuildInfoFileIdListId;
        self.file_names_to_file_id_list_id
            .insert(key, file_id_list_id);
        file_id_list_id
    }

    /// `(*toBuildInfo) toRelativeToBuildInfoCompilerOptionValue`.
    fn to_relative_to_build_info_compiler_option_value(
        &self,
        option: CommandLineOptionRef,
        v: Value,
    ) -> Value {
        if option.kind == CommandLineOptionKind::List {
            if option
                .elements()
                .is_some_and(|element| element.path_kind.is_rooted())
            {
                match v {
                    Value::FilePathList(paths) => {
                        return Value::StringList(
                            paths
                                .iter()
                                .map(|path| self.relative_to_build_info(&path.as_path()))
                                .collect(),
                        );
                    }
                    Value::DirPathList(paths) => {
                        return Value::StringList(
                            paths
                                .iter()
                                .map(|path| self.relative_to_build_info(&path.as_path()))
                                .collect(),
                        );
                    }
                    _ => {}
                }
            }
        } else if option.path_kind.is_rooted() {
            match v {
                Value::FilePath(path) => {
                    if !path.as_string().is_empty() {
                        return Value::Str(self.relative_to_build_info(&path.as_path()));
                    }
                    return Value::FilePath(path);
                }
                Value::DirPath(path) => {
                    if !path.as_string().is_empty() {
                        return Value::Str(self.relative_to_build_info(&path.as_path()));
                    }
                    return Value::DirPath(path);
                }
                Value::RootedPath(path) => {
                    if !path.as_string().is_empty() {
                        return Value::Str(self.relative_to_build_info(&path));
                    }
                    return Value::RootedPath(path);
                }
                _ => {}
            }
        }
        v
    }

    /// `(*toBuildInfo) toBuildInfoDiagnosticsFromFileNameDiagnostics`.
    fn to_build_info_diagnostics_from_file_name_diagnostics(
        &mut self,
        diagnostics: &[BuildInfoDiagnosticWithFileName],
    ) -> Vec<BuildInfoDiagnostic> {
        diagnostics
            .iter()
            .map(|d| {
                let file = if !d.file.as_string().is_empty() {
                    self.to_file_id(&d.file.clone())
                } else {
                    0
                };
                BuildInfoDiagnostic {
                    file,
                    no_file: d.no_file,
                    pos: d.pos,
                    end: d.end,
                    code: d.code,
                    category: d.category,
                    source: d.source.clone(),
                    message_text: d.message_text.clone(),
                    message_key: d.message_key.to_string(),
                    message_args: d.message_args.clone(),
                    message_chain: self
                        .to_build_info_diagnostics_from_file_name_diagnostics(&d.message_chain),
                    related_information: self.to_build_info_diagnostics_from_file_name_diagnostics(
                        &d.related_information,
                    ),
                    reports_unnecessary: d.reports_unnecessary,
                    reports_deprecated: d.reports_deprecated,
                    skipped_on_no_emit: d.skipped_on_no_emit,
                    repopulate_info: to_build_info_repopulate_info(d.repopulate_info.as_ref()),
                }
            })
            .collect()
    }

    /// `(*toBuildInfo) toBuildInfoDiagnosticsFromDiagnostics`.
    fn to_build_info_diagnostics_from_diagnostics(
        &mut self,
        file_path: &PathKey,
        diagnostics: &[tsc_ast::diagnostic::DiagnosticRef],
    ) -> Vec<BuildInfoDiagnostic> {
        diagnostics
            .iter()
            .map(|d| {
                let d = lock_diagnostic(d);
                let mut file = 0;
                let mut no_file = false;
                match d.file() {
                    None => no_file = true,
                    Some(diagnostic_file) => {
                        if diagnostic_file.path_key != *file_path {
                            file = self.to_file_id(&diagnostic_file.path_key.clone());
                        }
                    }
                }
                BuildInfoDiagnostic {
                    file,
                    no_file,
                    pos: d.loc().pos(),
                    end: d.loc().end(),
                    code: d.code(),
                    category: d.category(),
                    source: d.source().to_string(),
                    message_text: d.message_text().to_string(),
                    message_key: d.message_key().to_string(),
                    message_args: d.message_args().to_vec(),
                    // PORT: `d` is locked while converting nested chains —
                    // recursion into `message_chain` locks other diagnostics,
                    // never the same one, so no self-deadlock is possible.
                    message_chain: self
                        .to_build_info_diagnostics_from_diagnostics(file_path, d.message_chain()),
                    related_information: self.to_build_info_diagnostics_from_diagnostics(
                        file_path,
                        d.related_information(),
                    ),
                    reports_unnecessary: d.reports_unnecessary(),
                    reports_deprecated: d.reports_deprecated(),
                    skipped_on_no_emit: d.skipped_on_no_emit(),
                    repopulate_info: to_build_info_repopulate_info(d.repopulate_info()),
                }
            })
            .collect()
    }

    /// `(*toBuildInfo) toBuildInfoDiagnosticsOfFile`.
    fn to_build_info_diagnostics_of_file(
        &mut self,
        file_path: &PathKey,
        diags: &Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>>,
    ) -> Option<BuildInfoDiagnosticsOfFile> {
        let diags = diags.borrow();
        if let Some(diagnostics) = &diags.diagnostics {
            if !diagnostics.is_empty() {
                return Some(BuildInfoDiagnosticsOfFile {
                    file_id: self.to_file_id(file_path),
                    diagnostics: self
                        .to_build_info_diagnostics_from_diagnostics(file_path, diagnostics),
                });
            }
        }
        if !diags.build_info_diagnostics.is_empty() {
            return Some(BuildInfoDiagnosticsOfFile {
                file_id: self.to_file_id(file_path),
                diagnostics: self.to_build_info_diagnostics_from_file_name_diagnostics(
                    &diags.build_info_diagnostics,
                ),
            });
        }
        None
    }

    /// `(*toBuildInfo) collectRootFiles`.
    fn collect_root_files(&mut self) {
        for file_name in self.program.command_line().file_names() {
            let file = {
                let redirect = self.program.get_parse_file_redirect(file_name);
                if !redirect.as_string().is_empty() {
                    self.program.get_source_file(&redirect)
                } else {
                    self.program.get_source_file(file_name)
                }
            };
            if let Some(file) = file {
                self.roots
                    .insert(file, self.case_sensitivity.path_key(&file_name.as_path()));
            }
        }
    }

    /// `(*toBuildInfo) setFileInfoAndEmitSignatures`.
    fn set_file_info_and_emit_signatures(&mut self) {
        let files = self.program.source_files_slice();
        let mut file_infos = Vec::with_capacity(files.len());
        for &file in files {
            let (file_path_key, file_is_json) = {
                let nodes = self.program.arena_of(file);
                let sf = nodes[file].as_source_file();
                (sf.path_key().clone(), is_json_source_file(sf))
            };
            let info = self
                .snapshot
                .file_infos
                .load(&file_path_key)
                .expect("file info");
            let file_id = self.to_file_id(&file_path_key);
            if self.build_info.file_names[file_id as usize - 1]
                != self.serialized_path_key_relative_to_build_info(&file_path_key)
            {
                let is_valid_lib = self
                    .program
                    .get_default_lib_file(&file_path_key)
                    .is_some_and(|lib_file| {
                        !lib_file.replaced
                            && self.build_info.file_names[file_id as usize - 1].as_string()
                                == lib_file.name
                    });
                if !is_valid_lib {
                    panic!(
                        "File name at index {} does not match expected relative path or libName: {} != {}",
                        file_id - 1,
                        self.build_info.file_names[file_id as usize - 1].as_string(),
                        self.serialized_path_key_relative_to_build_info(&file_path_key)
                            .as_string()
                    );
                }
            }
            if self.snapshot.options.composite.is_true()
                && !file_is_json
                && self.program.source_file_may_be_emitted_for(file, false)
            {
                match self.snapshot.emit_signatures.load(&file_path_key) {
                    None => {
                        self.build_info
                            .emit_signatures
                            .push(BuildInfoEmitSignature {
                                file_id,
                                ..Default::default()
                            });
                    }
                    Some(emit_signature) => {
                        let info_signature = info.borrow().signature.clone();
                        if emit_signature.signature != info_signature {
                            let mut incremental_emit_signature = BuildInfoEmitSignature {
                                file_id,
                                ..Default::default()
                            };
                            if !emit_signature.signature.is_empty() {
                                incremental_emit_signature.signature =
                                    emit_signature.signature.clone();
                            } else if emit_signature
                                .signature_with_different_options
                                .as_ref()
                                .expect("signatureWithDifferentOptions")[0]
                                == info_signature
                            {
                                incremental_emit_signature.differs_only_in_dts_map = true;
                            } else {
                                incremental_emit_signature.signature = emit_signature
                                    .signature_with_different_options
                                    .as_ref()
                                    .expect("signatureWithDifferentOptions")[0]
                                    .clone();
                                incremental_emit_signature.differs_in_options = true;
                            }
                            self.build_info
                                .emit_signatures
                                .push(incremental_emit_signature);
                        }
                    }
                }
            }
            file_infos.push(Some(new_build_info_file_info(&info.borrow())));
        }
        self.build_info.file_infos = file_infos;
    }

    /// `(*toBuildInfo) setRootOfIncrementalProgram`.
    fn set_root_of_incremental_program(&mut self) {
        // PORT: Go sorts roots with `slices.SortFunc` whose comparator calls
        // `toFileId`, assigning ids in comparison order. `sort_by_cached_key`
        // assigns each id once in map order — a different but equally valid
        // internal numbering; ids need only be consistent within one
        // serialized buildInfo.
        let mut keys: Vec<NodeId> = self.roots.keys().copied().collect();
        keys.sort_by_cached_key(|file| {
            let path_key = {
                let nodes = self.program.arena_of(*file);
                nodes[*file].as_source_file().path_key().clone()
            };
            self.to_file_id(&path_key)
        });
        for file in keys {
            let root = self.to_file_id(&self.roots[&file].clone());
            let resolved = {
                let nodes = self.program.arena_of(file);
                let path_key = nodes[file].as_source_file().path_key().clone();
                self.to_file_id(&path_key)
            };
            match self.build_info.root.last_mut() {
                None => {
                    // First fileId as is.
                    self.build_info.root.push(BuildInfoRoot {
                        start: resolved,
                        ..Default::default()
                    });
                }
                Some(last) => {
                    if last.end == resolved - 1 || (last.end == 0 && last.start == resolved - 1) {
                        // Extend [start, fileId - 1] or [fileId - 1] to
                        // include fileId.
                        last.end = resolved;
                    } else {
                        self.build_info.root.push(BuildInfoRoot {
                            start: resolved,
                            ..Default::default()
                        });
                    }
                }
            }
            if root != resolved {
                self.build_info
                    .resolved_root
                    .push(BuildInfoResolvedRoot { resolved, root });
            }
        }
    }

    /// `(*toBuildInfo) setCompilerOptions`.
    fn set_compiler_options(&mut self) {
        for_each_compiler_option_affecting_build_info(
            &self.snapshot.options,
            &mut |option, value| {
                // Make it relative to buildInfo directory if it is a file path.
                if let Some(option) = option {
                    let value = self.to_relative_to_build_info_compiler_option_value(option, value);
                    self.build_info
                        .options
                        .get_or_insert_with(OrderedMap::new)
                        .set(option.name.to_string(), value);
                } else {
                    // PORT(deferred): Go's generated table always supplies a
                    // non-nil option; `None` means the generated lookup missed,
                    // which cannot happen for the shipped option set.
                    let _ = value;
                }
            },
        );
    }

    /// `(*toBuildInfo) setReferencedMap`.
    fn set_referenced_map(&mut self) {
        let mut keys = self.snapshot.referenced_map.get_paths_with_references();
        keys.sort();
        self.build_info.referenced_map = keys
            .iter()
            .map(|file_path| {
                let references = self
                    .snapshot
                    .referenced_map
                    .get_references(file_path)
                    .expect("references");
                BuildInfoReferenceMapEntry {
                    file_id: self.to_file_id(file_path),
                    file_id_list_id: self.to_file_id_list_id(&references),
                }
            })
            .collect();
    }

    /// `(*toBuildInfo) setChangeFileSet`.
    fn set_change_file_set(&mut self) {
        let mut files: Vec<PathKey> = self.snapshot.changed_files_set.to_slice();
        files.sort();
        self.build_info.change_file_set = files.iter().map(|file| self.to_file_id(file)).collect();
    }

    /// `(*toBuildInfo) setSemanticDiagnostics`.
    fn set_semantic_diagnostics(&mut self) {
        for &file in self.program.source_files_slice() {
            let path_key = {
                let nodes = self.program.arena_of(file);
                nodes[file].as_source_file().path_key().clone()
            };
            match self.snapshot.semantic_diagnostics_per_file.load(&path_key) {
                None => {
                    if !self.snapshot.changed_files_set.has(&path_key) {
                        let file_id = self.to_file_id(&path_key);
                        self.build_info.semantic_diagnostics_per_file.push(
                            BuildInfoSemanticDiagnostic {
                                file_id,
                                diagnostics: None,
                            },
                        );
                    }
                }
                Some(value) => {
                    if let Some(diagnostics) =
                        self.to_build_info_diagnostics_of_file(&path_key, &value)
                    {
                        self.build_info.semantic_diagnostics_per_file.push(
                            BuildInfoSemanticDiagnostic {
                                file_id: 0,
                                diagnostics: Some(Box::new(diagnostics)),
                            },
                        );
                    }
                }
            }
        }
    }

    /// `(*toBuildInfo) setEmitDiagnostics`.
    fn set_emit_diagnostics(&mut self) {
        let mut files: Vec<PathKey> = self.snapshot.emit_diagnostics_per_file.keys();
        files.sort();
        self.build_info.emit_diagnostics_per_file = files
            .iter()
            .filter_map(|file_path| {
                let value = self
                    .snapshot
                    .emit_diagnostics_per_file
                    .load(file_path)
                    .expect("emit diagnostics");
                self.to_build_info_diagnostics_of_file(file_path, &value)
            })
            .collect();
    }

    /// `(*toBuildInfo) setAffectedFilesPendingEmit`.
    fn set_affected_files_pending_emit(&mut self) {
        let mut files: Vec<PathKey> = self.snapshot.affected_files_pending_emit.keys();
        files.sort();
        let full_emit_kind = get_file_emit_kind(&self.snapshot.options);
        for file_path in files {
            let file = self.program.get_source_file_by_path(&file_path);
            if file.is_none()
                || !self
                    .program
                    .source_file_may_be_emitted_for(file.expect("checked"), false)
            {
                continue;
            }
            let pending_emit = self
                .snapshot
                .affected_files_pending_emit
                .load(&file_path)
                .unwrap_or_default();
            let file_id = self.to_file_id(&file_path);
            self.build_info
                .affected_files_pending_emit
                .push(BuildInfoFilePendingEmit {
                    file_id,
                    emit_kind: if pending_emit == full_emit_kind {
                        0
                    } else {
                        pending_emit
                    },
                });
        }
    }

    /// `(*toBuildInfo) setRootOfNonIncrementalProgram`.
    fn set_root_of_non_incremental_program(&mut self) {
        self.build_info.root = self
            .program
            .command_line()
            .file_names()
            .iter()
            .map(|file_name| BuildInfoRoot {
                non_incremental: self.serialized_path_key_relative_to_build_info(
                    &self.case_sensitivity.path_key(&file_name.as_path()),
                ),
                ..Default::default()
            })
            .collect();
    }

    /// `(*toBuildInfo) setPackageJsons`.
    fn set_package_jsons(&mut self) {
        let package_jsons = self.snapshot.package_jsons.borrow().clone();
        if let Some(package_jsons) = package_jsons {
            if !package_jsons.is_empty() {
                self.build_info.package_jsons = package_jsons
                    .iter()
                    .map(|path| self.file_name_relative_to_build_info(path))
                    .collect();
            }
        }
        let missing = self.snapshot.missing_package_jsons.borrow().clone();
        if let Some(missing) = missing {
            if !missing.is_empty() {
                self.build_info.missing_package_jsons = missing
                    .iter()
                    .map(|path| self.file_name_relative_to_build_info(path))
                    .collect();
            }
        }
    }
}

/// `func toBuildInfoRepopulateInfo`.
fn to_build_info_repopulate_info(
    info: Option<&RepopulateDiagnosticInfo>,
) -> Option<BuildInfoRepopulateInfo> {
    info.map(|info| BuildInfoRepopulateInfo {
        kind: info.kind,
        module_reference: info.module_reference.clone(),
        mode: info.mode,
        package_name: info.package_name.clone(),
    })
}
