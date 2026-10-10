// Ported from tsc/internal/execute/incremental/buildinfotosnapshot.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::diagnostic::RepopulateDiagnosticInfo;
use tsc_collections::Set;
use tsc_compiler::host::CompilerHost;
use tsc_core::tristate::{TS_FALSE, TS_TRUE};
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};

use crate::incremental::build_info::{
    BuildInfo, BuildInfoDiagnostic, BuildInfoPath, BuildInfoRepopulateInfo,
    resolve_build_info_file_name,
};
use crate::incremental::snapshot::{
    BuildInfoDiagnosticWithFileName, DiagnosticsOrBuildInfoDiagnosticsWithFileName, EmitSignature,
    Snapshot, get_file_emit_kind,
};

/// `func buildInfoToSnapshot`.
pub(crate) fn build_info_to_snapshot(
    build_info: BuildInfo,
    config: &ParsedCommandLine,
    host: &Arc<dyn CompilerHost>,
) -> Rc<Snapshot> {
    let build_info_directory = config.get_build_info_file_name().directory();
    let case_sensitivity = config.case_sensitivity();
    let file_paths: Vec<PathKey> = build_info
        .file_names
        .iter()
        .map(|file_name| {
            case_sensitivity.path_key(
                &resolve_build_info_file_name(
                    file_name,
                    &build_info_directory,
                    host.default_library_path(),
                )
                .as_path(),
            )
        })
        .collect();
    let file_path_set: Vec<Rc<Set<PathKey>>> = build_info
        .file_ids_list
        .iter()
        .map(|file_id_list| {
            let mut file_set = Set::with_size_hint(file_id_list.len());
            for file_id in file_id_list {
                file_set.add(file_paths[*file_id as usize - 1].clone());
            }
            Rc::new(file_set)
        })
        .collect();
    let mut to = ToSnapshot {
        build_info,
        build_info_directory,
        snapshot: Snapshot::default(),
        file_paths,
        file_path_set,
    };
    to.set_compiler_options();
    to.set_file_info_and_emit_signatures();
    to.set_referenced_map();
    to.set_change_file_set();
    to.set_semantic_diagnostics();
    to.set_emit_diagnostics();
    to.set_affected_files_pending_emit();
    let latest_changed_dts_file = to.build_info.latest_changed_dts_file.clone();
    if !latest_changed_dts_file.as_string().is_empty() {
        *to.snapshot.latest_changed_dts_file.borrow_mut() =
            to.to_absolute_file_name(&latest_changed_dts_file);
    }
    to.snapshot.has_errors.set(if to.build_info.errors {
        TS_TRUE
    } else {
        TS_FALSE
    });
    to.snapshot
        .has_semantic_errors
        .set(to.build_info.semantic_errors);
    to.snapshot.check_pending.set(to.build_info.check_pending);
    to.set_package_jsons();
    Rc::new(to.snapshot)
}

/// `type toSnapshot struct`.
struct ToSnapshot {
    build_info: BuildInfo,
    build_info_directory: RootedDirectoryPath,
    snapshot: Snapshot,
    file_paths: Vec<PathKey>,
    file_path_set: Vec<Rc<Set<PathKey>>>,
}

impl ToSnapshot {
    /// `(*toSnapshot) toAbsoluteFileName`.
    fn to_absolute_file_name(&self, path: &BuildInfoPath) -> RootedFilePath {
        self.build_info_directory.resolve_file(path.as_string())
    }

    /// `(*toSnapshot) filePathKey`.
    fn file_path_key(&self, file_id: crate::incremental::build_info::BuildInfoFileId) -> &PathKey {
        &self.file_paths[file_id as usize - 1]
    }

    /// `(*toSnapshot) toFilePathSet`.
    fn to_file_path_set(
        &self,
        file_id_list_id: crate::incremental::build_info::BuildInfoFileIdListId,
    ) -> Rc<Set<PathKey>> {
        self.file_path_set[file_id_list_id as usize - 1].clone()
    }

    /// `(*toSnapshot) toBuildInfoDiagnosticsWithFileName`.
    fn to_build_info_diagnostics_with_file_name(
        &self,
        diagnostics: &[BuildInfoDiagnostic],
    ) -> Vec<BuildInfoDiagnosticWithFileName> {
        diagnostics
            .iter()
            .map(|d| {
                let file = if d.file != 0 {
                    self.file_path_key(d.file).clone()
                } else {
                    PathKey::default()
                };
                BuildInfoDiagnosticWithFileName {
                    file,
                    no_file: d.no_file,
                    pos: d.pos,
                    end: d.end,
                    code: d.code,
                    category: d.category,
                    source: d.source.clone(),
                    message_text: d.message_text.clone(),
                    // PORT: `diagnostics::Key` is `&'static str`; deserialized
                    // build-info keys are arbitrary strings, so intern them.
                    message_key: Box::leak(d.message_key.clone().into_boxed_str()),
                    message_args: d.message_args.clone(),
                    message_chain: self.to_build_info_diagnostics_with_file_name(&d.message_chain),
                    related_information: self
                        .to_build_info_diagnostics_with_file_name(&d.related_information),
                    reports_unnecessary: d.reports_unnecessary,
                    reports_deprecated: d.reports_deprecated,
                    skipped_on_no_emit: d.skipped_on_no_emit,
                    repopulate_info: from_build_info_repopulate_info(d.repopulate_info.as_ref()),
                }
            })
            .collect()
    }

    /// `(*toSnapshot) toDiagnosticsOrBuildInfoDiagnosticsWithFileName`.
    fn to_diagnostics_or_build_info_diagnostics_with_file_name(
        &self,
        dig: &crate::incremental::build_info::BuildInfoDiagnosticsOfFile,
    ) -> DiagnosticsOrBuildInfoDiagnosticsWithFileName {
        DiagnosticsOrBuildInfoDiagnosticsWithFileName {
            diagnostics: None,
            build_info_diagnostics: self.to_build_info_diagnostics_with_file_name(&dig.diagnostics),
        }
    }

    /// `(*toSnapshot) setCompilerOptions`.
    fn set_compiler_options(&mut self) {
        self.snapshot.options = Rc::new(
            self.build_info
                .get_compiler_options(&self.build_info_directory),
        );
    }

    /// `(*toSnapshot) setFileInfoAndEmitSignatures`.
    fn set_file_info_and_emit_signatures(&mut self) {
        let is_composite = self.snapshot.options.composite.is_true();
        for (index, build_info_file_info) in self.build_info.file_infos.iter().enumerate() {
            let path = self.file_path_key((index + 1) as i32).clone();
            let info = build_info_file_info
                .as_ref()
                .map(|info| info.get_file_info())
                .unwrap_or_default();
            let signature = info.signature.clone();
            self.snapshot
                .file_infos
                .store(path.clone(), Rc::new(RefCell::new(info)));
            // Add default emit signature as file's signature.
            if !signature.is_empty() && is_composite {
                self.snapshot.emit_signatures.store(
                    path,
                    Rc::new(EmitSignature {
                        signature,
                        signature_with_different_options: None,
                    }),
                );
            }
        }
        // Fix up emit signatures.
        for value in &self.build_info.emit_signatures {
            if value.no_emit_signature() {
                self.snapshot
                    .emit_signatures
                    .delete(self.file_path_key(value.file_id));
            } else {
                let path = self.file_path_key(value.file_id).clone();
                self.snapshot.emit_signatures.store(
                    path.clone(),
                    Rc::new(value.to_emit_signature(&path, &self.snapshot.emit_signatures)),
                );
            }
        }
    }

    /// `(*toSnapshot) setReferencedMap`.
    fn set_referenced_map(&mut self) {
        for entry in &self.build_info.referenced_map {
            self.snapshot.referenced_map.store_references(
                self.file_path_key(entry.file_id).clone(),
                Some(self.to_file_path_set(entry.file_id_list_id)),
            );
        }
    }

    /// `(*toSnapshot) setChangeFileSet`.
    fn set_change_file_set(&mut self) {
        for file_id in &self.build_info.change_file_set {
            self.snapshot
                .changed_files_set
                .add(self.file_path_key(*file_id).clone());
        }
    }

    /// `(*toSnapshot) setSemanticDiagnostics`.
    fn set_semantic_diagnostics(&mut self) {
        self.snapshot.file_infos.range(|path, _info| {
            // Initialize to have no diagnostics if it is not a changed file.
            if !self.snapshot.changed_files_set.has(&path) {
                self.snapshot.semantic_diagnostics_per_file.store(
                    path,
                    Rc::new(RefCell::new(
                        DiagnosticsOrBuildInfoDiagnosticsWithFileName::default(),
                    )),
                );
            }
            true
        });
        for diagnostic in &self.build_info.semantic_diagnostics_per_file {
            if diagnostic.file_id != 0 {
                let file_path = self.file_path_key(diagnostic.file_id).clone();
                // File does not have cached diagnostics.
                self.snapshot
                    .semantic_diagnostics_per_file
                    .delete(&file_path);
            } else if let Some(diagnostics) = &diagnostic.diagnostics {
                let file_path = self.file_path_key(diagnostics.file_id).clone();
                self.snapshot.semantic_diagnostics_per_file.store(
                    file_path,
                    Rc::new(RefCell::new(
                        self.to_diagnostics_or_build_info_diagnostics_with_file_name(diagnostics),
                    )),
                );
            }
        }
    }

    /// `(*toSnapshot) setEmitDiagnostics`.
    fn set_emit_diagnostics(&mut self) {
        for diagnostic in &self.build_info.emit_diagnostics_per_file {
            let file_path = self.file_path_key(diagnostic.file_id).clone();
            self.snapshot.emit_diagnostics_per_file.store(
                file_path,
                Rc::new(RefCell::new(
                    self.to_diagnostics_or_build_info_diagnostics_with_file_name(diagnostic),
                )),
            );
        }
    }

    /// `(*toSnapshot) setAffectedFilesPendingEmit`.
    fn set_affected_files_pending_emit(&mut self) {
        if self.build_info.affected_files_pending_emit.is_empty() {
            return;
        }
        let own_options_emit_kind = get_file_emit_kind(&self.snapshot.options);
        for pending_emit in &self.build_info.affected_files_pending_emit {
            self.snapshot.affected_files_pending_emit.store(
                self.file_path_key(pending_emit.file_id).clone(),
                if pending_emit.emit_kind == 0 {
                    own_options_emit_kind
                } else {
                    pending_emit.emit_kind
                },
            );
        }
    }

    /// `(*toSnapshot) setPackageJsons` — Go assigns non-nil slices on both
    /// branches, so the port stores `Some` unconditionally.
    fn set_package_jsons(&mut self) {
        *self.snapshot.package_jsons.borrow_mut() = Some(
            self.build_info
                .package_jsons
                .iter()
                .map(|path| self.to_absolute_file_name(path))
                .collect(),
        );
        *self.snapshot.missing_package_jsons.borrow_mut() = Some(
            self.build_info
                .missing_package_jsons
                .iter()
                .map(|path| self.to_absolute_file_name(path))
                .collect(),
        );
    }
}

/// `func fromBuildInfoRepopulateInfo`.
fn from_build_info_repopulate_info(
    info: Option<&BuildInfoRepopulateInfo>,
) -> Option<RepopulateDiagnosticInfo> {
    info.map(|info| RepopulateDiagnosticInfo {
        kind: info.kind,
        module_reference: info.module_reference.clone(),
        mode: info.mode,
        package_name: info.package_name.clone(),
    })
}
