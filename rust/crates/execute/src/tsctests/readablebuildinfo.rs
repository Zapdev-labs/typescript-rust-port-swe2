// Ported from tsc/internal/execute/tsctests/readablebuildinfo.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - The readable structs are serialize-only (the `.readable.baseline.txt`
//   output is never parsed back), so Go's `UnmarshalJSON` methods are
//   dropped; the `MarshalJSON` shapes are kept via serde impls.
// - `,omitzero` tags become `skip_serializing_if`: zero ints/false bools/
//   empty strings/empty vecs/`None` options are omitted.
// - Go's `ReferencedMap`/`AffectedFilesPendingEmit` nil checks become
//   `is_empty` checks (Rust `Vec` can't distinguish nil from empty); an
//   empty-but-non-nil Go slice would emit `{}`/`[]` where the port omits
//   the key — not exercised by any known build-info shape.
// - `diagnostics.Category` serializes as its `i32` (Go marshals the int
//   type); `diagnostics.Key`/`messageKey` is `String` here, matching
//   `BuildInfoDiagnostic`'s port choice.

use serde::{Serialize, Serializer};

use tsc_ast::diagnostic::RepopulateDiagnosticKind;
use tsc_collections::OrderedMap;
use tsc_core::compileroptions::{RESOLUTION_MODE_NONE, ResolutionMode};
use tsc_diagnostics::Category;
use tsc_tsoptions::value::Value;
use tsc_tspath::RootedDirectoryPath;

use crate::incremental::build_info::{
    BuildInfo, BuildInfoDiagnostic, BuildInfoDiagnosticsOfFile, BuildInfoEmitSignature,
    BuildInfoFileId, BuildInfoFileIdListId, BuildInfoFileInfo, BuildInfoFilePendingEmit,
    BuildInfoPath, BuildInfoRoot,
};
use crate::incremental::{
    FILE_EMIT_KIND_DTS, FILE_EMIT_KIND_DTS_EMIT, FILE_EMIT_KIND_DTS_ERRORS, FILE_EMIT_KIND_DTS_MAP,
    FILE_EMIT_KIND_JS, FILE_EMIT_KIND_JS_INLINE_MAP, FILE_EMIT_KIND_JS_MAP, FileEmitKind,
    get_file_emit_kind,
};

// omitzero helpers (shared shape with incremental/build_info.rs).

fn is_false(b: &bool) -> bool {
    !*b
}

fn is_zero(v: &i32) -> bool {
    *v == 0
}

fn is_zero_size(v: &usize) -> bool {
    *v == 0
}

fn category_is_warning(c: &Category) -> bool {
    *c == Category::Warning
}

fn serialize_category<S: Serializer>(category: &Category, s: S) -> Result<S::Ok, S::Error> {
    (*category as i32).serialize(s)
}

fn is_none_mode(mode: &ResolutionMode) -> bool {
    *mode == RESOLUTION_MODE_NONE
}

fn serialize_kind<S: Serializer>(kind: &RepopulateDiagnosticKind, s: S) -> Result<S::Ok, S::Error> {
    kind.0.serialize(s)
}

/// `type readableBuildInfo struct` — field order mirrors Go's so
/// `marshal_indent` produces the same member order.
#[derive(Serialize)]
struct ReadableBuildInfo<'a> {
    #[serde(skip)]
    build_info: &'a BuildInfo,
    #[serde(rename = "version", skip_serializing_if = "String::is_empty")]
    version: String,

    // Common between incremental and tsc -b buildinfo for non incremental programs
    #[serde(rename = "errors", skip_serializing_if = "is_false")]
    errors: bool,
    #[serde(rename = "checkPending", skip_serializing_if = "is_false")]
    check_pending: bool,
    #[serde(rename = "root", skip_serializing_if = "Vec::is_empty")]
    root: Vec<ReadableBuildInfoRoot>,
    #[serde(rename = "packageJsons", skip_serializing_if = "Vec::is_empty")]
    package_jsons: Vec<String>,
    #[serde(
        rename = "missingPackageJsons",
        skip_serializing_if = "Vec::is_empty"
    )]
    missing_package_jsons: Vec<String>,

    // IncrementalProgram info
    #[serde(rename = "fileNames", skip_serializing_if = "Vec::is_empty")]
    file_names: Vec<String>,
    #[serde(rename = "fileInfos", skip_serializing_if = "Vec::is_empty")]
    file_infos: Vec<ReadableBuildInfoFileInfo>,
    #[serde(rename = "fileIdsList", skip_serializing_if = "Vec::is_empty")]
    file_ids_list: Vec<Vec<String>>,
    #[serde(rename = "options", skip_serializing_if = "Option::is_none")]
    options: Option<OrderedMap<String, Value>>,
    #[serde(
        rename = "referencedMap",
        skip_serializing_if = "Option::is_none"
    )]
    referenced_map: Option<OrderedMap<String, Vec<String>>>,
    #[serde(
        rename = "semanticDiagnosticsPerFile",
        skip_serializing_if = "Vec::is_empty"
    )]
    semantic_diagnostics_per_file: Vec<ReadableBuildInfoSemanticDiagnostic>,
    #[serde(
        rename = "emitDiagnosticsPerFile",
        skip_serializing_if = "Vec::is_empty"
    )]
    emit_diagnostics_per_file: Vec<ReadableBuildInfoDiagnosticsOfFile>,
    /// List of changed files in the program, not the whole set of files.
    #[serde(rename = "changeFileSet", skip_serializing_if = "Vec::is_empty")]
    change_file_set: Vec<String>,
    #[serde(
        rename = "affectedFilesPendingEmit",
        skip_serializing_if = "Vec::is_empty"
    )]
    affected_files_pending_emit: Vec<ReadableBuildInfoFilePendingEmit>,
    /// Because this is only output file in the program, we dont need fileId
    /// to deduplicate name.
    #[serde(
        rename = "latestChangedDtsFile",
        skip_serializing_if = "String::is_empty"
    )]
    latest_changed_dts_file: String,
    #[serde(
        rename = "emitSignatures",
        skip_serializing_if = "Vec::is_empty"
    )]
    emit_signatures: Vec<ReadableBuildInfoEmitSignature>,
    #[serde(rename = "resolvedRoot", skip_serializing_if = "Vec::is_empty")]
    resolved_root: Vec<ReadableBuildInfoResolvedRoot>,
    /// Size of the build info file.
    #[serde(rename = "size", skip_serializing_if = "is_zero_size")]
    size: usize,

    // NonIncrementalProgram info
    #[serde(rename = "semanticErrors", skip_serializing_if = "is_false")]
    semantic_errors: bool,
}

/// `type readableBuildInfoRoot struct`.
#[derive(Serialize)]
struct ReadableBuildInfoRoot {
    #[serde(rename = "files", skip_serializing_if = "Vec::is_empty")]
    files: Vec<String>,
    #[serde(rename = "original", skip_serializing_if = "Option::is_none")]
    original: Option<BuildInfoRoot>,
}

/// `type readableBuildInfoFileInfo struct`.
#[derive(Serialize)]
struct ReadableBuildInfoFileInfo {
    #[serde(rename = "fileName", skip_serializing_if = "String::is_empty")]
    file_name: String,
    #[serde(rename = "version", skip_serializing_if = "String::is_empty")]
    version: String,
    #[serde(rename = "signature", skip_serializing_if = "String::is_empty")]
    signature: String,
    #[serde(
        rename = "affectsGlobalScope",
        skip_serializing_if = "is_false"
    )]
    affects_global_scope: bool,
    #[serde(
        rename = "impliedNodeFormat",
        skip_serializing_if = "String::is_empty"
    )]
    implied_node_format: String,
    /// Original file path, if available.
    #[serde(rename = "original", skip_serializing_if = "Option::is_none")]
    original: Option<BuildInfoFileInfo>,
}

/// `type readableBuildInfoDiagnostic struct`.
#[derive(Serialize)]
struct ReadableBuildInfoDiagnostic {
    /// incrementalBuildInfoFileId if it is for a File thats other than its
    /// stored for.
    #[serde(rename = "file", skip_serializing_if = "String::is_empty")]
    file: String,
    #[serde(rename = "noFile", skip_serializing_if = "is_false")]
    no_file: bool,
    #[serde(rename = "pos", skip_serializing_if = "is_zero")]
    pos: i32,
    #[serde(rename = "end", skip_serializing_if = "is_zero")]
    end: i32,
    #[serde(rename = "code", skip_serializing_if = "is_zero")]
    code: i32,
    #[serde(
        rename = "category",
        skip_serializing_if = "category_is_warning",
        serialize_with = "serialize_category"
    )]
    category: Category,
    #[serde(rename = "messageKey", skip_serializing_if = "String::is_empty")]
    message_key: String,
    #[serde(
        rename = "messageArgs",
        skip_serializing_if = "Vec::is_empty"
    )]
    message_args: Vec<String>,
    #[serde(
        rename = "messageChain",
        skip_serializing_if = "Vec::is_empty"
    )]
    message_chain: Vec<ReadableBuildInfoDiagnostic>,
    #[serde(
        rename = "relatedInformation",
        skip_serializing_if = "Vec::is_empty"
    )]
    related_information: Vec<ReadableBuildInfoDiagnostic>,
    #[serde(
        rename = "reportsUnnecessary",
        skip_serializing_if = "is_false"
    )]
    reports_unnecessary: bool,
    #[serde(
        rename = "reportsDeprecated",
        skip_serializing_if = "is_false"
    )]
    reports_deprecated: bool,
    #[serde(
        rename = "skippedOnNoEmit",
        skip_serializing_if = "is_false"
    )]
    skipped_on_no_emit: bool,
    #[serde(
        rename = "repopulateInfo",
        skip_serializing_if = "Option::is_none"
    )]
    repopulate_info: Option<ReadableBuildInfoRepopulateInfo>,
}

/// `type readableBuildInfoRepopulateInfo struct`.
#[derive(Serialize)]
struct ReadableBuildInfoRepopulateInfo {
    #[serde(rename = "kind", serialize_with = "serialize_kind")]
    kind: RepopulateDiagnosticKind,
    #[serde(
        rename = "moduleReference",
        skip_serializing_if = "String::is_empty"
    )]
    module_reference: String,
    #[serde(rename = "mode", skip_serializing_if = "is_none_mode")]
    mode: ResolutionMode,
    #[serde(rename = "packageName", skip_serializing_if = "String::is_empty")]
    package_name: String,
}

/// `type readableBuildInfoDiagnosticsOfFile struct` — marshals
/// `[file, diagnostics]`.
struct ReadableBuildInfoDiagnosticsOfFile {
    file: String,
    diagnostics: Vec<ReadableBuildInfoDiagnostic>,
}

impl Serialize for ReadableBuildInfoDiagnosticsOfFile {
    /// `(*readableBuildInfoDiagnosticsOfFile) MarshalJSON` —
    /// `[]any{file, diagnostics}`.
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.file, &self.diagnostics).serialize(s)
    }
}

/// `type readableBuildInfoSemanticDiagnostic struct` — a bare file name or
/// a `[file, diagnostics]` pair.
struct ReadableBuildInfoSemanticDiagnostic {
    /// File is not in changedSet and still doesnt have cached diagnostics.
    file: String,
    /// Diagnostics for file.
    diagnostics: Option<Box<ReadableBuildInfoDiagnosticsOfFile>>,
}

impl Serialize for ReadableBuildInfoSemanticDiagnostic {
    /// `(*readableBuildInfoSemanticDiagnostic) MarshalJSON`.
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        if !self.file.is_empty() {
            return self.file.serialize(s);
        }
        self.diagnostics.serialize(s)
    }
}

/// `type readableBuildInfoFilePendingEmit struct` — marshals
/// `[file, emitKind, original]`.
struct ReadableBuildInfoFilePendingEmit {
    file: String,
    emit_kind: String,
    original: Option<BuildInfoFilePendingEmit>,
}

impl Serialize for ReadableBuildInfoFilePendingEmit {
    /// `(*readableBuildInfoFilePendingEmit) MarshalJSON`.
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.file, &self.emit_kind, &self.original).serialize(s)
    }
}

/// `type readableBuildInfoEmitSignature struct`.
#[derive(Serialize)]
struct ReadableBuildInfoEmitSignature {
    #[serde(rename = "file", skip_serializing_if = "String::is_empty")]
    file: String,
    #[serde(rename = "signature", skip_serializing_if = "String::is_empty")]
    signature: String,
    #[serde(
        rename = "differsOnlyInDtsMap",
        skip_serializing_if = "is_false"
    )]
    differs_only_in_dts_map: bool,
    #[serde(
        rename = "differsInOptions",
        skip_serializing_if = "is_false"
    )]
    differs_in_options: bool,
    #[serde(rename = "original", skip_serializing_if = "Option::is_none")]
    original: Option<BuildInfoEmitSignature>,
}

/// `type readableBuildInfoResolvedRoot struct` — marshals
/// `[resolved, root]`.
struct ReadableBuildInfoResolvedRoot {
    resolved: String,
    root: String,
}

impl Serialize for ReadableBuildInfoResolvedRoot {
    /// `(*readableBuildInfoResolvedRoot) MarshalJSON`.
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        [&self.resolved, &self.root].serialize(s)
    }
}

/// `toReadableBuildInfo`.
pub fn to_readable_build_info(build_info: &BuildInfo, build_info_text: &str) -> String {
    let mut readable = ReadableBuildInfo {
        build_info,
        version: build_info.version.clone(),
        errors: build_info.errors,
        check_pending: build_info.check_pending,
        root: Vec::new(),
        package_jsons: build_info_paths_as_strings(&build_info.package_jsons),
        missing_package_jsons: build_info_paths_as_strings(&build_info.missing_package_jsons),
        file_names: build_info_paths_as_strings(&build_info.file_names),
        file_infos: Vec::new(),
        file_ids_list: Vec::new(),
        options: build_info.options.clone(),
        referenced_map: None,
        semantic_diagnostics_per_file: Vec::new(),
        emit_diagnostics_per_file: Vec::new(),
        change_file_set: Vec::new(),
        affected_files_pending_emit: Vec::new(),
        latest_changed_dts_file: build_info.latest_changed_dts_file.as_string().to_string(),
        emit_signatures: Vec::new(),
        resolved_root: Vec::new(),
        size: build_info_text.len(),
        semantic_errors: build_info.semantic_errors,
    };
    readable.set_file_infos();
    readable.set_root();
    readable.set_file_ids_list();
    readable.set_referenced_map();
    readable.set_change_file_set();
    readable.set_semantic_diagnostics();
    readable.set_emit_diagnostics();
    readable.set_affected_files_pending_emit();
    readable.set_emit_signatures();
    readable.set_resolved_root();
    let contents = tsc_json::marshal_indent(&readable, "", "  ").unwrap_or_else(|err| {
        panic!("readableBuildInfo: failed to marshal readable build info: {err}")
    });
    String::from_utf8(contents).expect("marshal produces utf-8")
}

/// `buildInfoPathsAsStrings`.
fn build_info_paths_as_strings(paths: &[BuildInfoPath]) -> Vec<String> {
    paths.iter().map(|p| p.as_string().to_string()).collect()
}

impl ReadableBuildInfo<'_> {
    /// `toFilePath`.
    fn to_file_path(&self, file_id: BuildInfoFileId) -> String {
        self.build_info.file_names[file_id as usize - 1]
            .as_string()
            .to_string()
    }

    /// `toFilePathSet`.
    fn to_file_path_set(&self, file_id_list_id: BuildInfoFileIdListId) -> Vec<String> {
        self.file_ids_list[file_id_list_id as usize - 1].clone()
    }

    /// `toReadableBuildInfoDiagnostic`.
    fn to_readable_build_info_diagnostic(
        &self,
        diagnostics: &[BuildInfoDiagnostic],
    ) -> Vec<ReadableBuildInfoDiagnostic> {
        diagnostics
            .iter()
            .map(|d| {
                let file = if d.file != 0 {
                    self.to_file_path(d.file)
                } else {
                    String::new()
                };
                ReadableBuildInfoDiagnostic {
                    file,
                    no_file: d.no_file,
                    pos: d.pos,
                    end: d.end,
                    code: d.code,
                    category: d.category,
                    message_key: d.message_key.clone(),
                    message_args: d.message_args.clone(),
                    message_chain: self.to_readable_build_info_diagnostic(&d.message_chain),
                    related_information: self
                        .to_readable_build_info_diagnostic(&d.related_information),
                    reports_unnecessary: d.reports_unnecessary,
                    reports_deprecated: d.reports_deprecated,
                    skipped_on_no_emit: d.skipped_on_no_emit,
                    repopulate_info: to_readable_build_info_repopulate_info(d.repopulate_info.as_ref()),
                }
            })
            .collect()
    }

    /// `toReadableBuildInfoDiagnosticsOfFile`.
    fn to_readable_build_info_diagnostics_of_file(
        &self,
        diagnostics: &BuildInfoDiagnosticsOfFile,
    ) -> ReadableBuildInfoDiagnosticsOfFile {
        ReadableBuildInfoDiagnosticsOfFile {
            file: self.to_file_path(diagnostics.file_id),
            diagnostics: self.to_readable_build_info_diagnostic(&diagnostics.diagnostics),
        }
    }

    /// `setFileInfos`.
    fn set_file_infos(&mut self) {
        self.file_infos = self
            .build_info
            .file_infos
            .iter()
            .enumerate()
            .map(|(index, original)| {
                let file_info = original
                    .as_ref()
                    .map(|o| o.get_file_info())
                    .unwrap_or_default();
                // Dont set original for string encoding
                let original = match original {
                    Some(o) if !o.has_signature() => Some(o.clone()),
                    _ => None,
                };
                ReadableBuildInfoFileInfo {
                    file_name: self.to_file_path(index as i32 + 1),
                    version: file_info.version().to_string(),
                    signature: file_info.signature().to_string(),
                    affects_global_scope: file_info.affects_global_scope(),
                    implied_node_format: file_info.implied_node_format().to_string(),
                    original,
                }
            })
            .collect();
    }

    /// `setRoot`.
    fn set_root(&mut self) {
        self.root = self
            .build_info
            .root
            .iter()
            .map(|original| {
                let files = if !original.non_incremental.as_string().is_empty() {
                    vec![original.non_incremental.as_string().to_string()]
                } else if original.end == 0 {
                    vec![self.to_file_path(original.start)]
                } else {
                    let mut files = Vec::with_capacity((original.end - original.start + 1) as usize);
                    for i in original.start..=original.end {
                        files.push(self.to_file_path(i));
                    }
                    files
                };
                ReadableBuildInfoRoot {
                    files,
                    original: Some(original.clone()),
                }
            })
            .collect();
    }

    /// `setFileIdsList`.
    fn set_file_ids_list(&mut self) {
        self.file_ids_list = self
            .build_info
            .file_ids_list
            .iter()
            .map(|ids| ids.iter().map(|&id| self.to_file_path(id)).collect())
            .collect();
    }

    /// `setReferencedMap`.
    fn set_referenced_map(&mut self) {
        // Go nil-checks the slice; `is_empty` is the port's equivalent (see
        // file-header note on nil-vs-empty).
        if !self.build_info.referenced_map.is_empty() {
            let mut referenced_map = OrderedMap::new();
            for entry in &self.build_info.referenced_map {
                referenced_map.set(
                    self.to_file_path(entry.file_id),
                    self.to_file_path_set(entry.file_id_list_id),
                );
            }
            self.referenced_map = Some(referenced_map);
        }
    }

    /// `setChangeFileSet`.
    fn set_change_file_set(&mut self) {
        self.change_file_set = self
            .build_info
            .change_file_set
            .iter()
            .map(|&id| self.to_file_path(id))
            .collect();
    }

    /// `setSemanticDiagnostics`.
    fn set_semantic_diagnostics(&mut self) {
        self.semantic_diagnostics_per_file = self
            .build_info
            .semantic_diagnostics_per_file
            .iter()
            .map(|diagnostics| {
                if diagnostics.file_id != 0 {
                    return ReadableBuildInfoSemanticDiagnostic {
                        file: self.to_file_path(diagnostics.file_id),
                        diagnostics: None,
                    };
                }
                ReadableBuildInfoSemanticDiagnostic {
                    file: String::new(),
                    diagnostics: diagnostics.diagnostics.as_ref().map(|d| {
                        Box::new(self.to_readable_build_info_diagnostics_of_file(d))
                    }),
                }
            })
            .collect();
    }

    /// `setEmitDiagnostics`.
    fn set_emit_diagnostics(&mut self) {
        self.emit_diagnostics_per_file = self
            .build_info
            .emit_diagnostics_per_file
            .iter()
            .map(|d| self.to_readable_build_info_diagnostics_of_file(d))
            .collect();
    }

    /// `setAffectedFilesPendingEmit`.
    fn set_affected_files_pending_emit(&mut self) {
        // Go nil-check — see file-header note on nil-vs-empty.
        if self.build_info.affected_files_pending_emit.is_empty() {
            return;
        }
        let full_emit_kind = get_file_emit_kind(
            &self
                .build_info
                .get_compiler_options(&RootedDirectoryPath::default()),
        );
        self.affected_files_pending_emit = self
            .build_info
            .affected_files_pending_emit
            .iter()
            .map(|pending_emit| {
                let emit_kind = if pending_emit.emit_kind == 0 {
                    full_emit_kind
                } else {
                    pending_emit.emit_kind
                };
                ReadableBuildInfoFilePendingEmit {
                    file: self.to_file_path(pending_emit.file_id),
                    emit_kind: to_readable_file_emit_kind(emit_kind),
                    original: Some(*pending_emit),
                }
            })
            .collect();
    }

    /// `setEmitSignatures`.
    fn set_emit_signatures(&mut self) {
        self.emit_signatures = self
            .build_info
            .emit_signatures
            .iter()
            .map(|signature| ReadableBuildInfoEmitSignature {
                file: self.to_file_path(signature.file_id),
                signature: signature.signature.clone(),
                differs_only_in_dts_map: signature.differs_only_in_dts_map,
                differs_in_options: signature.differs_in_options,
                original: Some(signature.clone()),
            })
            .collect();
    }

    /// `setResolvedRoot`.
    fn set_resolved_root(&mut self) {
        self.resolved_root = self
            .build_info
            .resolved_root
            .iter()
            .map(|original| ReadableBuildInfoResolvedRoot {
                resolved: self.to_file_path(original.resolved),
                root: self.to_file_path(original.root),
            })
            .collect();
    }
}

/// `toReadableBuildInfoRepopulateInfo`.
fn to_readable_build_info_repopulate_info(
    info: Option<&crate::incremental::build_info::BuildInfoRepopulateInfo>,
) -> Option<ReadableBuildInfoRepopulateInfo> {
    info.map(|info| ReadableBuildInfoRepopulateInfo {
        kind: info.kind,
        module_reference: info.module_reference.clone(),
        mode: info.mode,
        package_name: info.package_name.clone(),
    })
}

/// `toReadableFileEmitKind`.
fn to_readable_file_emit_kind(file_emit_kind: FileEmitKind) -> String {
    let mut builder = String::new();
    let add_flags = |flags: &str, builder: &mut String| {
        if builder.is_empty() {
            builder.push_str(flags);
        } else {
            builder.push('|');
            builder.push_str(flags);
        }
    };
    if file_emit_kind != 0 {
        if (file_emit_kind & FILE_EMIT_KIND_JS) != 0 {
            add_flags("Js", &mut builder);
        }
        if (file_emit_kind & FILE_EMIT_KIND_JS_MAP) != 0 {
            add_flags("JsMap", &mut builder);
        }
        if (file_emit_kind & FILE_EMIT_KIND_JS_INLINE_MAP) != 0 {
            add_flags("JsInlineMap", &mut builder);
        }
        if (file_emit_kind & FILE_EMIT_KIND_DTS) == FILE_EMIT_KIND_DTS {
            add_flags("Dts", &mut builder);
        } else {
            if (file_emit_kind & FILE_EMIT_KIND_DTS_EMIT) != 0 {
                add_flags("DtsEmit", &mut builder);
            }
            if (file_emit_kind & FILE_EMIT_KIND_DTS_ERRORS) != 0 {
                add_flags("DtsErrors", &mut builder);
            }
        }
        if (file_emit_kind & FILE_EMIT_KIND_DTS_MAP) != 0 {
            add_flags("DtsMap", &mut builder);
        }
    }
    if !builder.is_empty() {
        return builder;
    }
    "None".to_string()
}
