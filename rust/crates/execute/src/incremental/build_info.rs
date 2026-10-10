// Ported from tsc/internal/execute/incremental/buildInfo.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use tsc_collections::{OrderedMap, SyncMap};
use tsc_contentmapper::host::Project;
use tsc_core::compileroptions::{RESOLUTION_MODE_COMMON_JS, ResolutionMode};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::version::version as core_version;
use tsc_diagnostics::Category;
use tsc_tsoptions::commandlineoption::CommandLineOptionKind;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::parsinghelpers::{convert_option_to_absolute_path, parse_compiler_options};
use tsc_tsoptions::tsconfigparsing::{command_line_compiler_options_map, name_map_get};
use tsc_tsoptions::value::{Value, value_into_go_map};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, path_is_absolute,
    path_is_relative, to_rooted_file_path,
};

use crate::incremental::snapshot::{
    FILE_EMIT_KIND_DTS, FILE_EMIT_KIND_DTS_ERRORS, FileEmitKind, FileInfo,
};

// ===========================================================================
// Serialized id/path aliases.
//
// Go `type BuildInfoFileId int` — file ids are 1-based indexes into
// `file_names`/`file_infos`; 0 means absent. Go `type BuildInfoFileIdListId
// int` indexes `file_ids_list`. Go `type BuildInfoPath string` may be relative
// to the build-info file, absolute, or a symbolic default-library name.
// ===========================================================================

/// `type BuildInfoFileId int` — 1-based id into `file_names`/`file_infos`.
pub type BuildInfoFileId = i32;
/// `type BuildInfoFileIdListId int` — 1-based id into `file_ids_list`.
pub type BuildInfoFileIdListId = i32;

/// `type BuildInfoPath string`.
#[derive(Clone, Default, PartialEq, Eq, Hash, Debug)]
pub struct BuildInfoPath(pub String);

impl BuildInfoPath {
    /// `(p BuildInfoPath) AsString`.
    pub fn as_string(&self) -> &str {
        &self.0
    }
}

impl From<String> for BuildInfoPath {
    fn from(s: String) -> Self {
        BuildInfoPath(s)
    }
}

impl From<&str> for BuildInfoPath {
    fn from(s: &str) -> Self {
        BuildInfoPath(s.to_string())
    }
}

impl AsRef<str> for BuildInfoPath {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Serialize for BuildInfoPath {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for BuildInfoPath {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(BuildInfoPath(String::deserialize(deserializer)?))
    }
}

// ===========================================================================
// omitzero helpers.
// ===========================================================================

fn is_false(b: &bool) -> bool {
    !*b
}

fn is_zero_file_id(id: &BuildInfoFileId) -> bool {
    *id == 0
}

fn is_zero_i32(v: &i32) -> bool {
    *v == 0
}

fn is_none_mode(mode: &ResolutionMode) -> bool {
    *mode == ResolutionMode::None
}

fn is_empty_path(p: &BuildInfoPath) -> bool {
    p.0.is_empty()
}

fn serialize_category<S: Serializer>(category: &Category, s: S) -> Result<S::Ok, S::Error> {
    (*category as i32).serialize(s)
}

fn deserialize_category<'de, D: Deserializer<'de>>(d: D) -> Result<Category, D::Error> {
    match i32::deserialize(d)? {
        0 => Ok(Category::Warning),
        1 => Ok(Category::Error),
        2 => Ok(Category::Suggestion),
        3 => Ok(Category::Message),
        // PORT: Go stores the raw int32 into `diagnostics.Category` without
        // validation; Rust enums reject out-of-range values, so reading a
        // corrupt build-info category fails the whole file rather than
        // smuggling an invalid discriminant.
        other => Err(serde::de::Error::custom(format!(
            "invalid diagnostic category: {other}"
        ))),
    }
}

fn category_is_warning(c: &Category) -> bool {
    *c == Category::Warning
}

// ===========================================================================
// BuildInfoRoot.
// ===========================================================================

/// `type BuildInfoRoot struct` — for incremental programs `start`/`end` are a
/// range of consecutive file ids (or `start` alone); for non-incremental
/// programs `non_incremental` is the root file name.
#[derive(Clone, Default, Debug)]
pub struct BuildInfoRoot {
    pub start: BuildInfoFileId,
    pub end: BuildInfoFileId,
    pub non_incremental: BuildInfoPath,
}

impl Serialize for BuildInfoRoot {
    /// `(*BuildInfoRoot) MarshalJSON`.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.start != 0 {
            if self.end != 0 {
                [self.start, self.end].serialize(serializer)
            } else {
                self.start.serialize(serializer)
            }
        } else {
            self.non_incremental.serialize(serializer)
        }
    }
}

impl<'de> Deserialize<'de> for BuildInfoRoot {
    /// `(*BuildInfoRoot) UnmarshalJSON` — try `[start, end]`, then `start`,
    /// then a non-incremental name, in that order.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Range([i32; 2]),
            Single(i32),
            Name(BuildInfoPath),
        }
        match Repr::deserialize(deserializer)? {
            Repr::Range([start, end]) => Ok(BuildInfoRoot {
                start,
                end,
                non_incremental: BuildInfoPath::default(),
            }),
            Repr::Single(start) => Ok(BuildInfoRoot {
                start,
                end: 0,
                non_incremental: BuildInfoPath::default(),
            }),
            Repr::Name(name) => Ok(BuildInfoRoot {
                start: 0,
                end: 0,
                non_incremental: name,
            }),
        }
    }
}

// ===========================================================================
// BuildInfoFileInfo.
// ===========================================================================

/// `type buildInfoFileInfoNoSignature struct`.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub(crate) struct BuildInfoFileInfoNoSignature {
    #[serde(rename = "version", default, skip_serializing_if = "String::is_empty")]
    pub version: String,
    #[serde(rename = "noSignature", default, skip_serializing_if = "is_false")]
    pub no_signature: bool,
    #[serde(
        rename = "affectsGlobalScope",
        default,
        skip_serializing_if = "is_false"
    )]
    pub affects_global_scope: bool,
    #[serde(
        rename = "impliedNodeFormat",
        default,
        skip_serializing_if = "is_none_mode"
    )]
    pub implied_node_format: ResolutionMode,
}

/// `type buildInfoFileInfoWithSignature struct` — `signature` is undefined
/// when `FileInfo.version == FileInfo.signature`.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub(crate) struct BuildInfoFileInfoWithSignature {
    #[serde(rename = "version", default, skip_serializing_if = "String::is_empty")]
    pub version: String,
    #[serde(
        rename = "signature",
        default,
        skip_serializing_if = "String::is_empty"
    )]
    pub signature: String,
    #[serde(
        rename = "affectsGlobalScope",
        default,
        skip_serializing_if = "is_false"
    )]
    pub affects_global_scope: bool,
    #[serde(
        rename = "impliedNodeFormat",
        default,
        skip_serializing_if = "is_none_mode"
    )]
    pub implied_node_format: ResolutionMode,
}

/// `type BuildInfoFileInfo struct` — a signature string, a no-signature
/// record, or a full with-signature record.
#[derive(Clone, Default, Debug)]
pub struct BuildInfoFileInfo {
    pub(crate) signature: String,
    pub(crate) no_signature: Option<BuildInfoFileInfoNoSignature>,
    pub(crate) file_info: Option<BuildInfoFileInfoWithSignature>,
}

/// `func newBuildInfoFileInfo`.
pub(crate) fn new_build_info_file_info(file_info: &FileInfo) -> BuildInfoFileInfo {
    let version = file_info.version();
    let signature = file_info.signature();
    if version == signature {
        if !file_info.affects_global_scope()
            && file_info.implied_node_format() == RESOLUTION_MODE_COMMON_JS
        {
            return BuildInfoFileInfo {
                signature: signature.to_string(),
                ..Default::default()
            };
        }
    } else if signature.is_empty() {
        return BuildInfoFileInfo {
            no_signature: Some(BuildInfoFileInfoNoSignature {
                version: version.to_string(),
                no_signature: true,
                affects_global_scope: file_info.affects_global_scope(),
                implied_node_format: file_info.implied_node_format(),
            }),
            ..Default::default()
        };
    }
    BuildInfoFileInfo {
        file_info: Some(BuildInfoFileInfoWithSignature {
            version: version.to_string(),
            signature: if signature == version {
                String::new()
            } else {
                signature.to_string()
            },
            affects_global_scope: file_info.affects_global_scope(),
            implied_node_format: file_info.implied_node_format(),
        }),
        ..Default::default()
    }
}

impl BuildInfoFileInfo {
    /// `(*BuildInfoFileInfo) GetFileInfo` — `Option<&Self>` receiver mirrors
    /// Go's nil-able `*BuildInfoFileInfo`.
    pub fn get_file_info(&self) -> FileInfo {
        if !self.signature.is_empty() {
            return FileInfo {
                version: self.signature.clone(),
                signature: self.signature.clone(),
                implied_node_format: RESOLUTION_MODE_COMMON_JS,
                ..Default::default()
            };
        }
        if let Some(no_signature) = &self.no_signature {
            return FileInfo {
                version: no_signature.version.clone(),
                affects_global_scope: no_signature.affects_global_scope,
                implied_node_format: no_signature.implied_node_format,
                ..Default::default()
            };
        }
        let file_info = self.file_info.as_ref().cloned().unwrap_or_default();
        FileInfo {
            signature: if file_info.signature.is_empty() {
                file_info.version.clone()
            } else {
                file_info.signature.clone()
            },
            version: file_info.version,
            affects_global_scope: file_info.affects_global_scope,
            implied_node_format: file_info.implied_node_format,
        }
    }

    /// `(*BuildInfoFileInfo) HasSignature`.
    pub fn has_signature(&self) -> bool {
        !self.signature.is_empty()
    }
}

impl Serialize for BuildInfoFileInfo {
    /// `(*BuildInfoFileInfo) MarshalJSON`.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if !self.signature.is_empty() {
            return self.signature.serialize(serializer);
        }
        if let Some(no_signature) = &self.no_signature {
            return no_signature.serialize(serializer);
        }
        self.file_info.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BuildInfoFileInfo {
    /// `(*BuildInfoFileInfo) UnmarshalJSON` — string signature, then a
    /// no-signature record (only if `noSignature` is true), then a
    /// with-signature record.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // PORT: Go tries `json.Unmarshal` into successive types; serde_json's
        // `Value` buffer gives the same "try each representation" behavior.
        let value = serde_json::Value::deserialize(deserializer)?;
        if let Ok(signature) = serde_json::from_value::<String>(value.clone()) {
            return Ok(BuildInfoFileInfo {
                signature,
                ..Default::default()
            });
        }
        match serde_json::from_value::<BuildInfoFileInfoNoSignature>(value.clone()) {
            Ok(no_signature) if no_signature.no_signature => {
                return Ok(BuildInfoFileInfo {
                    no_signature: Some(no_signature),
                    ..Default::default()
                });
            }
            _ => {}
        }
        let file_info = serde_json::from_value::<BuildInfoFileInfoWithSignature>(value)
            .map_err(|e| serde::de::Error::custom(format!("invalid BuildInfoFileInfo: {e}")))?;
        Ok(BuildInfoFileInfo {
            file_info: Some(file_info),
            ..Default::default()
        })
    }
}

// ===========================================================================
// BuildInfoReferenceMapEntry.
// ===========================================================================

/// `type BuildInfoReferenceMapEntry struct` — serialized `[fileId, fileIdListId]`.
#[derive(Clone, Copy, Default, Debug)]
pub struct BuildInfoReferenceMapEntry {
    pub file_id: BuildInfoFileId,
    pub file_id_list_id: BuildInfoFileIdListId,
}

impl Serialize for BuildInfoReferenceMapEntry {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        [self.file_id, self.file_id_list_id].serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BuildInfoReferenceMapEntry {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let [file_id, file_id_list_id] = <[i32; 2]>::deserialize(deserializer)?;
        Ok(BuildInfoReferenceMapEntry {
            file_id,
            file_id_list_id,
        })
    }
}

// ===========================================================================
// BuildInfoDiagnostic / BuildInfoRepopulateInfo.
// ===========================================================================

/// `type BuildInfoDiagnostic struct` — field order and `,omitzero` handling
/// mirror the Go struct tags so the serialized shape is identical.
///
/// PORT: `message_key` is `String` here (Go's `diagnostics.Key`); conversion
/// to the internal diagnostics representation interns it as a `&'static str`.
/// `category` round-trips through its int32 representation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BuildInfoDiagnostic {
    /// BuildInfoFileId if it is for a file other than the one it is stored for.
    #[serde(rename = "file", default, skip_serializing_if = "is_zero_file_id")]
    pub file: BuildInfoFileId,
    #[serde(rename = "noFile", default, skip_serializing_if = "is_false")]
    pub no_file: bool,
    #[serde(rename = "pos", default, skip_serializing_if = "is_zero_i32")]
    pub pos: i32,
    #[serde(rename = "end", default, skip_serializing_if = "is_zero_i32")]
    pub end: i32,
    #[serde(rename = "code", default, skip_serializing_if = "is_zero_i32")]
    pub code: i32,
    #[serde(
        rename = "category",
        default = "default_category",
        skip_serializing_if = "category_is_warning",
        serialize_with = "serialize_category",
        deserialize_with = "deserialize_category"
    )]
    pub category: Category,
    #[serde(rename = "source", default, skip_serializing_if = "String::is_empty")]
    pub source: String,
    #[serde(
        rename = "messageText",
        default,
        skip_serializing_if = "String::is_empty"
    )]
    pub message_text: String,
    #[serde(
        rename = "messageKey",
        default,
        skip_serializing_if = "String::is_empty"
    )]
    pub message_key: String,
    #[serde(rename = "messageArgs", default, skip_serializing_if = "Vec::is_empty")]
    pub message_args: Vec<String>,
    #[serde(
        rename = "messageChain",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub message_chain: Vec<BuildInfoDiagnostic>,
    #[serde(
        rename = "relatedInformation",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub related_information: Vec<BuildInfoDiagnostic>,
    #[serde(
        rename = "reportsUnnecessary",
        default,
        skip_serializing_if = "is_false"
    )]
    pub reports_unnecessary: bool,
    #[serde(
        rename = "reportsDeprecated",
        default,
        skip_serializing_if = "is_false"
    )]
    pub reports_deprecated: bool,
    #[serde(rename = "skippedOnNoEmit", default, skip_serializing_if = "is_false")]
    pub skipped_on_no_emit: bool,
    #[serde(
        rename = "repopulateInfo",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub repopulate_info: Option<BuildInfoRepopulateInfo>,
}

/// Go's zero-value `Category` is `Warning` (category 0); `Category` has no
/// `Default` impl in `tsc_diagnostics`, so provide it manually.
impl Default for BuildInfoDiagnostic {
    fn default() -> Self {
        Self {
            file: 0,
            no_file: false,
            pos: 0,
            end: 0,
            code: 0,
            category: default_category(),
            source: String::new(),
            message_text: String::new(),
            message_key: String::new(),
            message_args: Vec::new(),
            message_chain: Vec::new(),
            related_information: Vec::new(),
            reports_unnecessary: false,
            reports_deprecated: false,
            skipped_on_no_emit: false,
            repopulate_info: None,
        }
    }
}

fn default_category() -> Category {
    Category::Warning
}

/// `type BuildInfoRepopulateInfo struct` — `kind` is always emitted (no
/// omitzero in Go).
#[derive(Clone, Default, Debug)]
pub struct BuildInfoRepopulateInfo {
    pub kind: tsc_ast::diagnostic::RepopulateDiagnosticKind,
    pub module_reference: String,
    pub mode: ResolutionMode,
    pub package_name: String,
}

impl Serialize for BuildInfoRepopulateInfo {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = serializer.serialize_struct("BuildInfoRepopulateInfo", 4)?;
        st.serialize_field("kind", &self.kind.0)?;
        if !self.module_reference.is_empty() {
            st.serialize_field("moduleReference", &self.module_reference)?;
        }
        if !is_none_mode(&self.mode) {
            st.serialize_field("mode", &self.mode)?;
        }
        if !self.package_name.is_empty() {
            st.serialize_field("packageName", &self.package_name)?;
        }
        st.end()
    }
}

impl<'de> Deserialize<'de> for BuildInfoRepopulateInfo {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct Repr {
            #[serde(default)]
            kind: i32,
            #[serde(rename = "moduleReference", default)]
            module_reference: String,
            #[serde(rename = "mode", default)]
            mode: ResolutionMode,
            #[serde(rename = "packageName", default)]
            package_name: String,
        }
        let repr = Repr::deserialize(deserializer)?;
        Ok(BuildInfoRepopulateInfo {
            kind: tsc_ast::diagnostic::RepopulateDiagnosticKind(repr.kind),
            module_reference: repr.module_reference,
            mode: repr.mode,
            package_name: repr.package_name,
        })
    }
}

// ===========================================================================
// BuildInfoDiagnosticsOfFile.
// ===========================================================================

/// `type BuildInfoDiagnosticsOfFile struct` — serialized `[fileId, diagnostics]`.
#[derive(Clone, Default, Debug)]
pub struct BuildInfoDiagnosticsOfFile {
    pub file_id: BuildInfoFileId,
    pub diagnostics: Vec<BuildInfoDiagnostic>,
}

impl Serialize for BuildInfoDiagnosticsOfFile {
    /// `(*BuildInfoDiagnosticsOfFile) MarshalJSON`.
    ///
    /// PORT: Go marshals `[]any{fileId, diagnostics}` where a nil diagnostics
    /// slice would emit `null`; the Rust port always stores a `Vec`, which
    /// emits `[]`. Go only ever serializes non-empty lists here
    /// (`toBuildInfoDiagnosticsOfFile` returns nil otherwise), so the shapes
    // are identical in practice.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (self.file_id, &self.diagnostics).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BuildInfoDiagnosticsOfFile {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (file_id, diagnostics) =
            <(BuildInfoFileId, Vec<BuildInfoDiagnostic>)>::deserialize(deserializer).map_err(
                |e| serde::de::Error::custom(format!("invalid BuildInfoDiagnosticsOfFile: {e}")),
            )?;
        Ok(BuildInfoDiagnosticsOfFile {
            file_id,
            diagnostics,
        })
    }
}

// ===========================================================================
// BuildInfoSemanticDiagnostic.
// ===========================================================================

/// `type BuildInfoSemanticDiagnostic struct` — a bare file id when the file is
/// not in the changed set and has no cached diagnostics, otherwise
/// `[fileId, diagnostics]`.
#[derive(Clone, Default, Debug)]
pub struct BuildInfoSemanticDiagnostic {
    pub file_id: BuildInfoFileId,
    pub diagnostics: Option<Box<BuildInfoDiagnosticsOfFile>>,
}

impl Serialize for BuildInfoSemanticDiagnostic {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.file_id != 0 {
            self.file_id.serialize(serializer)
        } else {
            self.diagnostics.serialize(serializer)
        }
    }
}

impl<'de> Deserialize<'de> for BuildInfoSemanticDiagnostic {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            FileId(BuildInfoFileId),
            Diagnostics(BuildInfoDiagnosticsOfFile),
        }
        match Repr::deserialize(deserializer)? {
            Repr::FileId(file_id) => Ok(BuildInfoSemanticDiagnostic {
                file_id,
                diagnostics: None,
            }),
            Repr::Diagnostics(diagnostics) => Ok(BuildInfoSemanticDiagnostic {
                file_id: 0,
                diagnostics: Some(Box::new(diagnostics)),
            }),
        }
    }
}

// ===========================================================================
// BuildInfoFilePendingEmit.
// ===========================================================================

/// `type BuildInfoFilePendingEmit struct` — `fileId` when the pending emit
/// matches what compiler options imply, `[fileId]` for dts-only emit, or
/// `[fileId, emitKind]` otherwise.
#[derive(Clone, Copy, Default, Debug)]
pub struct BuildInfoFilePendingEmit {
    pub file_id: BuildInfoFileId,
    pub emit_kind: FileEmitKind,
}

impl Serialize for BuildInfoFilePendingEmit {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.emit_kind == 0 {
            return self.file_id.serialize(serializer);
        }
        if self.emit_kind == FILE_EMIT_KIND_DTS {
            return [self.file_id].serialize(serializer);
        }
        [self.file_id, self.emit_kind].serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BuildInfoFilePendingEmit {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Single(BuildInfoFileId),
            Tuple(Vec<i32>),
        }
        match Repr::deserialize(deserializer)? {
            Repr::Single(file_id) => Ok(BuildInfoFilePendingEmit {
                file_id,
                emit_kind: 0,
            }),
            Repr::Tuple(tuple) => match tuple.len() {
                1 => Ok(BuildInfoFilePendingEmit {
                    file_id: tuple[0],
                    emit_kind: FILE_EMIT_KIND_DTS,
                }),
                2 => Ok(BuildInfoFilePendingEmit {
                    file_id: tuple[0],
                    emit_kind: tuple[1],
                }),
                n => Err(serde::de::Error::custom(format!(
                    "invalid BuildInfoFilePendingEmit: expected 1 or 2 integers, got {n}"
                ))),
            },
        }
    }
}

// ===========================================================================
// BuildInfoEmitSignature.
// ===========================================================================

/// `type BuildInfoEmitSignature struct` — `[fileId, signature]` when the emit
/// signature differs from the file's signature, or a bare `fileId` when the
/// file was not emitted.
#[derive(Clone, Default, Debug)]
pub struct BuildInfoEmitSignature {
    pub file_id: BuildInfoFileId,
    /// Signature if it is different from the file's signature.
    pub signature: String,
    /// True if the signature differs only in the dts map value.
    pub differs_only_in_dts_map: bool,
    /// True if the signature differs in the options used to emit the file.
    pub differs_in_options: bool,
}

impl BuildInfoEmitSignature {
    /// `(*BuildInfoEmitSignature) noEmitSignature`.
    pub(crate) fn no_emit_signature(&self) -> bool {
        self.signature.is_empty() && !self.differs_only_in_dts_map && !self.differs_in_options
    }

    /// `(*BuildInfoEmitSignature) toEmitSignature`.
    pub(crate) fn to_emit_signature(
        &self,
        path: &PathKey,
        emit_signatures: &SyncMap<
            PathKey,
            std::rc::Rc<crate::incremental::snapshot::EmitSignature>,
        >,
    ) -> crate::incremental::snapshot::EmitSignature {
        let mut signature = String::new();
        let mut signature_with_different_options: Option<Vec<String>> = None;
        if self.differs_only_in_dts_map {
            let info = emit_signatures.load(path).expect("emit signature");
            signature_with_different_options = Some(vec![info.signature.clone()]);
        } else if self.differs_in_options {
            signature_with_different_options = Some(vec![self.signature.clone()]);
        } else {
            signature = self.signature.clone();
        }
        crate::incremental::snapshot::EmitSignature {
            signature,
            signature_with_different_options,
        }
    }
}

impl Serialize for BuildInfoEmitSignature {
    /// `(*BuildInfoEmitSignature) MarshalJSON`.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.no_emit_signature() {
            return self.file_id.serialize(serializer);
        }
        // Go marshals `[]any{fileId, signature}` where signature is a string,
        // `[]string{}` (differsOnlyInDtsMap) or `[]string{signature}`
        // (differsInOptions).
        if self.differs_only_in_dts_map {
            return (self.file_id, Vec::<String>::new()).serialize(serializer);
        }
        if self.differs_in_options {
            return (self.file_id, vec![self.signature.clone()]).serialize(serializer);
        }
        (self.file_id, self.signature.clone()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BuildInfoEmitSignature {
    /// `(*BuildInfoEmitSignature) UnmarshalJSON` — bare file id or
    /// `[fileId, signature | [] | [signature]]`.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Single(BuildInfoFileId),
            Pair(Box<(i32, serde_json::Value)>),
        }
        match Repr::deserialize(deserializer)? {
            Repr::Single(file_id) => Ok(BuildInfoEmitSignature {
                file_id,
                ..Default::default()
            }),
            Repr::Pair(pair) => {
                let (file_id, signature_value) = *pair;
                let mut signature = String::new();
                let mut differs_only_in_dts_map = false;
                let mut differs_in_options = false;
                match signature_value {
                    serde_json::Value::String(s) => signature = s,
                    serde_json::Value::Array(list) => match list.len() {
                        0 => differs_only_in_dts_map = true,
                        1 => match &list[0] {
                            serde_json::Value::String(s) => {
                                signature = s.clone();
                                differs_in_options = true;
                            }
                            other => {
                                return Err(serde::de::Error::custom(format!(
                                    "invalid signature in BuildInfoEmitSignature: expected string, got {other}"
                                )));
                            }
                        },
                        n => {
                            return Err(serde::de::Error::custom(format!(
                                "invalid signature in BuildInfoEmitSignature: expected []string with 0 or 1 element, got {n} elements"
                            )));
                        }
                    },
                    other => {
                        return Err(serde::de::Error::custom(format!(
                            "invalid signature in BuildInfoEmitSignature: expected string or []string, got {other}"
                        )));
                    }
                }
                Ok(BuildInfoEmitSignature {
                    file_id,
                    signature,
                    differs_only_in_dts_map,
                    differs_in_options,
                })
            }
        }
    }
}

// ===========================================================================
// BuildInfoResolvedRoot.
// ===========================================================================

/// `type BuildInfoResolvedRoot struct` — serialized `[resolved, root]`.
#[derive(Clone, Copy, Default, Debug)]
pub struct BuildInfoResolvedRoot {
    pub resolved: BuildInfoFileId,
    pub root: BuildInfoFileId,
}

impl Serialize for BuildInfoResolvedRoot {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        [self.resolved, self.root].serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for BuildInfoResolvedRoot {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let [resolved, root] = <[i32; 2]>::deserialize(deserializer)
            .map_err(|_| serde::de::Error::custom("invalid BuildInfoResolvedRoot"))?;
        Ok(BuildInfoResolvedRoot { resolved, root })
    }
}

// ===========================================================================
// BuildInfo.
// ===========================================================================

/// `type BuildInfo struct` — field order mirrors Go's struct definition so
/// `tsc_json::marshal` produces byte-compatible field ordering.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct BuildInfo {
    #[serde(rename = "version", default, skip_serializing_if = "String::is_empty")]
    pub version: String,

    // Common between incremental and tsc -b buildinfo for non incremental programs
    #[serde(rename = "errors", default, skip_serializing_if = "is_false")]
    pub errors: bool,
    #[serde(rename = "checkPending", default, skip_serializing_if = "is_false")]
    pub check_pending: bool,
    #[serde(rename = "root", default, skip_serializing_if = "Vec::is_empty")]
    pub root: Vec<BuildInfoRoot>,
    #[serde(
        rename = "packageJsons",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub package_jsons: Vec<BuildInfoPath>,
    #[serde(
        rename = "missingPackageJsons",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub missing_package_jsons: Vec<BuildInfoPath>,
    #[serde(
        rename = "contentMapperIdentities",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub content_mapper_identities: Vec<String>,

    // IncrementalProgram info
    #[serde(rename = "fileNames", default, skip_serializing_if = "Vec::is_empty")]
    pub file_names: Vec<BuildInfoPath>,
    #[serde(rename = "fileInfos", default, skip_serializing_if = "Vec::is_empty")]
    pub file_infos: Vec<Option<BuildInfoFileInfo>>,
    #[serde(rename = "fileIdsList", default, skip_serializing_if = "Vec::is_empty")]
    pub file_ids_list: Vec<Vec<BuildInfoFileId>>,
    #[serde(
        rename = "options",
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "deserialize_build_info_options"
    )]
    pub options: Option<OrderedMap<String, Value>>,
    #[serde(
        rename = "referencedMap",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub referenced_map: Vec<BuildInfoReferenceMapEntry>,
    #[serde(
        rename = "semanticDiagnosticsPerFile",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub semantic_diagnostics_per_file: Vec<BuildInfoSemanticDiagnostic>,
    #[serde(
        rename = "emitDiagnosticsPerFile",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub emit_diagnostics_per_file: Vec<BuildInfoDiagnosticsOfFile>,
    #[serde(
        rename = "changeFileSet",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub change_file_set: Vec<BuildInfoFileId>,
    #[serde(
        rename = "affectedFilesPendingEmit",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub affected_files_pending_emit: Vec<BuildInfoFilePendingEmit>,
    /// Because this is the only output file in the program, no fileId is needed
    /// to deduplicate the name.
    #[serde(
        rename = "latestChangedDtsFile",
        default,
        skip_serializing_if = "is_empty_path"
    )]
    pub latest_changed_dts_file: BuildInfoPath,
    #[serde(
        rename = "emitSignatures",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub emit_signatures: Vec<BuildInfoEmitSignature>,
    #[serde(
        rename = "resolvedRoot",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub resolved_root: Vec<BuildInfoResolvedRoot>,

    // NonIncrementalProgram info
    #[serde(rename = "semanticErrors", default, skip_serializing_if = "is_false")]
    pub semantic_errors: bool,
}

/// Deserializes `BuildInfo.options` — nested object members decode into
/// `map[string]any` in Go (the OrderedMap values are plain `any`), so they
/// become `Value::GoMap` here, matching Go's parse behavior (e.g. the
/// `*OrderedMap` assertion in `parseStringMap` deliberately fails on them).
fn deserialize_build_info_options<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<OrderedMap<String, Value>>, D::Error> {
    let raw: Option<OrderedMap<String, Value>> = Option::deserialize(deserializer)?;
    let Some(raw) = raw else {
        return Ok(None);
    };
    let mut map = OrderedMap::with_size_hint(raw.size());
    for (key, value) in raw.entries() {
        map.set(key.clone(), value_into_go_map(value.clone()));
    }
    Ok(Some(map))
}

impl BuildInfo {
    /// `(*BuildInfo) IsValidVersion`.
    pub fn is_valid_version(&self) -> bool {
        self.version == core_version()
    }

    /// `(*BuildInfo) ContentMapperIdentitiesMatch`.
    pub fn content_mapper_identities_match(&self, current: &[String]) -> bool {
        self.content_mapper_identities == current
    }

    /// `(*BuildInfo) IsIncremental` — Go also nil-checks the receiver; here
    /// the Option at the call site carries the nil.
    pub fn is_incremental(&self) -> bool {
        !self.file_names.is_empty()
    }

    /// `(b *BuildInfo) fileName` (1-based).
    pub(crate) fn file_name(&self, file_id: BuildInfoFileId) -> &BuildInfoPath {
        static EMPTY: BuildInfoPath = BuildInfoPath(String::new());
        if file_id < 1 || file_id as usize > self.file_names.len() {
            return &EMPTY;
        }
        &self.file_names[file_id as usize - 1]
    }

    /// `(b *BuildInfo) fileInfo` (1-based).
    pub(crate) fn file_info(&self, file_id: BuildInfoFileId) -> Option<&BuildInfoFileInfo> {
        if file_id < 1 || file_id as usize > self.file_infos.len() {
            return None;
        }
        self.file_infos[file_id as usize - 1].as_ref()
    }

    /// `(*BuildInfo) GetCompilerOptions`.
    pub fn get_compiler_options(
        &self,
        build_info_directory: &RootedDirectoryPath,
    ) -> CompilerOptions {
        let mut options = CompilerOptions::default();
        if let Some(options_map) = &self.options {
            let name_map = command_line_compiler_options_map();
            for (option, value) in options_map.entries() {
                let option_declaration = name_map_get(name_map, option);
                if build_info_directory.as_string().is_empty() {
                    if let Some(option_declaration) = option_declaration {
                        let mut path_kind = option_declaration.path_kind;
                        if option_declaration.kind == CommandLineOptionKind::List {
                            if let Some(element) = option_declaration.elements() {
                                path_kind = element.path_kind;
                            }
                        }
                        if path_kind.is_rooted() {
                            continue;
                        }
                    }
                }
                if !build_info_directory.as_string().is_empty() {
                    if let Some(result) = convert_option_to_absolute_path(
                        option,
                        value,
                        name_map,
                        build_info_directory,
                    ) {
                        parse_compiler_options(option, &result, &mut options);
                        continue;
                    }
                }
                parse_compiler_options(option, value, &mut options);
            }
        }
        options
    }

    /// `(*BuildInfo) IsEmitPending`.
    pub fn is_emit_pending(
        &self,
        resolved: &ParsedCommandLine,
        build_info_directory: &RootedDirectoryPath,
    ) -> bool {
        let compiler_options = resolved.compiler_options().cloned().unwrap_or_default();
        // Some of the emit files like source map or dts etc are not yet done
        if !compiler_options.no_emit.is_true() || compiler_options.get_emit_declarations() {
            let mut pending_emit = crate::incremental::snapshot::get_pending_emit_kind_with_options(
                &compiler_options,
                &self.get_compiler_options(build_info_directory),
            );
            if compiler_options.no_emit.is_true() {
                pending_emit &= FILE_EMIT_KIND_DTS_ERRORS;
            }
            return pending_emit != 0;
        }
        false
    }

    /// `(*BuildInfo) GetPackageJsons`.
    pub fn get_package_jsons(
        &self,
        build_info_directory: &RootedDirectoryPath,
    ) -> Vec<RootedFilePath> {
        get_build_info_file_names(&self.package_jsons, build_info_directory)
    }

    /// `(*BuildInfo) GetMissingPackageJsons`.
    pub fn get_missing_package_jsons(
        &self,
        build_info_directory: &RootedDirectoryPath,
    ) -> Vec<RootedFilePath> {
        get_build_info_file_names(&self.missing_package_jsons, build_info_directory)
    }

    /// `(*BuildInfo) GetBuildInfoRootInfoReader`.
    pub fn get_build_info_root_info_reader(
        &self,
        build_info_directory: &RootedDirectoryPath,
        case_sensitivity: CaseSensitivity,
    ) -> BuildInfoRootInfoReader {
        let mut resolved_root_file_infos: rustc_hash::FxHashMap<PathKey, BuildInfoFileInfo> =
            rustc_hash::FxHashMap::default();
        let mut resolved_root_file_names: rustc_hash::FxHashMap<PathKey, RootedFilePath> =
            rustc_hash::FxHashMap::default();
        let mut root_file_names: rustc_hash::FxHashMap<PathKey, RootedFilePath> =
            rustc_hash::FxHashMap::default();
        // Roots of the file
        let mut root_to_resolved =
            OrderedMap::<PathKey, PathKey>::with_size_hint(self.file_names.len());
        let mut resolved_to_root: rustc_hash::FxHashMap<PathKey, PathKey> =
            rustc_hash::FxHashMap::default();
        let to_file_name = |file_name: &BuildInfoPath| -> RootedFilePath {
            to_rooted_file_path(file_name.as_string(), build_info_directory)
        };

        // Create map from resolvedRoot to root
        for resolved in &self.resolved_root {
            let resolved_root = self.file_name(resolved.resolved);
            let root = self.file_name(resolved.root);
            if !resolved_root.as_string().is_empty() && !root.as_string().is_empty() {
                let root_file_name = to_file_name(root);
                let root_path = case_sensitivity.path_key(&root_file_name.as_path());
                resolved_to_root.insert(
                    case_sensitivity.path_key(&to_file_name(resolved_root).as_path()),
                    root_path.clone(),
                );
                root_file_names.insert(root_path, root_file_name);
            }
        }

        let mut add_root = |resolved_root: &BuildInfoPath,
                            file_info: Option<&BuildInfoFileInfo>| {
            if resolved_root.as_string().is_empty() {
                return;
            }
            let resolved_root_file_name = to_file_name(resolved_root);
            let resolved_root_path = case_sensitivity.path_key(&resolved_root_file_name.as_path());
            resolved_root_file_names.insert(resolved_root_path.clone(), resolved_root_file_name);
            if let Some(root_path) = resolved_to_root.get(&resolved_root_path) {
                root_to_resolved.set(root_path.clone(), resolved_root_path.clone());
            } else {
                root_to_resolved.set(resolved_root_path.clone(), resolved_root_path.clone());
                root_file_names.insert(resolved_root_path.clone(), to_file_name(resolved_root));
            }
            if let Some(file_info) = file_info {
                resolved_root_file_infos.insert(resolved_root_path, file_info.clone());
            }
        };

        for root in &self.root {
            if !root.non_incremental.as_string().is_empty() {
                add_root(&root.non_incremental, None);
            } else if root.end == 0 {
                add_root(self.file_name(root.start), self.file_info(root.start));
            } else {
                for i in root.start..=root.end {
                    add_root(self.file_name(i), self.file_info(i));
                }
            }
        }

        BuildInfoRootInfoReader {
            resolved_root_file_infos,
            resolved_root_file_names,
            root_file_names,
            root_to_resolved,
        }
    }
}

fn get_build_info_file_names(
    paths: &[BuildInfoPath],
    build_info_directory: &RootedDirectoryPath,
) -> Vec<RootedFilePath> {
    paths
        .iter()
        .map(|path| build_info_directory.resolve_file(path.as_string()))
        .collect()
}

/// `type BuildInfoRootInfoReader struct`.
pub struct BuildInfoRootInfoReader {
    resolved_root_file_infos: rustc_hash::FxHashMap<PathKey, BuildInfoFileInfo>,
    resolved_root_file_names: rustc_hash::FxHashMap<PathKey, RootedFilePath>,
    root_file_names: rustc_hash::FxHashMap<PathKey, RootedFilePath>,
    root_to_resolved: OrderedMap<PathKey, PathKey>,
}

impl BuildInfoRootInfoReader {
    /// `(*BuildInfoRootInfoReader) GetBuildInfoFileInfo`.
    pub fn get_build_info_file_info(
        &self,
        input_file_path: &PathKey,
    ) -> (Option<&BuildInfoFileInfo>, Option<&RootedFilePath>) {
        if let Some(info) = self.resolved_root_file_infos.get(input_file_path) {
            return (
                Some(info),
                self.resolved_root_file_names.get(input_file_path),
            );
        }
        if let Some(resolved) = self.root_to_resolved.get(input_file_path) {
            return (
                self.resolved_root_file_infos.get(resolved),
                self.resolved_root_file_names.get(resolved),
            );
        }
        (None, None)
    }

    /// `(*BuildInfoRootInfoReader) Roots`.
    pub fn roots(&self) -> impl Iterator<Item = &PathKey> {
        self.root_to_resolved.keys()
    }

    /// `(*BuildInfoRootInfoReader) RootFileName`.
    pub fn root_file_name(&self, path: &PathKey) -> &RootedFilePath {
        self.root_file_names
            .get(path)
            .expect("root file name not found")
    }
}

/// `func ContentMapperIdentities` — the project's sorted mapper transform
/// identities. `None` means the compiler host has no configured content
/// mappers.
pub fn content_mapper_identities(
    project: Option<&Arc<dyn Project>>,
) -> Result<Vec<String>, tsc_contentmapper::host::Error> {
    match project {
        None => Ok(Vec::new()),
        Some(project) => project.identities(),
    }
}

/// `func IsBuildInfoFileNameDefaultLibrary`.
pub fn is_build_info_file_name_default_library(file_name: &BuildInfoPath) -> bool {
    !path_is_relative(file_name.as_string()) && !path_is_absolute(file_name.as_string())
}

/// `func ResolveBuildInfoFileName`.
pub fn resolve_build_info_file_name(
    file_name: &BuildInfoPath,
    build_info_directory: &RootedDirectoryPath,
    default_library_path: &RootedDirectoryPath,
) -> RootedFilePath {
    if is_build_info_file_name_default_library(file_name) {
        return default_library_path.resolve_file(file_name.as_string());
    }
    to_rooted_file_path(file_name.as_string(), build_info_directory)
}
