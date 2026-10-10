// Ported from tsc/internal/execute/incremental/snapshot.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::{Cell, OnceCell, RefCell};
use std::rc::Rc;
use std::sync::atomic::AtomicBool;

use tsc_ast::diagnostic::{
    DiagnosticFile, DiagnosticRef, RepopulateDiagnosticInfo, RepopulateDiagnosticKind,
    lock_diagnostic, new_diagnostic_from_serialized,
};
use tsc_ast::ids::NodeId;
use tsc_collections::{SyncMap, SyncSet};
use tsc_compiler::emit_host::WriteFileData;
use tsc_compiler::program::Program as CompilerProgram;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::TextRange;
use tsc_core::tristate::Tristate;
use tsc_diagnostics::Key;
use tsc_tspath::{CaseSensitivity, PathKey, RootedFilePath};

use crate::incremental::reference_map::ReferenceMap;

// ===========================================================================
// FileInfo.
// ===========================================================================

/// `type FileInfo struct` — stored per-file incremental state.
///
/// PORT: Go mutates `info.signature` on the stored `*FileInfo`; the Rust map
/// stores `Rc<RefCell<FileInfo>>` for the same aliased mutation.
#[derive(Clone, Default, Debug)]
pub struct FileInfo {
    pub(crate) version: String,
    pub(crate) signature: String,
    pub(crate) affects_global_scope: bool,
    pub(crate) implied_node_format: ResolutionMode,
}

impl FileInfo {
    /// `(*FileInfo) Version`.
    pub fn version(&self) -> &str {
        &self.version
    }
    /// `(*FileInfo) Signature`.
    pub fn signature(&self) -> &str {
        &self.signature
    }
    /// `(*FileInfo) AffectsGlobalScope`.
    pub fn affects_global_scope(&self) -> bool {
        self.affects_global_scope
    }
    /// `(*FileInfo) ImpliedNodeFormat`.
    pub fn implied_node_format(&self) -> ResolutionMode {
        self.implied_node_format
    }
}

/// `func ComputeHash` — xxh3 128-bit hash, hex encoded; when `hash_with_text`
/// the original text is appended for test-baseline comparisons.
pub fn compute_hash(text: &str, hash_with_text: bool) -> String {
    let hash_bytes = xxhash_rust::xxh3::xxh3_128(text.as_bytes()).to_be_bytes();
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut hash = String::with_capacity(32 + if hash_with_text { text.len() + 1 } else { 0 });
    for b in hash_bytes {
        hash.push(HEX[(b >> 4) as usize] as char);
        hash.push(HEX[(b & 0xf) as usize] as char);
    }
    if hash_with_text {
        hash.push('-');
        hash.push_str(text);
    }
    hash
}

// ===========================================================================
// FileEmitKind.
// ===========================================================================

/// `type FileEmitKind uint32`.
pub type FileEmitKind = i32;

pub const FILE_EMIT_KIND_NONE: FileEmitKind = 0;
/// Emit js file.
pub const FILE_EMIT_KIND_JS: FileEmitKind = 1 << 0;
/// Emit js.map file.
pub const FILE_EMIT_KIND_JS_MAP: FileEmitKind = 1 << 1;
/// Emit inline source map in js file.
pub const FILE_EMIT_KIND_JS_INLINE_MAP: FileEmitKind = 1 << 2;
/// Emit dts errors.
pub const FILE_EMIT_KIND_DTS_ERRORS: FileEmitKind = 1 << 3;
/// Emit d.ts file.
pub const FILE_EMIT_KIND_DTS_EMIT: FileEmitKind = 1 << 4;
/// Emit d.ts.map file.
pub const FILE_EMIT_KIND_DTS_MAP: FileEmitKind = 1 << 5;

pub const FILE_EMIT_KIND_DTS: FileEmitKind = FILE_EMIT_KIND_DTS_ERRORS | FILE_EMIT_KIND_DTS_EMIT;
pub const FILE_EMIT_KIND_ALL_JS: FileEmitKind =
    FILE_EMIT_KIND_JS | FILE_EMIT_KIND_JS_MAP | FILE_EMIT_KIND_JS_INLINE_MAP;
pub const FILE_EMIT_KIND_ALL_DTS_EMIT: FileEmitKind =
    FILE_EMIT_KIND_DTS_EMIT | FILE_EMIT_KIND_DTS_MAP;
pub const FILE_EMIT_KIND_ALL_DTS: FileEmitKind = FILE_EMIT_KIND_DTS | FILE_EMIT_KIND_DTS_MAP;
pub const FILE_EMIT_KIND_ALL: FileEmitKind = FILE_EMIT_KIND_ALL_JS | FILE_EMIT_KIND_ALL_DTS;

/// `func GetFileEmitKind`.
pub fn get_file_emit_kind(options: &CompilerOptions) -> FileEmitKind {
    let mut result = FILE_EMIT_KIND_JS;
    if options.source_map.is_true() {
        result |= FILE_EMIT_KIND_JS_MAP;
    }
    if options.inline_source_map.is_true() {
        result |= FILE_EMIT_KIND_JS_INLINE_MAP;
    }
    if options.get_emit_declarations() {
        result |= FILE_EMIT_KIND_DTS;
    }
    if options.declaration_map.is_true() {
        result |= FILE_EMIT_KIND_DTS_MAP;
    }
    if options.emit_declaration_only.is_true() {
        result &= FILE_EMIT_KIND_ALL_DTS;
    }
    result
}

/// `func getPendingEmitKindWithOptions`.
pub fn get_pending_emit_kind_with_options(
    options: &CompilerOptions,
    old_options: &CompilerOptions,
) -> FileEmitKind {
    let old_emit_kind = get_file_emit_kind(old_options);
    let new_emit_kind = get_file_emit_kind(options);
    get_pending_emit_kind(new_emit_kind, old_emit_kind)
}

/// `func getPendingEmitKind`.
pub fn get_pending_emit_kind(emit_kind: FileEmitKind, old_emit_kind: FileEmitKind) -> FileEmitKind {
    if old_emit_kind == emit_kind {
        return FILE_EMIT_KIND_NONE;
    }
    if old_emit_kind == 0 || emit_kind == 0 {
        return emit_kind;
    }
    let diff = old_emit_kind ^ emit_kind;
    let mut result = FILE_EMIT_KIND_NONE;
    // If there is diff in js emit, pending emit is js emit flags
    if (diff & FILE_EMIT_KIND_ALL_JS) != 0 {
        result |= emit_kind & FILE_EMIT_KIND_ALL_JS;
    }
    // If dts errors pending, add dts errors flag
    if (diff & FILE_EMIT_KIND_DTS_ERRORS) != 0 {
        result |= emit_kind & FILE_EMIT_KIND_ALL_DTS;
    }
    // If there is diff in dts emit, pending emit is dts emit flags
    if (diff & FILE_EMIT_KIND_ALL_DTS_EMIT) != 0 {
        result |= emit_kind & FILE_EMIT_KIND_ALL_DTS_EMIT;
    }
    result
}

// ===========================================================================
// emitSignature.
// ===========================================================================

/// `type emitSignature struct` — signature (hash of d.ts emitted) is a string
/// if emitted with the same d.ts.map option as the compiler options indicate,
/// otherwise a tuple of strings.
#[derive(Clone, Default, Debug)]
pub struct EmitSignature {
    pub signature: String,
    pub signature_with_different_options: Option<Vec<String>>,
}

impl EmitSignature {
    /// `(*emitSignature) getNewEmitSignature` — convert the emit signature
    /// based on old and new options. If the d.ts map options differ the
    /// format is swapped, otherwise it is used as is.
    pub fn get_new_emit_signature(
        &self,
        old_options: &CompilerOptions,
        new_options: &CompilerOptions,
    ) -> EmitSignature {
        if old_options.declaration_map.is_true() == new_options.declaration_map.is_true() {
            return self.clone();
        }
        match &self.signature_with_different_options {
            None => EmitSignature {
                signature: String::new(),
                signature_with_different_options: Some(vec![self.signature.clone()]),
            },
            Some(different) => EmitSignature {
                signature: different[0].clone(),
                signature_with_different_options: None,
            },
        }
    }
}

// ===========================================================================
// buildInfoDiagnosticWithFileName / DiagnosticsOrBuildInfoDiagnosticsWithFileName.
// ===========================================================================

/// `type buildInfoDiagnosticWithFileName struct`.
#[derive(Clone, Debug)]
pub struct BuildInfoDiagnosticWithFileName {
    /// File name if it is for a file other than the one it is stored for.
    pub file: PathKey,
    pub no_file: bool,
    pub pos: i32,
    pub end: i32,
    pub code: i32,
    pub category: tsc_diagnostics::Category,
    pub source: String,
    pub message_text: String,
    pub message_key: Key,
    pub message_args: Vec<String>,
    pub message_chain: Vec<BuildInfoDiagnosticWithFileName>,
    pub related_information: Vec<BuildInfoDiagnosticWithFileName>,
    pub reports_unnecessary: bool,
    pub reports_deprecated: bool,
    pub skipped_on_no_emit: bool,
    pub repopulate_info: Option<RepopulateDiagnosticInfo>,
}

/// Go's zero-value `Category` is `Warning` (category 0).
impl Default for BuildInfoDiagnosticWithFileName {
    fn default() -> Self {
        Self {
            file: PathKey::default(),
            no_file: false,
            pos: 0,
            end: 0,
            code: 0,
            category: tsc_diagnostics::Category::Warning,
            source: String::new(),
            message_text: String::new(),
            message_key: "",
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

/// `type DiagnosticsOrBuildInfoDiagnosticsWithFileName struct`.
///
/// PORT: `diagnostics` is `Option<Vec<..>>` so `None` mirrors Go's nil slice
/// ("not yet converted"); `Some(vec![])` is a converted-but-empty list, which
/// Go distinguishes from nil.
#[derive(Default)]
pub struct DiagnosticsOrBuildInfoDiagnosticsWithFileName {
    pub diagnostics: Option<Vec<DiagnosticRef>>,
    pub build_info_diagnostics: Vec<BuildInfoDiagnosticWithFileName>,
}

fn diagnostic_file_for(p: &CompilerProgram, file: Option<NodeId>) -> Option<DiagnosticFile> {
    file.map(|f| DiagnosticFile::from_node(f, &p.arena_of(f)))
}

impl BuildInfoDiagnosticWithFileName {
    /// `(*buildInfoDiagnosticWithFileName) toDiagnostic`.
    pub fn to_diagnostic(&self, p: &CompilerProgram, file: Option<NodeId>) -> DiagnosticRef {
        let file_for_diagnostic = if !self.file.as_string().is_empty() {
            p.get_source_file_by_path(&self.file)
        } else if !self.no_file {
            file
        } else {
            None
        };

        if self.repopulate_info.is_some() {
            return repopulate_diagnostic_chain(self, p, file_for_diagnostic);
        }

        let message_chain = self
            .message_chain
            .iter()
            .map(|msg| msg.to_diagnostic(p, file_for_diagnostic))
            .collect();
        let related_information = self
            .related_information
            .iter()
            .map(|info| info.to_diagnostic(p, file_for_diagnostic))
            .collect();
        let diagnostic = new_diagnostic_from_serialized(
            diagnostic_file_for(p, file_for_diagnostic),
            TextRange::new(self.pos, self.end),
            self.code,
            self.category,
            self.message_key,
            self.message_args.clone(),
            message_chain,
            related_information,
            self.reports_unnecessary,
            self.reports_deprecated,
            self.skipped_on_no_emit,
        );
        if !self.source.is_empty() || !self.message_text.is_empty() {
            lock_diagnostic(&diagnostic)
                .set_external_data(self.source.clone(), self.message_text.clone());
        }
        diagnostic
    }

    /// `(*buildInfoDiagnosticWithFileName) toDiagnosticWithoutRepopulate`.
    fn to_diagnostic_without_repopulate(
        &self,
        p: &CompilerProgram,
        file: Option<NodeId>,
    ) -> DiagnosticRef {
        let message_chain = self
            .message_chain
            .iter()
            .map(|msg| msg.to_diagnostic(p, file))
            .collect();
        let related_information = self
            .related_information
            .iter()
            .map(|info| info.to_diagnostic(p, file))
            .collect();
        new_diagnostic_from_serialized(
            diagnostic_file_for(p, file),
            TextRange::new(self.pos, self.end),
            self.code,
            self.category,
            self.message_key,
            self.message_args.clone(),
            message_chain,
            related_information,
            self.reports_unnecessary,
            self.reports_deprecated,
            self.skipped_on_no_emit,
        )
    }
}

/// `func repopulateDiagnosticChain` — recomputes a diagnostic chain entry that
/// depends on program state which may have changed between incremental builds.
pub(crate) fn repopulate_diagnostic_chain(
    b: &BuildInfoDiagnosticWithFileName,
    p: &CompilerProgram,
    file: Option<NodeId>,
) -> DiagnosticRef {
    let info = b.repopulate_info.as_ref().expect("repopulate info");
    if info.kind == RepopulateDiagnosticKind::ModeMismatch {
        repopulate_mode_mismatch_chain(b, p, file)
    } else if info.kind == RepopulateDiagnosticKind::ModuleNotFound {
        repopulate_module_not_found_chain(b, p, file, info)
    } else {
        // Fall back to using the stored (possibly stale) data.
        b.to_diagnostic_without_repopulate(p, file)
    }
}

fn repopulate_mode_mismatch_chain(
    b: &BuildInfoDiagnosticWithFileName,
    p: &CompilerProgram,
    file: Option<NodeId>,
) -> DiagnosticRef {
    let Some(file_id) = file else {
        return b.to_diagnostic_without_repopulate(p, file);
    };

    let details = {
        let nodes = p.arena_of(file_id);
        tsc_checker::utilities::create_mode_mismatch_details(p, nodes[file_id].as_source_file())
    };

    let next_chain = b
        .message_chain
        .iter()
        .map(|msg| msg.to_diagnostic(p, file))
        .collect();

    new_diagnostic_from_serialized(
        diagnostic_file_for(p, file),
        TextRange::new(b.pos, b.end),
        details.message.code(),
        details.message.category(),
        details.message.key(),
        details.args,
        next_chain,
        Vec::new(),
        false,
        false,
        false,
    )
}

fn repopulate_module_not_found_chain(
    b: &BuildInfoDiagnosticWithFileName,
    p: &CompilerProgram,
    file: Option<NodeId>,
    info: &RepopulateDiagnosticInfo,
) -> DiagnosticRef {
    let Some(file_id) = file else {
        return b.to_diagnostic_without_repopulate(p, file);
    };

    let package_name = if !info.package_name.is_empty() {
        info.package_name.clone()
    } else {
        info.module_reference.clone()
    };

    let details = {
        let nodes = p.arena_of(file_id);
        tsc_checker::utilities::create_module_not_found_chain(
            p,
            nodes[file_id].as_source_file(),
            &info.module_reference,
            info.mode,
            &package_name,
        )
    };

    let next_chain = b
        .message_chain
        .iter()
        .map(|msg| msg.to_diagnostic(p, file))
        .collect();

    new_diagnostic_from_serialized(
        diagnostic_file_for(p, file),
        TextRange::new(b.pos, b.end),
        details.message.code(),
        details.message.category(),
        details.message.key(),
        details.args,
        next_chain,
        Vec::new(),
        false,
        false,
        false,
    )
}

impl DiagnosticsOrBuildInfoDiagnosticsWithFileName {
    /// `(*DiagnosticsOrBuildInfoDiagnosticsWithFileName) getDiagnostics` —
    /// converts and caches the diagnostics on first use.
    pub fn get_diagnostics(
        &mut self,
        p: &CompilerProgram,
        file: Option<NodeId>,
    ) -> &[DiagnosticRef] {
        if self.diagnostics.is_none() {
            // Convert and cache the diagnostics.
            self.diagnostics = Some(
                self.build_info_diagnostics
                    .iter()
                    .map(|diag| diag.to_diagnostic(p, file))
                    .collect(),
            );
        }
        self.diagnostics.as_deref().unwrap_or(&[])
    }
}

// ===========================================================================
// snapshot.
// ===========================================================================

/// `type snapshot struct` — the incremental program state. Fields marked
/// "serialized" in Go correspond to `BuildInfo` members; the rest track
/// intra-build state.
///
/// PORT: Go stores mutable scalars on `*snapshot` and mutates them through
/// shared pointers; the Rust port wraps the snapshot in `Rc` and uses
/// interior mutability (`Cell`/`RefCell`/`OnceCell`/`AtomicBool`) for the same
/// aliased writes. `semantic_diagnostics_per_file` is an `Rc<SyncMap>` because
/// `TestingData` aliases the same map (Go takes `&snapshot.semanticDiagnosticsPerFile`).
#[derive(Default)]
pub struct Snapshot {
    // These are the fields that get serialized:
    /// Information of the file e.g. its version, signature etc.
    pub file_infos: SyncMap<PathKey, Rc<RefCell<FileInfo>>>,
    pub options: Rc<CompilerOptions>,
    /// Contains the map of ReferencedSet = referenced files of the file if
    /// module emit is enabled.
    pub referenced_map: ReferenceMap,
    /// Cache of semantic diagnostics for files keyed by path.
    pub semantic_diagnostics_per_file:
        Rc<SyncMap<PathKey, Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>>>>,
    /// Cache of dts emit diagnostics for files keyed by path.
    pub emit_diagnostics_per_file:
        SyncMap<PathKey, Rc<RefCell<DiagnosticsOrBuildInfoDiagnosticsWithFileName>>>,
    /// Set keyed by source file path of files that have changed.
    pub changed_files_set: SyncSet<PathKey>,
    /// Files pending to be emitted.
    pub affected_files_pending_emit: SyncMap<PathKey, FileEmitKind>,
    /// Name of the file whose dts was the latest to change.
    pub latest_changed_dts_file: RefCell<RootedFilePath>,
    /// Hash of d.ts emitted for the file; used to track when d.ts emit changes.
    pub emit_signatures: SyncMap<PathKey, Rc<EmitSignature>>,
    /// Recorded if program had errors that need to be reported even with
    /// --noCheck.
    pub has_errors: Cell<Tristate>,
    /// Recorded if program had semantic errors — only for non-incremental
    /// builds.
    pub has_semantic_errors: Cell<bool>,
    /// If semantic diagnostic check is pending.
    pub check_pending: Cell<bool>,
    /// Looked-up package.json files.
    ///
    /// PORT: `Option` mirrors Go's nil-able slice — `None` means "not yet
    /// computed by `ensurePackageJsonsForState`".
    pub package_jsons: RefCell<Option<Vec<RootedFilePath>>>,
    pub missing_package_jsons: RefCell<Option<Vec<RootedFilePath>>>,

    // Additional fields that are not serialized but needed to track state:
    /// True if build info emit is pending.
    pub build_info_emit_pending: AtomicBool,
    pub has_errors_from_old_state: Tristate,
    pub has_semantic_errors_from_old_state: bool,
    /// Cache of all files excluding default library files for the current
    /// program (`allFilesExcludingDefaultLibraryFileOnce` +
    /// `allFilesExcludingDefaultLibraryFile`).
    all_files_excluding_default_library_file: OnceCell<Vec<NodeId>>,
    pub package_jsons_from_old_state: Option<Vec<RootedFilePath>>,
    pub missing_package_jsons_from_old_state: Option<Vec<RootedFilePath>>,
    pub has_changed_dts_file: Cell<bool>,
    pub has_emit_diagnostics: Cell<bool>,

    /// Used with testing to add text of hash for better comparison.
    pub hash_with_text: bool,
}

impl Snapshot {
    /// `(*snapshot) addFileToChangeSet`.
    pub fn add_file_to_change_set(&self, file_path: PathKey) {
        self.changed_files_set.add(file_path);
        self.build_info_emit_pending
            .store(true, std::sync::atomic::Ordering::SeqCst);
    }

    /// `(*snapshot) addFileToAffectedFilesPendingEmit`.
    pub fn add_file_to_affected_files_pending_emit(
        &self,
        file_path: PathKey,
        emit_kind: FileEmitKind,
    ) {
        let existing_kind = self
            .affected_files_pending_emit
            .load(&file_path)
            .unwrap_or_default();
        self.affected_files_pending_emit
            .store(file_path.clone(), existing_kind | emit_kind);
        if emit_kind & FILE_EMIT_KIND_DTS_ERRORS != 0 {
            self.emit_diagnostics_per_file.delete(&file_path);
        }
        self.build_info_emit_pending
            .store(true, std::sync::atomic::Ordering::SeqCst);
    }

    /// `(*snapshot) getAllFilesExcludingDefaultLibraryFile`.
    pub fn get_all_files_excluding_default_library_file(
        &self,
        program: &CompilerProgram,
        first_source_file: Option<NodeId>,
    ) -> &Vec<NodeId> {
        self.all_files_excluding_default_library_file
            .get_or_init(|| {
                let files = program.source_files_slice();
                let mut result = Vec::with_capacity(files.len());
                let mut add_source_file = |file: NodeId| {
                    let path_key = {
                        let nodes = program.arena_of(file);
                        nodes[file].as_source_file().path_key().clone()
                    };
                    if !program.is_source_file_default_library(&path_key) {
                        result.push(file);
                    }
                };
                if let Some(first) = first_source_file {
                    add_source_file(first);
                }
                for &file in files {
                    if Some(file) != first_source_file {
                        add_source_file(file);
                    }
                }
                result
            })
    }

    /// `(*snapshot) computeSignatureWithDiagnostics`.
    pub fn compute_signature_with_diagnostics(
        &self,
        program: &CompilerProgram,
        file: NodeId,
        text: &str,
        data: &WriteFileData,
    ) -> String {
        let file_name = {
            let nodes = program.arena_of(file);
            nodes[file].as_source_file().file_name().clone()
        };
        let mut builder = get_text_handling_source_map_for_signature(text, data).to_string();
        for diag in &data.diagnostics {
            diagnostic_to_string_builder(diag, file, &file_name, &mut builder);
        }
        self.compute_hash(&builder)
    }

    /// `(*snapshot) computeHash`.
    pub fn compute_hash(&self, text: &str) -> String {
        compute_hash(text, self.hash_with_text)
    }

    /// `(*snapshot) canUseIncrementalState`.
    pub fn can_use_incremental_state(&self) -> bool {
        if !self.options.is_incremental() && self.options.build.is_true() {
            // If not incremental build (with tsc -b), we don't need to track
            // state except diagnostics per file so we can use it.
            return false;
        }
        true
    }
}

/// `func getTextHandlingSourceMapForSignature`.
pub fn get_text_handling_source_map_for_signature<'a>(
    text: &'a str,
    data: &WriteFileData,
) -> &'a str {
    if data.source_map_url_pos != -1 {
        return &text[..data.source_map_url_pos as usize];
    }
    text
}

/// `func diagnosticToStringBuilder`.
fn diagnostic_to_string_builder(
    diagnostic: &DiagnosticRef,
    file: NodeId,
    file_name: &RootedFilePath,
    builder: &mut String,
) {
    let d = lock_diagnostic(diagnostic);
    builder.push('\n');
    // Go compares `diagnostic.File() != file` on `*SourceFile` pointers; the
    // `DiagnosticFile.node` arena id is the port's file identity.
    let diagnostic_file_node = d.file().and_then(|f| f.node);
    if diagnostic_file_node != Some(file) {
        // Go: `diagnostic.File().FileName()` — nil file would panic there;
        // this branch is only reachable when the diagnostic has a file.
        let diagnostic_file_name = d.file().map(|f| f.file_name.clone()).unwrap_or_default();
        if let Some(relative_path) = CaseSensitivity::CaseInsensitive
            .relative_path_from_file(file_name, &diagnostic_file_name)
        {
            builder.push_str(relative_path.as_module_specifier().as_string());
        } else {
            builder.push_str(diagnostic_file_name.as_string());
        }
    }
    if d.file().is_some() {
        builder.push_str(&format!("({},{}): ", d.pos(), d.len()));
    }
    builder.push_str(d.category().name());
    builder.push_str(&format!("{}: ", d.code()));
    builder.push_str(d.message_key());
    builder.push('\n');
    for arg in d.message_args() {
        builder.push_str(arg);
        builder.push('\n');
    }
    let message_chain: Vec<DiagnosticRef> = d.message_chain().to_vec();
    let related_information: Vec<DiagnosticRef> = d.related_information().to_vec();
    drop(d);
    for chain in &message_chain {
        diagnostic_to_string_builder(chain, file, file_name, builder);
    }
    for info in &related_information {
        diagnostic_to_string_builder(info, file, file_name, builder);
    }
}
