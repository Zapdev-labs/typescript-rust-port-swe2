// Ported from tsc/internal/ast/diagnostic.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Diagnostic, DiagnosticsCollection, and the diagnostic ordering/equality
// helpers.
//
// Pointer model: Go `*Diagnostic` is a shared mutable heap object —
// `DiagnosticsCollection.Add` returns the canonical diagnostic which
// callers keep mutating, and `d1 == d2` pointer checks are load-bearing in
// `EqualDiagnostics`/`CompareDiagnostics` (they terminate recursion for
// self-referential chains and message chains). Rust uses
// `DiagnosticRef = Arc<Mutex<Diagnostic>>`: `Arc::ptr_eq` is `d1 == d2`,
// and the mutex keeps `DiagnosticsCollection` `Send + Sync`, matching the
// `sync.Mutex` guard in Go. A diagnostic's lock is never held while another
// diagnostic's is taken — the equality/ordering helpers snapshot fields
// into `DiagnosticView` — so there is no lock ordering to deadlock.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::sync::{Arc, Mutex, MutexGuard};

use rustc_hash::FxHashMap;
use tsc_collections::Set;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::text::{TextPos, TextRange};
use tsc_diagnostics::{Category, Key, Message, new_adhoc_message, stringify_args};
use tsc_locale::Locale;
use tsc_spanmap::SpanMap;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::ast::Node;
use crate::ids::NodeId;

/// `type RepopulateDiagnosticKind int` — indicates the kind of repopulation
/// for a diagnostic chain entry.
///
/// PORT: open int set → newtype, matching the `spanmap::Kind`/`Feature`
/// precedent (Go's zero value 0 names no constant but is a legal value).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RepopulateDiagnosticKind(pub i32);

#[allow(non_upper_case_globals)]
impl RepopulateDiagnosticKind {
    /// `RepopulateModeMismatch`
    pub const ModeMismatch: RepopulateDiagnosticKind = RepopulateDiagnosticKind(1);
    /// `RepopulateModuleNotFound`
    pub const ModuleNotFound: RepopulateDiagnosticKind = RepopulateDiagnosticKind(2);
}

/// `type RepopulateDiagnosticInfo struct` — information needed to recompute
/// a diagnostic chain entry during incremental builds when the program
/// state may have changed.
///
/// PORT: Go stores `*RepopulateDiagnosticInfo`; the info is never mutated
/// after `SetRepopulateInfo`, so a plain `Option` value (cloned by callers
/// that need to retain it) preserves the semantics.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct RepopulateDiagnosticInfo {
    pub kind: RepopulateDiagnosticKind,
    pub module_reference: String,
    /// `core.ResolutionMode` is a Go alias for `ModuleKind`.
    pub mode: ResolutionMode,
    pub package_name: String,
}

// DiagnosticFile

/// The source file a diagnostic is located in.
///
/// PORT: Go stores `file *SourceFile` — a live pointer into the AST. The
/// pieces diagnostics actually read are `PathKey()` (collection bucketing,
/// `diagnosticLocationKey`), `FileName()` (ordering), and
/// `Text()`/`OriginalText()`/`SpanMap()` (the `displayMessageArgs` alias
/// substitution). In Rust a `SourceFile` is `NodeData` inside the `nodes`
/// arena and does not yet carry `parseOptions`/`PathKey` or
/// `contentMapperInfo`, so diagnostics store this cloneable handle instead:
/// `node` is the arena address of the file node (resolve it through `nodes`
/// for line maps and other live data), and the remaining fields are the
/// file attributes diagnostics read directly. Go fixes all of them before
/// the file is published (`parseOptions` at construction,
/// `contentMapperInfo` via `SetContentMapperInfo`), so the snapshot cannot
/// go stale.
#[derive(Clone, Default)]
pub struct DiagnosticFile {
    /// `NodeId` of the `Kind::SourceFile` node — the arena address of the
    /// `*SourceFile` Go would store. `None` for handles built without an
    /// arena (tests, external diagnostics).
    pub node: Option<NodeId>,
    /// `file.FileName()` — `parseOptions.FileName`.
    pub file_name: RootedFilePath,
    /// `file.PathKey()` — `parseOptions.PathKey`; the canonical key
    /// `DiagnosticsCollection` groups by.
    pub path_key: PathKey,
    /// `file.Text()` — the file's (possibly virtual) text. Read only by
    /// `display_message_args`.
    pub text: Arc<str>,
    /// `file.OriginalText()` — the untransformed text; equals `text` when the
    /// file is not content-mapped.
    pub original_text: Arc<str>,
    /// `file.SpanMap()` — `None` for unmapped files (Go's map is nil-safe,
    /// so `None` mirrors nil). Always `None` until `SourceFile` carries
    /// `content_mapper_info` — contentmapper is deferred (PORTING-NOTES).
    pub span_map: Option<Arc<SpanMap>>,
}

impl DiagnosticFile {
    /// Builds the handle for a parsed `SourceFile` node. `path_key` is
    /// `file.PathKey()`: the Rust `SourceFile` does not store
    /// `parseOptions` yet, so the caller supplies the key it computed when
    /// loading the file.
    ///
    /// Until `SourceFile` gains `content_mapper_info`, `OriginalText()` is
    /// `Text()` and `SpanMap()` is nil — the same values Go's accessors
    /// return for an unmapped file.
    pub fn from_node(node: NodeId, nodes: &[Node], path_key: PathKey) -> DiagnosticFile {
        let d = nodes[node].as_source_file();
        DiagnosticFile {
            node: Some(node),
            file_name: RootedFilePath::from(d.file_name.clone()),
            path_key,
            text: Arc::from(d.text.as_str()),
            original_text: Arc::from(d.text.as_str()),
            span_map: None,
        }
    }
}

// Diagnostic

/// `*Diagnostic` — a shared, mutable diagnostic (see module docs).
pub type DiagnosticRef = Arc<Mutex<Diagnostic>>;

/// Locks a `DiagnosticRef`. Go's `sync.Mutex` does not poison on panic;
/// recovering the guard with `into_inner` mirrors Go's `defer`-unlocked
/// mutex that remains usable after a panicking caller.
pub fn lock_diagnostic(d: &DiagnosticRef) -> MutexGuard<'_, Diagnostic> {
    d.lock().unwrap_or_else(|e| e.into_inner())
}

/// `type Diagnostic struct` — Go's unexported fields stay private behind
/// the same accessor/setter methods.
#[derive(Clone)]
pub struct Diagnostic {
    file: Option<DiagnosticFile>,
    loc: TextRange,
    code: i32,
    category: Category,
    /// source, when non-empty, is a custom prefix (e.g. a content mapper's name)
    /// shown instead of "TS" before the code. It marks the diagnostic as coming
    /// from an external source whose ranges point into the file's original,
    /// untransformed text.
    source: String,
    /// Original message; may be nil.
    message: Option<&'static Message>,
    /// messageText is an already-localized message used when message is nil,
    /// e.g. a diagnostic deserialized from an external process that owns its
    /// own localization.
    message_text: String,
    message_key: Key,
    message_args: Vec<String>,
    message_chain: Vec<DiagnosticRef>,
    related_information: Vec<DiagnosticRef>,
    reports_unnecessary: bool,
    reports_deprecated: bool,
    skipped_on_no_emit: bool,
    repopulate_info: Option<RepopulateDiagnosticInfo>,
}

impl Default for Diagnostic {
    /// The Go `&Diagnostic{}` zero value.
    fn default() -> Diagnostic {
        Diagnostic {
            file: None,
            loc: TextRange::default(),
            code: 0,
            category: Category::Warning,
            source: String::new(),
            message: None,
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

impl Diagnostic {
    /// `d.File()` — `None` is Go's nil `*SourceFile`.
    pub fn file(&self) -> Option<&DiagnosticFile> {
        self.file.as_ref()
    }
    /// `d.Pos()`
    pub fn pos(&self) -> i32 {
        self.loc.pos()
    }
    /// `d.End()`
    pub fn end(&self) -> i32 {
        self.loc.end()
    }
    /// `d.Len()`
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> i32 {
        self.loc.len()
    }
    /// `d.Loc()`
    pub fn loc(&self) -> TextRange {
        self.loc
    }
    /// `d.Code()`
    pub fn code(&self) -> i32 {
        self.code
    }
    /// `d.Category()`
    pub fn category(&self) -> Category {
        self.category
    }
    /// `d.Source()`
    pub fn source(&self) -> &str {
        &self.source
    }
    /// `d.MessageText()`
    pub fn message_text(&self) -> &str {
        &self.message_text
    }
    /// `d.MessageKey()`
    pub fn message_key(&self) -> Key {
        self.message_key
    }
    /// `d.MessageArgs()`
    pub fn message_args(&self) -> &[String] {
        &self.message_args
    }
    /// `d.MessageChain()`
    pub fn message_chain(&self) -> &[DiagnosticRef] {
        &self.message_chain
    }
    /// `d.RelatedInformation()`
    pub fn related_information(&self) -> &[DiagnosticRef] {
        &self.related_information
    }
    /// `d.ReportsUnnecessary()`
    pub fn reports_unnecessary(&self) -> bool {
        self.reports_unnecessary
    }
    /// `d.ReportsDeprecated()`
    pub fn reports_deprecated(&self) -> bool {
        self.reports_deprecated
    }
    /// `d.SkippedOnNoEmit()`
    pub fn skipped_on_no_emit(&self) -> bool {
        self.skipped_on_no_emit
    }
    /// `d.RepopulateInfo()` — `None` is Go's nil.
    pub fn repopulate_info(&self) -> Option<&RepopulateDiagnosticInfo> {
        self.repopulate_info.as_ref()
    }

    /// `d.SetFile(file)`
    pub fn set_file(&mut self, file: Option<DiagnosticFile>) {
        self.file = file;
    }
    /// `d.SetLocation(loc)`
    pub fn set_location(&mut self, loc: TextRange) {
        self.loc = loc;
    }
    /// `d.SetCategory(category)`
    pub fn set_category(&mut self, category: Category) {
        self.category = category;
    }
    /// `d.SetSkippedOnNoEmit()`
    pub fn set_skipped_on_no_emit(&mut self) {
        self.skipped_on_no_emit = true;
    }
    /// `d.SetRepopulateInfo(info)`
    pub fn set_repopulate_info(&mut self, info: Option<RepopulateDiagnosticInfo>) {
        self.repopulate_info = info;
    }

    /// `d.SetExternalData(source, messageText)` — returns `&mut Self` for
    /// chaining, like Go returning `d`.
    pub fn set_external_data(&mut self, source: String, message_text: String) -> &mut Self {
        self.source = source;
        self.message_text = message_text;
        self
    }

    /// `d.SetMessageChain(messageChain)`
    pub fn set_message_chain(&mut self, message_chain: Vec<DiagnosticRef>) -> &mut Self {
        self.message_chain = message_chain;
        self
    }

    /// `d.AddMessageChain(messageChain)` — `None` is Go's nil (a no-op).
    pub fn add_message_chain(&mut self, message_chain: Option<DiagnosticRef>) -> &mut Self {
        if let Some(message_chain) = message_chain {
            self.message_chain.push(message_chain);
        }
        self
    }

    /// `d.SetRelatedInfo(relatedInformation)`
    pub fn set_related_info(&mut self, related_information: Vec<DiagnosticRef>) -> &mut Self {
        self.related_information = related_information;
        self
    }

    /// `d.AddRelatedInfo(relatedInformation)` — `None` is Go's nil (a no-op).
    pub fn add_related_info(&mut self, related_information: Option<DiagnosticRef>) -> &mut Self {
        if let Some(related_information) = related_information {
            self.related_information.push(related_information);
        }
        self
    }

    /// `d.Clone()` — a shallow copy. Go copies the struct and shares the
    /// slice backing; `Vec<DiagnosticRef>` clones share the same `Arc`
    /// elements, which is the shared-element half of Go's semantics.
    pub fn clone_diagnostic(&self) -> DiagnosticRef {
        Arc::new(Mutex::new(self.clone()))
    }

    /// `d.Localize(locale)`
    pub fn localize(&self, locale: &Locale) -> String {
        if self.message.is_none() && !self.message_text.is_empty() {
            return self.message_text.clone();
        }
        tsc_diagnostics::localize(
            locale,
            self.message,
            self.message_key,
            &self.display_message_args(),
        )
    }

    /// `d.displayMessageArgs()` — substitutes the original text for a
    /// complete alias span when a diagnostic argument exactly matches the
    /// virtual alias. Stored arguments remain unchanged for code fixes and
    /// serialization.
    ///
    /// PORT: returns `Cow` — `Borrowed(&self.message_args)` is Go's
    /// `return d.messageArgs` (the same slice), `Owned` is Go's cloned
    /// `result`.
    fn display_message_args(&self) -> Cow<'_, [String]> {
        let Some(file) = &self.file else {
            return Cow::Borrowed(&self.message_args);
        };
        if !self.source.is_empty() {
            return Cow::Borrowed(&self.message_args);
        }
        let Some(segment) = SpanMap::alias_for_virtual_span(file.span_map.as_deref(), self.loc)
        else {
            return Cow::Borrowed(&self.message_args);
        };
        let virtual_text = file.text.as_bytes();
        let original_text = file.original_text.as_bytes();
        if segment.virtual_start < 0
            || segment.virtual_end > virtual_text.len() as TextPos
            || segment.original_start < 0
            || segment.original_end > original_text.len() as TextPos
        {
            return Cow::Borrowed(&self.message_args);
        }
        // PORT: Go slices strings at byte offsets (possibly mid-UTF-8);
        // comparing and substituting bytes preserves that. A non-UTF-8
        // original span is lossy-decoded — Rust `String` cannot hold
        // arbitrary bytes.
        let virtual_name =
            &virtual_text[segment.virtual_start as usize..segment.virtual_end as usize];
        let original_name =
            &original_text[segment.original_start as usize..segment.original_end as usize];
        let mut result: Option<Vec<String>> = None;
        for (i, arg) in self.message_args.iter().enumerate() {
            if arg.as_bytes() != virtual_name {
                continue;
            }
            let result = result.get_or_insert_with(|| self.message_args.clone());
            result[i] = String::from_utf8_lossy(original_name).into_owned();
        }
        match result {
            Some(result) => Cow::Owned(result),
            None => Cow::Borrowed(&self.message_args),
        }
    }
}

/// For debugging only. `func (d *Diagnostic) String() string`.
impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.message.is_none() && !self.message_text.is_empty() {
            return f.write_str(&self.message_text);
        }
        f.write_str(&tsc_diagnostics::localize(
            &tsc_locale::DEFAULT,
            self.message,
            self.message_key,
            &self.display_message_args(),
        ))
    }
}

/// `func NewDiagnosticFromSerialized(...) *Diagnostic`
#[allow(clippy::too_many_arguments)]
pub fn new_diagnostic_from_serialized(
    file: Option<DiagnosticFile>,
    loc: TextRange,
    code: i32,
    category: Category,
    message_key: Key,
    message_args: Vec<String>,
    message_chain: Vec<DiagnosticRef>,
    related_information: Vec<DiagnosticRef>,
    reports_unnecessary: bool,
    reports_deprecated: bool,
    skipped_on_no_emit: bool,
) -> DiagnosticRef {
    Arc::new(Mutex::new(Diagnostic {
        file,
        loc,
        code,
        category,
        message_key,
        message_args,
        message_chain,
        related_information,
        reports_unnecessary,
        reports_deprecated,
        skipped_on_no_emit,
        ..Default::default()
    }))
}

/// `func NewDiagnosticFromText(...) *Diagnostic`
#[allow(clippy::too_many_arguments)]
pub fn new_diagnostic_from_text(
    file: Option<DiagnosticFile>,
    loc: TextRange,
    code: i32,
    category: Category,
    text: String,
    message_chain: Vec<DiagnosticRef>,
    related_information: Vec<DiagnosticRef>,
    reports_unnecessary: bool,
    reports_deprecated: bool,
) -> DiagnosticRef {
    Arc::new(Mutex::new(Diagnostic {
        file,
        loc,
        code,
        category,
        message: Some(new_adhoc_message(text)),
        message_chain,
        related_information,
        reports_unnecessary,
        reports_deprecated,
        ..Default::default()
    }))
}

/// `func NewDiagnostic(file *SourceFile, loc core.TextRange, message *diagnostics.Message, args ...any) *Diagnostic`
pub fn new_diagnostic<T: fmt::Display>(
    file: Option<DiagnosticFile>,
    loc: TextRange,
    message: &'static Message,
    args: &[T],
) -> DiagnosticRef {
    Arc::new(Mutex::new(Diagnostic {
        file,
        loc,
        code: message.code(),
        category: message.category(),
        message: Some(message),
        message_key: message.key(),
        message_args: stringify_args(args),
        reports_unnecessary: message.reports_unnecessary(),
        reports_deprecated: message.reports_deprecated(),
        ..Default::default()
    }))
}

/// `func NewDiagnosticChain(chain *Diagnostic, message *diagnostics.Message, args ...any) *Diagnostic`
pub fn new_diagnostic_chain<T: fmt::Display>(
    chain: Option<&DiagnosticRef>,
    message: &'static Message,
    args: &[T],
) -> DiagnosticRef {
    if let Some(chain) = chain {
        let (file, loc, related_information) = {
            let c = lock_diagnostic(chain);
            (
                c.file.clone(),
                c.loc,
                // Go: `SetRelatedInfo(chain.relatedInformation)` shares the
                // chain's slice; cloning the `Vec` shares the same `Arc`
                // elements, which is what callers observe.
                c.related_information.clone(),
            )
        };
        let result = new_diagnostic(file, loc, message, args);
        lock_diagnostic(&result)
            .add_message_chain(Some(chain.clone()))
            .set_related_info(related_information);
        return result;
    }
    // `core.TextRange{}`
    new_diagnostic(None, TextRange::default(), message, args)
}

/// `func NewCompilerDiagnostic(message *diagnostics.Message, args ...any) *Diagnostic`
pub fn new_compiler_diagnostic<T: fmt::Display>(
    message: &'static Message,
    args: &[T],
) -> DiagnosticRef {
    new_diagnostic(None, TextRange::undefined(), message, args)
}

/// `func NewExternalDiagnostic(...) *Diagnostic` — creates a diagnostic
/// reported by an external source such as a content mapper. The message
/// text is already localized (the external source owns localization) and
/// the code is shown with the given source prefix (e.g. "vue") instead of
/// "TS". The location refers to the file's original, untransformed content.
pub fn new_external_diagnostic(
    file: Option<DiagnosticFile>,
    loc: TextRange,
    source: String,
    category: Category,
    code: i32,
    message_text: String,
) -> DiagnosticRef {
    Arc::new(Mutex::new(Diagnostic {
        file,
        loc,
        code,
        category,
        source,
        message_text,
        ..Default::default()
    }))
}

// DiagnosticsCollection

/// `type DiagnosticsCollection struct` — the `sync.Mutex`-guarded
/// diagnostic store that dedups by location.
///
/// PORT: all guarded fields live in one `DiagnosticsCollectionState` under
/// a single `Mutex` — the Go lock granularity.
#[derive(Default)]
pub struct DiagnosticsCollection {
    state: Mutex<DiagnosticsCollectionState>,
}

#[derive(Default)]
struct DiagnosticsCollectionState {
    count: usize,
    file_diagnostics: FxHashMap<PathKey, Vec<DiagnosticRef>>,
    file_diagnostics_sorted: Set<PathKey>,
    non_file_diagnostics: Vec<DiagnosticRef>,
    non_file_diagnostics_sorted: bool,
    diagnostic_index: FxHashMap<DiagnosticLocationKey, DiagnosticRef>,
    diagnostic_collisions: FxHashMap<DiagnosticLocationKey, Vec<DiagnosticRef>>,
}

/// `type diagnosticLocationKey struct`
#[derive(Clone, PartialEq, Eq, Hash)]
struct DiagnosticLocationKey {
    path: PathKey,
    loc: TextRange,
    code: i32,
}

/// `getDiagnosticLocationKey(diagnostic)`
fn get_diagnostic_location_key(diagnostic: &DiagnosticRef) -> DiagnosticLocationKey {
    let d = lock_diagnostic(diagnostic);
    DiagnosticLocationKey {
        path: d
            .file
            .as_ref()
            .map(|file| file.path_key.clone())
            .unwrap_or_default(),
        loc: d.loc,
        code: d.code,
    }
}

impl DiagnosticsCollection {
    /// `var c DiagnosticsCollection` — the Go zero value.
    pub fn new() -> DiagnosticsCollection {
        Self::default()
    }

    fn state(&self) -> MutexGuard<'_, DiagnosticsCollectionState> {
        // Go's `sync.Mutex` does not poison; recover the guard so a
        // panicking caller does not wedge the collection (Go's `defer`
        // unlock keeps it usable).
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// `c.Add(diagnostic)` — returns the canonical diagnostic for the
    /// location: an earlier `EqualDiagnostics` match, or `diagnostic`
    /// itself.
    pub fn add(&self, diagnostic: &DiagnosticRef) -> DiagnosticRef {
        let mut state = self.state();

        let key = get_diagnostic_location_key(diagnostic);
        if let Some(existing) = state.diagnostic_index.get(&key) {
            if equal_diagnostics(existing, diagnostic) {
                return existing.clone();
            }
            if let Some(collisions) = state.diagnostic_collisions.get(&key) {
                for collision in collisions {
                    if equal_diagnostics(collision, diagnostic) {
                        return collision.clone();
                    }
                }
            }
        }
        match state.diagnostic_index.entry(key.clone()) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(diagnostic.clone());
            }
            std::collections::hash_map::Entry::Occupied(_) => {
                state
                    .diagnostic_collisions
                    .entry(key)
                    .or_default()
                    .push(diagnostic.clone());
            }
        }

        state.count += 1;

        // `diagnostic.File() != nil` — file presence, not an empty path key.
        let path = lock_diagnostic(diagnostic)
            .file
            .as_ref()
            .map(|file| file.path_key.clone());
        match path {
            Some(path) => {
                state
                    .file_diagnostics
                    .entry(path.clone())
                    .or_default()
                    .push(diagnostic.clone());
                state.file_diagnostics_sorted.delete(&path);
            }
            None => {
                state.non_file_diagnostics.push(diagnostic.clone());
                state.non_file_diagnostics_sorted = false;
            }
        }
        diagnostic.clone()
    }

    /// `c.Lookup(diagnostic)`
    pub fn lookup(&self, diagnostic: &DiagnosticRef) -> Option<DiagnosticRef> {
        let mut state = self.state();

        let file = lock_diagnostic(diagnostic).file.clone();
        let diagnostics = match &file {
            Some(file) => state.get_diagnostics_for_file_locked(file),
            None => state.get_global_diagnostics_locked(),
        };
        // `slices.BinarySearchFunc` returns the smallest index whose element
        // equals the target — `partition_point` is the same search.
        let i = diagnostics.partition_point(|d| compare_diagnostics(d, diagnostic) < 0);
        if i < diagnostics.len() && compare_diagnostics(&diagnostics[i], diagnostic) == 0 {
            return Some(diagnostics[i].clone());
        }
        None
    }

    /// `c.GetGlobalDiagnostics()`
    pub fn get_global_diagnostics(&self) -> Vec<DiagnosticRef> {
        self.state().get_global_diagnostics_locked()
    }

    /// `c.GetDiagnosticsForFile(file)`
    pub fn get_diagnostics_for_file(&self, file: &DiagnosticFile) -> Vec<DiagnosticRef> {
        self.state().get_diagnostics_for_file_locked(file)
    }

    /// `c.GetDiagnostics()`
    pub fn get_diagnostics(&self) -> Vec<DiagnosticRef> {
        let state = self.state();

        let mut diagnostics = Vec::with_capacity(state.count);
        diagnostics.extend(state.non_file_diagnostics.iter().cloned());
        // Go's map iteration order is arbitrary — the post-concatenation
        // sort makes it unobservable.
        for diags in state.file_diagnostics.values() {
            diagnostics.extend(diags.iter().cloned());
        }
        // `slices.SortFunc` is Go's unstable pdqsort → `sort_unstable_by`.
        diagnostics.sort_unstable_by(|a, b| compare_diagnostics(a, b).cmp(&0));
        diagnostics
    }
}

impl DiagnosticsCollectionState {
    /// `c.getGlobalDiagnosticsLocked()`
    fn get_global_diagnostics_locked(&mut self) -> Vec<DiagnosticRef> {
        if !self.non_file_diagnostics_sorted {
            // `slices.SortStableFunc` — Rust `sort_by` is stable.
            self.non_file_diagnostics
                .sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
            self.non_file_diagnostics_sorted = true;
        }
        self.non_file_diagnostics.clone()
    }

    /// `c.getDiagnosticsForFileLocked(file)`
    fn get_diagnostics_for_file_locked(&mut self, file: &DiagnosticFile) -> Vec<DiagnosticRef> {
        let path = file.path_key.clone();
        if !self.file_diagnostics_sorted.has(&path) {
            if let Some(diagnostics) = self.file_diagnostics.get_mut(&path) {
                diagnostics.sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
            }
            self.file_diagnostics_sorted.add(path.clone());
        }
        self.file_diagnostics
            .get(&path)
            .cloned()
            .unwrap_or_default()
    }
}

// Go relies on the `sync.Mutex` to share the collection across goroutines;
// pin the intended auto-traits.
const _: () = {
    const fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<DiagnosticsCollection>();
    assert_send_sync::<DiagnosticRef>();
};

// Ordering and equality

/// Everything the equality/ordering helpers read, captured under a single
/// lock acquisition per diagnostic. Never holding two diagnostic locks at
/// once keeps the helpers deadlock-free without a lock ordering.
struct DiagnosticView {
    /// `getDiagnosticPath(d)`
    path: String,
    loc: TextRange,
    code: i32,
    category: Category,
    source: String,
    /// `getDiagnosticMessageIdentity(d)`
    message_identity: String,
    message_args: Vec<String>,
    message_chain: Vec<DiagnosticRef>,
    related_information: Vec<DiagnosticRef>,
}

fn view_of(d: &DiagnosticRef) -> DiagnosticView {
    let d = lock_diagnostic(d);
    DiagnosticView {
        path: get_diagnostic_path(&d).to_string(),
        loc: d.loc,
        code: d.code,
        category: d.category,
        source: d.source.clone(),
        message_identity: get_diagnostic_message_identity(&d).to_string(),
        message_args: d.message_args.clone(),
        message_chain: d.message_chain.clone(),
        related_information: d.related_information.clone(),
    }
}

/// `getDiagnosticPath(d)` — `d.File().FileName().AsString()` or "".
fn get_diagnostic_path(d: &Diagnostic) -> &str {
    match &d.file {
        Some(file) => file.file_name.as_string(),
        None => "",
    }
}

/// `slices.EqualFunc`
fn slice_equal_func<T>(a: &[T], b: &[T], eq: impl Fn(&T, &T) -> bool) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| eq(x, y))
}

/// `func EqualDiagnostics(d1, d2 *Diagnostic) bool`
pub fn equal_diagnostics(d1: &DiagnosticRef, d2: &DiagnosticRef) -> bool {
    if Arc::ptr_eq(d1, d2) {
        return true;
    }
    let v1 = view_of(d1);
    let v2 = view_of(d2);
    equal_views_no_related_info(&v1, &v2)
        && slice_equal_func(&v1.related_information, &v2.related_information, equal_diagnostics)
}

/// `func EqualDiagnosticsNoRelatedInfo(d1, d2 *Diagnostic) bool`
pub fn equal_diagnostics_no_related_info(d1: &DiagnosticRef, d2: &DiagnosticRef) -> bool {
    if Arc::ptr_eq(d1, d2) {
        return true;
    }
    equal_views_no_related_info(&view_of(d1), &view_of(d2))
}

fn equal_views_no_related_info(v1: &DiagnosticView, v2: &DiagnosticView) -> bool {
    v1.path == v2.path
        && v1.loc == v2.loc
        && v1.code == v2.code
        && v1.category == v2.category
        && v1.source == v2.source
        && v1.message_identity == v2.message_identity
        && v1.message_args == v2.message_args
        && slice_equal_func(&v1.message_chain, &v2.message_chain, equal_message_chain)
}

/// `getDiagnosticMessageIdentity(diagnostic)`
fn get_diagnostic_message_identity(d: &Diagnostic) -> &str {
    if !d.message_text.is_empty() {
        return &d.message_text;
    }
    if let Some(message) = d.message {
        if d.code == -1 {
            return message.text();
        }
    }
    d.message_key
}

/// `equalMessageChain`
fn equal_message_chain(c1: &DiagnosticRef, c2: &DiagnosticRef) -> bool {
    if Arc::ptr_eq(c1, c2) {
        return true;
    }
    let v1 = view_of(c1);
    let v2 = view_of(c2);
    v1.code == v2.code
        && v1.message_args == v2.message_args
        && slice_equal_func(&v1.message_chain, &v2.message_chain, equal_message_chain)
}

/// `Ordering` → Go's `int` compare result. `strings.Compare`/`slices.Compare`
/// return -1/0/+1 and the `a - b` subtractions agree in sign — only the
/// sign is ever read.
fn ord_i32(o: Ordering) -> i32 {
    o as i32
}

/// `compareMessageChainSize` — note `len(c2) - len(c1)` is descending.
fn compare_message_chain_size(c1: &[DiagnosticRef], c2: &[DiagnosticRef]) -> i32 {
    let c = ord_i32(c2.len().cmp(&c1.len()));
    if c != 0 {
        return c;
    }
    for i in 0..c1.len() {
        let c = compare_message_chain_size(
            &view_of(&c1[i]).message_chain,
            &view_of(&c2[i]).message_chain,
        );
        if c != 0 {
            return c;
        }
    }
    0
}

/// `compareMessageChainContent`
fn compare_message_chain_content(c1: &[DiagnosticRef], c2: &[DiagnosticRef]) -> i32 {
    for i in 0..c1.len() {
        let v1 = view_of(&c1[i]);
        let v2 = view_of(&c2[i]);
        let c = ord_i32(v1.message_args.cmp(&v2.message_args));
        if c != 0 {
            return c;
        }
        // Go: `c1[i].MessageChain() != nil` — an empty chain compares 0
        // either way, so the nil check reduces to non-empty here.
        if !v1.message_chain.is_empty() {
            let c = compare_message_chain_content(&v1.message_chain, &v2.message_chain);
            if c != 0 {
                return c;
            }
        }
    }
    0
}

/// `compareRelatedInfo` — note `len(r2) - len(r1)` is descending.
fn compare_related_info(r1: &[DiagnosticRef], r2: &[DiagnosticRef]) -> i32 {
    let c = ord_i32(r2.len().cmp(&r1.len()));
    if c != 0 {
        return c;
    }
    for i in 0..r1.len() {
        let c = compare_diagnostics(&r1[i], &r2[i]);
        if c != 0 {
            return c;
        }
    }
    0
}

/// `func CompareDiagnostics(d1, d2 *Diagnostic) int`
pub fn compare_diagnostics(d1: &DiagnosticRef, d2: &DiagnosticRef) -> i32 {
    if Arc::ptr_eq(d1, d2) {
        return 0;
    }
    let v1 = view_of(d1);
    let v2 = view_of(d2);
    let c = ord_i32(v1.path.cmp(&v2.path));
    if c != 0 {
        return c;
    }
    let c = ord_i32(v1.loc.pos().cmp(&v2.loc.pos()));
    if c != 0 {
        return c;
    }
    let c = ord_i32(v1.loc.end().cmp(&v2.loc.end()));
    if c != 0 {
        return c;
    }
    let c = ord_i32(v1.code.cmp(&v2.code));
    if c != 0 {
        return c;
    }
    let c = ord_i32((v1.category as i32).cmp(&(v2.category as i32)));
    if c != 0 {
        return c;
    }
    let c = ord_i32(v1.source.cmp(&v2.source));
    if c != 0 {
        return c;
    }
    let c = ord_i32(v1.message_identity.cmp(&v2.message_identity));
    if c != 0 {
        return c;
    }
    let c = ord_i32(v1.message_args.cmp(&v2.message_args));
    if c != 0 {
        return c;
    }
    let c = compare_message_chain_size(&v1.message_chain, &v2.message_chain);
    if c != 0 {
        return c;
    }
    let c = compare_message_chain_content(&v1.message_chain, &v2.message_chain);
    if c != 0 {
        return c;
    }
    compare_related_info(&v1.related_information, &v2.related_information)
}

#[cfg(test)]
mod tests {
    // Ported from tsc/internal/ast/diagnostic_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

    use std::sync::Arc;

    use tsc_diagnostics::{Cannot_find_name_0, X_0_is_declared_here, new_adhoc_message};
    use tsc_tspath::{CaseSensitivity, PathKey, RootedFilePath};

    use super::*;

    /// `TestDiagnosticsCollectionDeduplicatesExactDiagnosticsOnAdd`
    #[test]
    fn test_diagnostics_collection_deduplicates_exact_diagnostics_on_add() {
        let collection = DiagnosticsCollection::new();
        let first = new_compiler_diagnostic(&Cannot_find_name_0, &["x"]);
        lock_diagnostic(&first).add_related_info(Some(new_compiler_diagnostic(
            &X_0_is_declared_here,
            &["first"],
        )));
        let second = new_compiler_diagnostic(&Cannot_find_name_0, &["x"]);
        lock_diagnostic(&second).add_related_info(Some(new_compiler_diagnostic(
            &X_0_is_declared_here,
            &["first"],
        )));
        let different = new_compiler_diagnostic(&Cannot_find_name_0, &["x"]);
        lock_diagnostic(&different).add_related_info(Some(new_compiler_diagnostic(
            &X_0_is_declared_here,
            &["second"],
        )));

        let got = collection.add(&first);
        assert!(Arc::ptr_eq(&got, &first), "first add() must return first");
        let canonical = collection.add(&second);
        assert!(
            Arc::ptr_eq(&canonical, &first),
            "second add() must return the canonical diagnostic"
        );
        let got = collection.add(&different);
        assert!(
            Arc::ptr_eq(&got, &different),
            "different add() must return different"
        );

        lock_diagnostic(&canonical).add_related_info(Some(new_compiler_diagnostic(
            &X_0_is_declared_here,
            &["third"],
        )));
        let collected = collection.get_global_diagnostics();
        assert_eq!(collected.len(), 2, "GetGlobalDiagnostics() length");
        assert_eq!(
            lock_diagnostic(&first).related_information().len(),
            2,
            "canonical diagnostic related-information length"
        );
    }

    /// `TestDiagnosticsCollectionPreservesDistinctAdHocMessages`
    #[test]
    fn test_diagnostics_collection_preserves_distinct_adhoc_messages() {
        let collection = DiagnosticsCollection::new();
        let first = new_compiler_diagnostic(new_adhoc_message("first".to_string()), &[] as &[&str]);
        let second =
            new_compiler_diagnostic(new_adhoc_message("second".to_string()), &[] as &[&str]);

        collection.add(&first);
        collection.add(&second);
        assert_eq!(collection.get_global_diagnostics().len(), 2);
    }

    /// `TestDiagnosticsCollectionGetsDiagnosticsForEquivalentSourceFile`
    ///
    /// PORT: Go builds two `*SourceFile` values sharing `parseOptions` —
    /// `DiagnosticsCollection` only reads `PathKey()`, so two handles with
    /// the same file identity exercise the same equivalence.
    #[test]
    fn test_diagnostics_collection_gets_diagnostics_for_equivalent_source_file() {
        let file_name = RootedFilePath::from("/src/file.ts");
        let path = CaseSensitivity::CaseSensitive.path_key(&file_name.as_path());
        let diagnostic_file = DiagnosticFile {
            file_name: file_name.clone(),
            path_key: path.clone(),
            ..Default::default()
        };
        let requested_file = DiagnosticFile {
            file_name,
            path_key: path,
            ..Default::default()
        };
        let diagnostic = new_diagnostic(
            Some(diagnostic_file),
            TextRange::default(),
            &Cannot_find_name_0,
            &["x"],
        );

        let collection = DiagnosticsCollection::new();
        collection.add(&diagnostic);

        let collected = collection.get_diagnostics_for_file(&requested_file);
        assert!(
            collected.len() == 1 && Arc::ptr_eq(&collected[0], &diagnostic),
            "GetDiagnosticsForFile() must return the diagnostic for an equivalent source file"
        );
    }

    /// `TestExternalDiagnosticIdentity`
    #[test]
    fn test_external_diagnostic_identity() {
        let file = DiagnosticFile {
            file_name: RootedFilePath::from("/src/file.vue"),
            path_key: PathKey::from("/src/file.vue"),
            ..Default::default()
        };
        let loc = TextRange::new(1, 2);
        let first = new_external_diagnostic(
            Some(file.clone()),
            loc,
            "mapper-a".to_string(),
            Category::Error,
            0,
            "first".to_string(),
        );
        let diagnostics = [
            first.clone(),
            new_external_diagnostic(
                Some(file.clone()),
                loc,
                "mapper-a".to_string(),
                Category::Error,
                0,
                "second".to_string(),
            ),
            new_external_diagnostic(
                Some(file.clone()),
                loc,
                "mapper-b".to_string(),
                Category::Error,
                0,
                "first".to_string(),
            ),
            new_external_diagnostic(
                Some(file.clone()),
                loc,
                "mapper-a".to_string(),
                Category::Warning,
                0,
                "first".to_string(),
            ),
        ];

        let collection = DiagnosticsCollection::new();
        for diagnostic in &diagnostics {
            assert!(
                !equal_diagnostics_no_related_info(&first, diagnostic)
                    || Arc::ptr_eq(&first, diagnostic)
            );
            assert!(
                compare_diagnostics(&first, diagnostic) != 0 || Arc::ptr_eq(&first, diagnostic)
            );
            collection.add(diagnostic);
        }
        assert_eq!(collection.get_diagnostics().len(), diagnostics.len());
    }
}
