// Ported from tsc/internal/fourslash/baselineutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// ASSUMPTIONS about the parallel fourslash.rs / test_parser.rs ports (all
// `pub(crate)`):
//   - `fourslash::FourslashTest` has fields `test_data: TestData`,
//     `baselines: HashMap<BaselineCommand, String>`,
//     `state_baseline: Option<StateBaseline>`,
//     `open_files: <set of RootedFilePath>` (`.contains(&path)`),
//     `vfs: Arc<dyn Vfs>`, and methods
//     `get_script_info(&self, &RootedFilePath) -> &ScriptInfo` where
//     `ScriptInfo` implements `lsconv::Script` and has `content: String` and
//     `line_map: LspLineMap`.
//   - `fourslash::{is_lib_file(&str) -> bool, get_base_file_name_from_test() -> String}`.
//   - `fourslash::{new_test_converters, TestConverters}` where
//     `TestConverters::line_and_character_to_position<T: Script + Clone>(&self, script: T, Position) -> TextPos`.
//   - `test_parser::{MarkerOrRange, Marker}` where `MarkerOrRange` is a trait
//     with `file_name(&self) -> &RootedFilePath`, `ls_pos(&self) -> Position`,
//     `get_name(&self) -> Option<&String>`; `Marker` has `position` (Ord),
//     `ls_position: Position`, `name: Option<String>`.
//   - Go's `t *testing.T` parameters are dropped; failures are `panic!`/`assert!`.
//
// NOTE: marker strings are written with `\u{3c}`/`\u{3e}` escapes (byte-exact
// equivalents of the literal context-start/context-end markers).

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tsc_bundled as bundled;
use tsc_collections::{MultiMap, OrderedMap, group_by};
use tsc_core::core as core;
use tsc_core::text::TextPos;
use tsc_debug as debug;
use tsc_lsconv::{compute_lsp_line_starts, file_name_to_document_uri};
use tsc_lsproto::{DocumentUri, Location, Position, Range, SymbolInformation, compare_positions};
use tsc_stringutil::lower_first_char;
use tsc_testutil::baseline;
use tsc_tspath::{
    RootedDirectoryPath, RootedFilePath, rooted_directory_path_from_absolute,
    rooted_directory_path_from_path, rooted_file_path_from_path,
};
use tsc_vfs::Vfs;

use crate::fourslash::{
    FourslashTest, ScriptInfo, TestConverters, get_base_file_name_from_test, is_lib_file,
};
use crate::test_parser::{Marker, MarkerOrRange};

pub(crate) const AUTO_IMPORTS_CMD: BaselineCommand = BaselineCommand("Auto Imports");
pub(crate) const CALL_HIERARCHY_CMD: BaselineCommand = BaselineCommand("Call Hierarchy");
pub(crate) const CLOSING_TAG_CMD: BaselineCommand = BaselineCommand("Closing Tag");
pub(crate) const DOCUMENT_HIGHLIGHTS_CMD: BaselineCommand = BaselineCommand("documentHighlights");
pub(crate) const FIND_ALL_REFERENCES_CMD: BaselineCommand = BaselineCommand("findAllReferences");
pub(crate) const VS_FIND_ALL_REFERENCES_CMD: BaselineCommand =
    BaselineCommand("vsFindAllReferences");
pub(crate) const GO_TO_DEFINITION_CMD: BaselineCommand = BaselineCommand("goToDefinition");
pub(crate) const GO_TO_IMPLEMENTATION_CMD: BaselineCommand = BaselineCommand("goToImplementation");
pub(crate) const GO_TO_SOURCE_DEFINITION_CMD: BaselineCommand =
    BaselineCommand("goToSourceDefinition");
pub(crate) const GO_TO_TYPE_DEFINITION_CMD: BaselineCommand = BaselineCommand("goToType");
pub(crate) const INLAY_HINTS_CMD: BaselineCommand = BaselineCommand("Inlay Hints");
pub(crate) const NON_SUGGESTION_DIAGNOSTICS_CMD: BaselineCommand =
    BaselineCommand("Syntax and Semantic Diagnostics");
pub(crate) const QUICK_INFO_CMD: BaselineCommand = BaselineCommand("QuickInfo");
pub(crate) const VS_QUICK_INFO_CMD: BaselineCommand = BaselineCommand("VSQuickInfo");
pub(crate) const LINKED_EDITING_CMD: BaselineCommand = BaselineCommand("linkedEditing");
pub(crate) const RENAME_CMD: BaselineCommand = BaselineCommand("findRenameLocations");
pub(crate) const SIGNATURE_HELP_CMD: BaselineCommand = BaselineCommand("SignatureHelp");
pub(crate) const SMART_SELECTION_CMD: BaselineCommand = BaselineCommand("Smart Selection");
pub(crate) const CODE_LENSES_CMD: BaselineCommand = BaselineCommand("Code Lenses");
pub(crate) const DOCUMENT_SYMBOLS_CMD: BaselineCommand = BaselineCommand("Document Symbols");
/// `baselineCommand("workspaceSymbol")` — used inline in Go's VerifyBaselineWorkspaceSymbol.
pub(crate) const WORKSPACE_SYMBOL_CMD: BaselineCommand = BaselineCommand("workspaceSymbol");

/// `type baselineCommand string`
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct BaselineCommand(pub &'static str);

impl FourslashTest {
    /// `addResultToBaseline`.
    pub(crate) fn add_result_to_baseline(&mut self, command: BaselineCommand, actual: &str) {
        // Single baseline for all commands when state baselining is enabled.
        if self.test_data.is_state_baselining_enabled() {
            let mut b = self
                .state_baseline
                .as_ref()
                .expect("state baselining enabled but stateBaseline is not initialized")
                .baseline
                .borrow_mut();
            if !b.is_empty() {
                b.push_str("\n\n\n\n");
            }
            b.push_str(&format!("// === {} ===\n", command.0));
            b.push_str(actual);
        } else {
            let b = self.baselines.entry(command).or_default();
            if !b.is_empty() {
                b.push_str("\n\n\n\n");
            }
            b.push_str("// === ");
            b.push_str(command.0);
            b.push_str(" ===\n");
            b.push_str(actual);
        }
    }

    /// `writeToBaseline`.
    pub(crate) fn write_to_baseline(&mut self, command: BaselineCommand, content: &str) {
        self.baselines.entry(command).or_default().push_str(content);
    }
}

/// `getBaselineFileName`.
pub(crate) fn get_baseline_file_name(command: BaselineCommand) -> String {
    format!(
        "{}.{}",
        get_base_file_name_from_test(),
        get_baseline_extension(command)
    )
}

/// `getBaselineExtension`.
fn get_baseline_extension(command: BaselineCommand) -> &'static str {
    match command {
        QUICK_INFO_CMD | VS_QUICK_INFO_CMD | SIGNATURE_HELP_CMD | SMART_SELECTION_CMD
        | INLAY_HINTS_CMD | NON_SUGGESTION_DIAGNOSTICS_CMD | DOCUMENT_SYMBOLS_CMD
        | CLOSING_TAG_CMD | VS_FIND_ALL_REFERENCES_CMD => "baseline",
        CALL_HIERARCHY_CMD => "callHierarchy.txt",
        AUTO_IMPORTS_CMD => "baseline.md",
        LINKED_EDITING_CMD => "linkedEditing.txt",
        _ => "baseline.jsonc",
    }
}

impl FourslashTest {
    /// `getBaselineOptions`.
    pub(crate) fn get_baseline_options(&self, command: BaselineCommand) -> baseline::Options {
        baseline::Options {
            subfolder: format!("fourslash/{}", normalize_command_name(command.0)),
            ..Default::default()
        }
    }
}

/// `dropTrailingEmptyLines`.
pub(crate) fn drop_trailing_empty_lines(ss: &[String]) -> &[String] {
    &ss[..(core::find_last_index(ss, |s| !s.is_empty()) + 1) as usize]
}

/// `normalizeCommandName`.
fn normalize_command_name(command: &str) -> String {
    let joined: String = command.split_whitespace().collect();
    String::from_utf8(lower_first_char(joined.as_bytes())).expect("command name is not utf-8")
}

/// `type documentSpan struct`.
#[derive(Clone, PartialEq)]
pub(crate) struct DocumentSpan {
    pub(crate) uri: DocumentUri,
    pub(crate) text_span: Range,
    pub(crate) context_span: Option<Range>,
}

/// `type baselineFourslashLocationsOptions struct`.
///
/// `marker`/`additionalSpan` use `Rc`/`Option`; the Go `nil`-able func fields
/// are `Option<Box<dyn Fn…>>`.
#[derive(Default)]
pub(crate) struct BaselineFourslashLocationsOptions {
    // markerInfo
    /// `marker` — `MarkerOrRange`; location.
    pub(crate) marker: Option<Rc<dyn MarkerOrRange>>,
    /// `markerName` — name of the marker to be printed in baseline.
    pub(crate) marker_name: String,

    pub(crate) end_marker: String,

    pub(crate) start_marker_prefix: Option<Box<dyn Fn(&DocumentSpan) -> Option<String>>>,
    pub(crate) end_marker_suffix: Option<Box<dyn Fn(&DocumentSpan) -> Option<String>>>,
    pub(crate) get_location_data: Option<Box<dyn Fn(&DocumentSpan) -> String>>,

    pub(crate) additional_span: Option<DocumentSpan>,
    pub(crate) preserve_result_order: bool,
    pub(crate) ordered_files: Vec<DocumentUri>,
}

/// `locationToSpan`.
pub(crate) fn location_to_span(loc: &Location) -> DocumentSpan {
    DocumentSpan {
        uri: loc.uri.clone(),
        text_span: loc.range.clone(),
        context_span: None,
    }
}

impl FourslashTest {
    /// `getBaselineForLocationsWithFileContents`.
    pub(crate) fn get_baseline_for_locations_with_file_contents(
        &self,
        locations: &[Location],
        options: BaselineFourslashLocationsOptions,
    ) -> String {
        self.get_baseline_for_spans_with_file_contents(
            &core::map(locations, location_to_span),
            options,
        )
    }

    /// `getBaselineForSpansWithFileContents`.
    pub(crate) fn get_baseline_for_spans_with_file_contents(
        &self,
        spans: &[DocumentSpan],
        mut options: BaselineFourslashLocationsOptions,
    ) -> String {
        let spans_by_file = group_by(spans.iter().cloned(), |span: &DocumentSpan| span.uri.clone());
        if options.preserve_result_order {
            options.ordered_files = unique_files_in_span_order(spans);
        }
        self.get_baseline_for_grouped_spans_with_file_contents(&spans_by_file, &options)
    }

    /// `getBaselineForGroupedSpansWithFileContents`.
    pub(crate) fn get_baseline_for_grouped_spans_with_file_contents(
        &self,
        grouped_ranges: &MultiMap<DocumentUri, DocumentSpan>,
        options: &BaselineFourslashLocationsOptions,
    ) -> String {
        // We must always print the file containing the marker,
        // but don't want to print it twice at the end if it already
        // found in a file with ranges.
        let mut found_marker = false;
        let mut found_additional_location = false;
        let mut span_to_context_id: SpanToContextId = Vec::new();

        let mut baseline_entries: Vec<String> = Vec::new();
        let mut add_file_entry = |path: &RootedFilePath| {
            let file_name = file_name_to_document_uri(path);
            let ranges = grouped_ranges.get(&file_name);
            if ranges.is_empty() {
                return;
            }

            let Some(content) = self.text_of_file(path) else {
                return;
            };

            if options.marker.is_some() && options.marker.as_ref().unwrap().file_name() == path {
                found_marker = true;
            }

            if let Some(additional_span) = &options.additional_span
                && additional_span.uri == file_name
            {
                found_additional_location = true;
            }

            baseline_entries.push(self.get_baseline_content_for_file(
                path,
                &content,
                ranges,
                &mut span_to_context_id,
                options,
            ));
        };
        if options.preserve_result_order {
            for uri in &options.ordered_files {
                add_file_entry(&uri.file_name());
            }
        } else {
            for path in
                get_accessible_file_paths(&*self.vfs, &rooted_directory_path_from_absolute("/"))
            {
                add_file_entry(&path);
            }
            for path in get_accessible_file_paths(&*self.vfs, &bundled::lib_path()) {
                add_file_entry(&path);
            }
        }

        // In Strada, there is a bug where we only ever add additional spans to baselines if we haven't
        // already added the file to the baseline.
        if let Some(additional_span) = &options.additional_span
            && !found_additional_location
        {
            let file_name = additional_span.uri.file_name();
            if let Some(content) = self.text_of_file(&file_name) {
                baseline_entries.push(self.get_baseline_content_for_file(
                    &file_name,
                    &content,
                    std::slice::from_ref(additional_span),
                    &mut span_to_context_id,
                    options,
                ));
                if options.marker.is_some()
                    && options.marker.as_ref().unwrap().file_name() == &file_name
                {
                    found_marker = true;
                }
            }
        }

        if !found_marker
            && let Some(marker) = &options.marker
        {
            // If we didn't find the marker in any file, we need to add it.
            let marker_file_name = marker.file_name().clone();
            if let Some(content) = self.text_of_file(&marker_file_name) {
                baseline_entries.push(self.get_baseline_content_for_file(
                    &marker_file_name,
                    &content,
                    &[],
                    &mut span_to_context_id,
                    options,
                ));
            }
        }

        // !!! skipDocumentContainingOnlyMarker

        baseline_entries.join("\n\n")
    }
}

/// `getAccessibleFilePaths` — `vfs.WalkDir` behavior for collecting regular
/// files: lexical DFS, symlinks reported but not followed (never "regular").
/// PORT: `walk_dir` requires `Arc<dyn Vfs>`; callers only have `&dyn Vfs`, so
/// the traversal is replicated directly over `GetAccessibleEntries`.
pub(crate) fn get_accessible_file_paths(
    file_system: &dyn Vfs,
    root: &RootedDirectoryPath,
) -> Vec<RootedFilePath> {
    fn visit(
        file_system: &dyn Vfs,
        directory: &RootedDirectoryPath,
        files: &mut Vec<RootedFilePath>,
    ) {
        let entries = file_system.get_accessible_entries(directory);
        let directories: HashSet<&str> =
            entries.directories.iter().map(String::as_str).collect();
        let mut names: Vec<&String> = entries
            .directories
            .iter()
            .chain(entries.files.iter())
            .collect();
        names.sort();
        for name in names {
            let child_path = if directories.contains(name.as_str()) {
                directory.resolve_directory(name).as_path()
            } else {
                directory.resolve_file(name).as_path()
            };
            // `entry.Type().IsRegular()` — symlinks are never regular.
            let is_symlink = match &entries.symlinks {
                Some(symlinks) => symlinks.contains(name),
                None => {
                    let real_directory = rooted_directory_path_from_path(
                        file_system.realpath(&directory.as_path()),
                    );
                    let expected_realpath = if directories.contains(name.as_str()) {
                        real_directory.resolve_directory(name).as_path()
                    } else {
                        real_directory.resolve_file(name).as_path()
                    };
                    file_system.realpath(&child_path) != expected_realpath
                }
            };
            if directories.contains(name.as_str()) {
                if !is_symlink {
                    visit(file_system, &directory.resolve_directory(name), files);
                }
            } else if !is_symlink {
                files.push(rooted_file_path_from_path(child_path));
            }
        }
    }

    if !file_system.directory_exists(root) {
        return Vec::new();
    }
    let mut files = Vec::new();
    visit(file_system, root, &mut files);
    files
}

/// `uniqueFilesInSpanOrder`.
fn unique_files_in_span_order(spans: &[DocumentSpan]) -> Vec<DocumentUri> {
    if spans.is_empty() {
        return Vec::new();
    }
    let mut seen: HashSet<DocumentUri> = HashSet::new();
    let mut result = Vec::with_capacity(spans.len());
    for span in spans {
        if !seen.insert(span.uri.clone()) {
            continue;
        }
        result.push(span.uri.clone());
    }
    result
}

impl FourslashTest {
    /// `textOfFile`.
    pub(crate) fn text_of_file(&self, file_name: &RootedFilePath) -> Option<String> {
        if self.open_files.contains(file_name) {
            return Some(
                self.get_script_info(file_name)
                    .expect("script info")
                    .content
                    .clone(),
            );
        }
        self.vfs.read_file(file_name)
    }
}

/// `type detailKind int` — discriminant order is load-bearing (`d1.kind - d2.kind`).
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[repr(i32)]
pub(crate) enum DetailKind {
    /// `detailKindMarker` — written as `/*MARKER*/`.
    #[default]
    Marker = 0,
    /// `detailKindContextStart` — written as the context-start marker.
    ContextStart = 1,
    /// `detailKindTextStart` — written as `[|`.
    TextStart = 2,
    /// `detailKindTextEnd` — written as `|]`.
    TextEnd = 3,
    /// `detailKindContextEnd` — written as the context-end marker.
    ContextEnd = 4,
}
impl DetailKind {
    fn is_end(&self) -> bool {
        matches!(self, DetailKind::ContextEnd | DetailKind::TextEnd)
    }

    fn is_start(&self) -> bool {
        matches!(self, DetailKind::ContextStart | DetailKind::TextStart)
    }
}

/// `type baselineDetail struct` — `Rc` shared so prefix/suffix maps and span
/// identity can key by pointer like Go's `*baselineDetail`/`*documentSpan`.
#[derive(Default)]
pub(crate) struct BaselineDetail {
    pub(crate) pos: Position,
    pub(crate) position_marker: String,
    pub(crate) span: Option<Rc<DocumentSpan>>,
    pub(crate) kind: DetailKind,
}

impl BaselineDetail {
    /// `getRange`.
    fn get_range(&self) -> Range {
        match self.kind {
            DetailKind::ContextStart | DetailKind::ContextEnd => {
                self.span.as_ref().unwrap().context_span.clone().unwrap()
            }
            DetailKind::TextStart | DetailKind::TextEnd => {
                self.span.as_ref().unwrap().text_span.clone()
            }
            DetailKind::Marker => Range {
                start: self.pos,
                end: self.pos,
            },
        }
    }
}

/// `d1.span == d2.span` — Go pointer equality on `*documentSpan` (nil==nil).
fn same_span(a: &Option<Rc<DocumentSpan>>, b: &Option<Rc<DocumentSpan>>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => Rc::ptr_eq(a, b),
        (None, None) => true,
        _ => false,
    }
}

fn ord_i32(c: i32) -> Ordering {
    c.cmp(&0)
}

/// `map[documentSpan]int` — `DocumentSpan` can't derive `Hash`/`Eq` (foreign
/// `Range`/`Position` lack them), so the port uses a Vec with value equality.
pub(crate) type SpanToContextId = Vec<(DocumentSpan, usize)>;

pub(crate) fn span_to_context_id_get(
    m: &SpanToContextId,
    span: &DocumentSpan,
) -> Option<usize> {
    m.iter().find(|(s, _)| s == span).map(|(_, id)| *id)
}

fn span_to_context_id_insert(m: &mut SpanToContextId, span: DocumentSpan) {
    m.push((span, m.len()));
}

impl FourslashTest {
    /// `getBaselineContentForFile`.
    fn get_baseline_content_for_file(
        &self,
        file_name: &RootedFilePath,
        content: &str,
        spans_in_file: &[DocumentSpan],
        span_to_context_id: &mut SpanToContextId,
        options: &BaselineFourslashLocationsOptions,
    ) -> String {
        let mut details: Vec<Rc<BaselineDetail>> = Vec::new();
        let mut detail_prefixes: HashMap<*const BaselineDetail, String> = HashMap::new();
        let mut detail_suffixes: HashMap<*const BaselineDetail, String> = HashMap::new();
        let mut can_determine_context_id_inline = true;

        if let Some(marker) = &options.marker
            && marker.file_name() == file_name
        {
            details.push(Rc::new(BaselineDetail {
                pos: marker.ls_pos(),
                position_marker: options.marker_name.clone(),
                span: None,
                kind: DetailKind::Marker,
            }));
        }

        for span in spans_in_file {
            let span_rc = Rc::new(span.clone());
            let context_span_index = details.len();

            // Add context span markers if present
            if let Some(context_span) = &span.context_span {
                details.push(Rc::new(BaselineDetail {
                    pos: context_span.start,
                    position_marker: "\u{3c}|".to_string(),
                    span: Some(span_rc.clone()),
                    kind: DetailKind::ContextStart,
                }));

                // Check if context span starts after text span
                if compare_positions(&context_span.start, &span.text_span.start) > 0 {
                    can_determine_context_id_inline = false;
                }
            }

            let text_span_index = details.len();
            let mut start_marker = "[|".to_string();
            if let Some(get_location_data) = &options.get_location_data {
                start_marker += &get_location_data(span);
            }
            details.push(Rc::new(BaselineDetail {
                pos: span.text_span.start,
                position_marker: start_marker,
                span: Some(span_rc.clone()),
                kind: DetailKind::TextStart,
            }));
            details.push(Rc::new(BaselineDetail {
                pos: span.text_span.end,
                position_marker: if options.end_marker.is_empty() {
                    "|]".to_string()
                } else {
                    options.end_marker.clone()
                },
                span: Some(span_rc.clone()),
                kind: DetailKind::TextEnd,
            }));

            if let Some(context_span) = &span.context_span {
                details.push(Rc::new(BaselineDetail {
                    pos: context_span.end,
                    position_marker: "|\u{3e}".to_string(),
                    span: Some(span_rc.clone()),
                    kind: DetailKind::ContextEnd,
                }));
            }

            if let Some(start_marker_prefix) = &options.start_marker_prefix
                && let Some(start_prefix) = start_marker_prefix(span)
            {
                // Special case: if this span starts at the same position as the provided marker,
                // we want the span's prefix to appear before the marker name.
                // i.e. We want `/*START PREFIX*/A: /*RENAME*/[|ARENAME|]`,
                // not `/*RENAME*//*START PREFIX*/A: [|ARENAME|]`
                if let Some(marker) = &options.marker
                    && file_name == marker.file_name()
                    && span.text_span.start == marker.ls_pos()
                {
                    debug::assert_!(
                        !detail_prefixes.contains_key(&Rc::as_ptr(&details[0])),
                        "Expected only single prefix at marker location"
                    );
                    detail_prefixes.insert(Rc::as_ptr(&details[0]), start_prefix);
                } else if let Some(context_span) = &span.context_span
                    && context_span.start == span.text_span.start
                {
                    detail_prefixes
                        .insert(Rc::as_ptr(&details[context_span_index]), start_prefix);
                } else {
                    detail_prefixes.insert(Rc::as_ptr(&details[text_span_index]), start_prefix);
                }
            }

            if let Some(end_marker_suffix) = &options.end_marker_suffix
                && let Some(end_suffix) = end_marker_suffix(span)
            {
                // Same as above for suffixes:
                if let Some(marker) = &options.marker
                    && file_name == marker.file_name()
                    && span.text_span.end == marker.ls_pos()
                {
                    detail_suffixes.insert(Rc::as_ptr(&details[0]), end_suffix);
                } else if let Some(context_span) = &span.context_span
                    && context_span.end == span.text_span.end
                {
                    detail_suffixes
                        .insert(Rc::as_ptr(&details[text_span_index + 2]), end_suffix);
                } else {
                    detail_suffixes
                        .insert(Rc::as_ptr(&details[text_span_index + 1]), end_suffix);
                }
            }
        }

        // Our preferred way to write markers is
        // /*MARKER*/[| some text |]
        // [| some /*MARKER*/ text |]
        // [| some text |]/*MARKER*/
        details.sort_by(|d1, d2| {
            let c = compare_positions(&d1.pos, &d2.pos);
            if c != 0 || (d1.kind == DetailKind::Marker && d2.kind == DetailKind::Marker) {
                return ord_i32(c);
            }

            // /*MARKER*/[| some text |]
            if d1.kind == DetailKind::Marker && d2.kind.is_start() {
                return Ordering::Less;
            }
            if d2.kind == DetailKind::Marker && d1.kind.is_start() {
                return Ordering::Greater;
            }

            // [| some text |]/*MARKER*/
            if d1.kind == DetailKind::Marker && d2.kind.is_end() {
                return Ordering::Greater;
            }
            if d2.kind == DetailKind::Marker && d1.kind.is_end() {
                return Ordering::Less;
            }

            // [||] or context-span equivalent
            if same_span(&d1.span, &d2.span) {
                return ord_i32(d1.kind as i32 - d2.kind as i32);
            }

            // context-end before context-start
            if d1.kind.is_start() && d2.kind.is_end() {
                return Ordering::Greater;
            }
            if d1.kind.is_end() && d2.kind.is_start() {
                return Ordering::Less;
            }

            // context start ... text start ... text end ... context end
            if d1.kind.is_end() && d2.kind.is_end() {
                let c = compare_positions(&d2.get_range().start, &d1.get_range().start);
                if c != 0 {
                    return ord_i32(c);
                }
                return ord_i32(d1.kind as i32 - d2.kind as i32);
            }

            // context start, text start ... text end ... context end
            if d1.kind.is_start() && d2.kind.is_start() {
                // NOTE: Go compares `d2.getRange().End` to itself — faithful port.
                let c = compare_positions(&d2.get_range().end, &d2.get_range().end);
                if c != 0 {
                    return ord_i32(c);
                }
                return ord_i32(d1.kind as i32 - d2.kind as i32);
            }

            Ordering::Equal
        });
        // !!! if canDetermineContextIdInline

        // PORT: `ManuallyDrop` — `new_text_with_context_from_file_name` takes
        // `&'a TestConverters<'a>` where the inner `'a` equals the borrow
        // lifetime; a plain local `TestConverters<'a>` can never satisfy that
        // because its `Box<dyn Fn>` destructor would need `'a` to outlive the
        // value's own drop. `ManuallyDrop` suppresses the destructor (and the
        // dropck requirement) — same pattern as `crates/ls`.
        let converters = std::mem::ManuallyDrop::new(self.test_converters());
        let mut text_with_context =
            new_text_with_context_from_file_name(file_name.clone(), content, &converters);
        for (index, detail) in details.iter().enumerate() {
            text_with_context.add(Some(detail.as_ref()));
            text_with_context.pos = detail.pos;
            // Prefix
            if let Some(prefix) = detail_prefixes.get(&Rc::as_ptr(detail))
                && !prefix.is_empty()
            {
                text_with_context.new_content.extend_from_slice(prefix.as_bytes());
            }
            text_with_context
                .new_content
                .extend_from_slice(detail.position_marker.as_bytes());
            if let Some(span) = &detail.span {
                match detail.kind {
                    DetailKind::TextStart => {
                        let mut text = String::new();
                        if let Some(context_id) =
                            span_to_context_id_get(span_to_context_id, span.as_ref())
                        {
                            let mut is_after_context_start = false;
                            let mut text_start_index = index as i32 - 1;
                            while text_start_index >= 0 {
                                let text_start_detail = &details[text_start_index as usize];
                                if text_start_detail.kind == DetailKind::ContextStart
                                    && same_span(&text_start_detail.span, &detail.span)
                                {
                                    is_after_context_start = true;
                                    break;
                                }
                                // Marker is ok to skip over
                                if text_start_detail.span.is_some() {
                                    break;
                                }
                                text_start_index -= 1;
                            }
                            // Skip contextId on span thats surrounded by context span immediately
                            if !is_after_context_start {
                                if text.is_empty() {
                                    text = format!("contextId: {context_id}");
                                } else {
                                    text = format!("contextId: {context_id}, {text}");
                                }
                            }
                        }
                        if !text.is_empty() {
                            text_with_context.new_content.extend_from_slice(b"{ ");
                            text_with_context.new_content.extend_from_slice(text.as_bytes());
                            text_with_context.new_content.extend_from_slice(b" |}");
                        }
                    }
                    DetailKind::ContextStart => {
                        if can_determine_context_id_inline {
                            span_to_context_id_insert(span_to_context_id, (**span).clone());
                        }
                    }
                    _ => {}
                }
            }
            if let Some(suffix) = detail_suffixes.get(&Rc::as_ptr(detail)) {
                text_with_context.new_content.extend_from_slice(suffix.as_bytes());
            }
        }
        text_with_context.add(None);
        if !text_with_context.new_content.is_empty() {
            text_with_context.readable_contents.push(b'\n');
            let new_content = std::mem::take(&mut text_with_context.new_content);
            text_with_context.readable_jsonc_baseline(&new_content);
        }
        String::from_utf8_lossy(&text_with_context.readable_contents).into_owned()
    }
}

/// `lineSplitter` — `\r?\n`, on bytes so non-UTF-8 content splits byte-exactly.
fn split_lines_bytes(text: &[u8]) -> Vec<&[u8]> {
    let mut lines = Vec::new();
    let mut start = 0;
    for (i, b) in text.iter().enumerate() {
        if *b == b'\n' {
            let mut end = i;
            if end > start && text[end - 1] == b'\r' {
                end -= 1;
            }
            lines.push(&text[start..end]);
            start = i + 1;
        }
    }
    lines.push(&text[start..]);
    lines
}

/// `lineSplitter` on `&str`.
fn split_lines_str(text: &str) -> Vec<String> {
    text.split('\n')
        .map(|line| line.strip_suffix('\r').unwrap_or(line).to_string())
        .collect()
}

/// `type textWithContext struct`.
///
/// PORT: Go's `t *textWithContext` implements `lsconv.Script`; the Rust
/// `TestConverters` operates on `&ScriptInfo` directly, so the struct holds
/// an owned `ScriptInfo` and a borrowed `TestConverters` (from `FourslashTest`).
struct TextWithContext<'a> {
    n_lines_context: i32, // number of context lines to write to baseline

    readable_contents: Vec<u8>, // builds what will be returned to be written to baseline

    new_content: Vec<u8>, // helper; the part of the original file content to write between details
    pos: Position,
    is_lib_file: bool,
    script_info: ScriptInfo, // file_name + content + line_map of the original file
    converters: &'a TestConverters<'a>,

    // posLineInfo
    pos_info: Option<Position>,
    line_info: i32,
}

/// `newTextWithContextFromFileName`.
fn new_text_with_context_from_file_name<'a>(
    file_name: RootedFilePath,
    content: &str,
    converters: &'a TestConverters<'a>,
) -> TextWithContext<'a> {
    let mut t = TextWithContext {
        n_lines_context: 4,
        readable_contents: Vec::new(),
        is_lib_file: is_lib_file(file_name.as_string()),
        new_content: Vec::new(),
        pos: Position {
            line: 0,
            character: 0,
        },
        script_info: ScriptInfo {
            file_name: file_name.clone(),
            content: content.to_string(),
            line_map: compute_lsp_line_starts(content.as_bytes()),
            version: 1,
        },
        converters,
        pos_info: None,
        line_info: 0,
    };
    t.readable_contents
        .extend_from_slice(format!("// === {} ===", file_name.as_string()).as_bytes());
    t
}

/// `getIndex` argument — Go's `any`-typed index (offset or position).
enum Index {
    Offset(TextPos),
    Pos(Position),
}

impl From<TextPos> for Index {
    fn from(pos: TextPos) -> Index {
        Index::Offset(pos)
    }
}

impl From<Position> for Index {
    fn from(pos: Position) -> Index {
        Index::Pos(pos)
    }
}

impl TextWithContext<'_> {
    /// `add`.
    fn add(&mut self, detail: Option<&BaselineDetail>) {
        if self.new_content.is_empty() && detail.is_none() {
            panic!("Unsupported");
        }
        if detail.is_none()
            || !matches!(
                detail.unwrap().kind,
                DetailKind::TextEnd | DetailKind::ContextEnd
            )
        {
            // Calculate pos to location number of lines
            let mut pos_line_index = self.line_info;
            if self.pos_info.is_none() || self.pos_info.unwrap() != self.pos {
                pos_line_index = self.script_info.line_map.compute_index_of_line_start(                    self.converters.line_and_character_to_position(&self.script_info, self.pos),
                );
            }

            let mut location_line_index = self.script_info.line_map.line_starts.len() as i32 - 1;
            if let Some(detail) = detail {
                location_line_index = self.script_info.line_map.compute_index_of_line_start(                    self.converters.line_and_character_to_position(&self.script_info, detail.pos),
                );
                self.pos_info = Some(detail.pos);
                self.line_info = location_line_index;
            }

            let mut n_lines = 0;
            if !self.new_content.is_empty() {
                n_lines += self.n_lines_context + 1;
            }
            if detail.is_some() {
                n_lines += self.n_lines_context + 1;
            }
            // first nLinesContext and last nLinesContext
            if location_line_index - pos_line_index > n_lines {
                if !self.new_content.is_empty() {
                    let skipped_string = if self.is_lib_file {
                        "--- (line: --) skipped ---\n".to_string()
                    } else {
                        format!("--- (line: {}) skipped ---", pos_line_index + self.n_lines_context + 1)
                    };

                    self.readable_contents.push(b'\n');
                    let mut text = self.new_content.clone();
                    text.extend_from_slice(self.slice_of_content(
                        Some(self.get_index(self.pos.into())),
                        Some(
                            self.get_index(
                                self.script_info.line_map.line_starts
                                    [(pos_line_index + self.n_lines_context) as usize]
                                    .into(),
                            ),
                        ),
                    ));
                    text.extend_from_slice(skipped_string.as_bytes());
                    self.readable_jsonc_baseline(&text);

                    if detail.is_some() {
                        self.readable_contents.push(b'\n');
                    }
                    self.new_content.clear();
                }
                if let Some(detail) = detail {
                    if self.is_lib_file {
                        self.new_content
                            .extend_from_slice(b"--- (line: --) skipped ---\n");
                    } else {
                        self.new_content.extend_from_slice(
                            format!(
                                "--- (line: {}) skipped ---\n",
                                location_line_index - self.n_lines_context + 1
                            )
                            .as_bytes(),
                        );
                    }
                    let start = self.get_index(
                        self.script_info.line_map.line_starts
                            [(location_line_index - self.n_lines_context + 1) as usize]
                            .into(),
                    );
                    let end = self.get_index(detail.pos.into());
                    let slice = self.slice_of_content(Some(start), Some(end)).to_vec();
                    self.new_content.extend_from_slice(&slice);
                }
                return;
            }
        }
        match detail {
            None => {
                let start = self.get_index(self.pos.into());
                let slice = self.slice_of_content(Some(start), None).to_vec();
                self.new_content.extend_from_slice(&slice);
            }
            Some(detail) => {
                let start = self.get_index(self.pos.into());
                let end = self.get_index(detail.pos.into());
                let slice = self.slice_of_content(Some(start), Some(end)).to_vec();
                self.new_content.extend_from_slice(&slice);
            }
        }
    }

    /// `readableJsoncBaseline`.
    fn readable_jsonc_baseline(&mut self, text: &[u8]) {
        for (i, line) in split_lines_bytes(text).iter().enumerate() {
            if i > 0 {
                self.readable_contents.push(b'\n');
            }
            self.readable_contents.extend_from_slice(b"// ");
            self.readable_contents.extend_from_slice(line);
        }
    }

    /// `sliceOfContent` — Go `*int` bounds become `Option<i64>` (None = edge).
    fn slice_of_content(&self, start: Option<i64>, end: Option<i64>) -> &[u8] {
        let len = self.script_info.content.len() as i64;
        let start = match start {
            Some(s) if s >= 0 => s,
            _ => 0,
        };
        let end = match end {
            Some(e) if e <= len => e,
            _ => len,
        };
        if start > end {
            return &[];
        }
        &self.script_info.content.as_bytes()[start as usize..end as usize]
    }

    /// `getIndex`.
    fn get_index(&self, i: Index) -> i64 {
        match i {
            Index::Offset(pos) => pos as i64,
            Index::Pos(pos) => {
                self.converters.line_and_character_to_position(&self.script_info, pos) as i64
            }
        }
    }
}

/// `type markerAndItem[T any] struct`.
#[derive(Clone)]
pub(crate) struct MarkerAndItem<T> {
    /// `Marker` — `*Marker` in Go; `Rc` here since markers are shared.
    pub marker: Rc<Marker>,
    pub item: T,
}

// Hand-rolled `Serialize` — serde doesn't implement it for `Rc` without the
// `rc` feature. Matches Go's `markerAndItem` JSON shape (`{"marker":…,"item":…}`).
impl<T: serde::Serialize> serde::Serialize for MarkerAndItem<T> {
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = serializer.serialize_struct("MarkerAndItem", 2)?;
        st.serialize_field("marker", self.marker.as_ref())?;
        st.serialize_field("item", &self.item)?;
        st.end()
    }
}

impl FourslashTest {
    /// `annotateContentWithTooltips`.
    ///
    /// PORT: Go `item != *new(T)` becomes `T: PartialEq + Default`; the
    /// `getRange`/`getTooltipLines` func params take `&T` and return
    /// `Option<Range>`/`Vec<String>`.
    pub(crate) fn annotate_content_with_tooltips<T: Clone + Default + PartialEq>(
        &self,
        markers_and_items: &[MarkerAndItem<T>],
        op_name: &str,
        get_range: impl Fn(&T) -> Option<Range>,
        get_tooltip_lines: impl Fn(&T, &T) -> Vec<String>,
    ) -> String {
        let bar_with_gutter = format!("| {}", "-".repeat(70));

        // sort by file, then *backwards* by position in the file
        // so we can insert multiple times on a line without counting.
        let mut sorted = markers_and_items.to_vec();
        sorted.sort_by(|a, b| {
            a.marker
                .file_name()
                .cmp(b.marker.file_name())
                .then(b.marker.position.cmp(&a.marker.position))
        });

        let mut files_to_lines: OrderedMap<RootedFilePath, Vec<String>> =
            OrderedMap::with_size_hint(1);
        let mut previous = T::default();
        for item_and_marker in &sorted {
            let marker = &item_and_marker.marker;
            let item = &item_and_marker.item;

            let mut text_range = get_range(item);
            if text_range.is_none() {
                let start = marker.ls_position;
                let mut end = start;
                end.character += 1;
                text_range = Some(Range { start, end });
            }
            let text_range = text_range.unwrap();

            assert!(
                text_range.start.line == text_range.end.line,
                "Expected text range to be on a single line, got {text_range:?}"
            );
            let underline = " ".repeat(text_range.start.character as usize)
                + &"^".repeat((text_range.end.character - text_range.start.character) as usize);

            let file_name = marker.file_name();
            let mut lines = match files_to_lines.get(file_name) {
                Some(lines) => lines.clone(),
                None => split_lines_str(
                &self
                    .get_script_info(file_name)
                    .expect("script info")
                    .content,
            ),
            };

            let mut tooltip_lines = Vec::new();
            if *item != T::default() {
                tooltip_lines = get_tooltip_lines(item, &previous);
            }
            if tooltip_lines.is_empty() {
                tooltip_lines = vec![format!(
                    "No {op_name} at /*{}*/.",
                    marker.name.as_deref().expect("marker name")
                )];
            }
            let tooltip_lines: Vec<String> =
                core::map(&tooltip_lines, |line| format!("| {line}"));

            let mut lines_to_insert = vec![String::new(); tooltip_lines.len() + 3];
            lines_to_insert[0] = underline;
            lines_to_insert[1] = bar_with_gutter.clone();
            lines_to_insert[2..2 + tooltip_lines.len()].clone_from_slice(&tooltip_lines);
            let last = lines_to_insert.len() - 1;
            lines_to_insert[last] = bar_with_gutter.clone();

            lines.splice(
                (text_range.start.line + 1) as usize..(text_range.start.line + 1) as usize,
                lines_to_insert,
            );
            files_to_lines.set(file_name.clone(), lines);

            previous = item.clone();
        }

        let mut builder = String::new();
        let mut seen_first = false;
        for (file_name, lines) in files_to_lines.entries() {
            builder.push_str(&format!("=== {} ===\n", file_name.as_string()));
            for line in lines {
                builder.push_str("// ");
                builder.push_str(line);
                builder.push('\n');
            }

            if seen_first {
                builder.push_str("\n\n");
            } else {
                seen_first = true;
            }
        }

        builder
    }
}

/// `codeFence`.
pub(crate) fn code_fence(lang: &str, code: &str) -> String {
    format!("```{lang}\n{code}\n```")
}

/// `symbolInformationToData`.
pub(crate) fn symbol_information_to_data(symbol: &SymbolInformation) -> String {
    format!("{{| name: {}, kind: {} |}}", symbol.name, symbol.kind)
}
