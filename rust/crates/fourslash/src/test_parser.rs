// Ported from tsc/internal/fourslash/test_parser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Parses `//@`-annotated fourslash test files into [TestData] (file
// contents, markers, ranges, global options).
//
// PORT notes:
// - `testing.T` follows the workspace convention (see tsc-testutil): Go's
//   `t.Fatalf` failures surface as `Err(Error)`; callers `?` or `.unwrap()`.
// - `*Marker` / `*RangeMarker` pointer sharing becomes `Rc<Marker>` /
//   `Rc<RangeMarker>`; a `RangeMarker` may reference the same `Rc<Marker>`
//   that also appears in `TestData.markers` / `marker_positions`.
// - `Marker.Data map[string]any` becomes `Option<serde_json::Map<String,
//   serde_json::Value>>`.
// - `utf8.DecodeRuneInString` is a local copy of the Go stdlib routine —
//   the identical helpers in `tsc-stringutil`/`tsc-lsconv` are
//   crate-private, so each consumer keeps its own copy (same pattern as
//   `lsconv/src/runes.rs`).
// - `rootDir` and `testConverters` live in the still-skeletal
//   `fourslash.go` port; local copies are defined here (see the
//   PORT(deferred) notes) and should be unified when `fourslash.rs` lands.

use std::borrow::Cow;
use std::rc::Rc;
use std::sync::{Arc, LazyLock};

use rustc_hash::FxHashMap;
use tsc_core::text::{TextPos, TextRange};
use tsc_json as json;
use tsc_lsconv::{
    self as lsconv, LspLineMap, compute_lsp_line_starts, file_name_to_document_uri, new_converters,
};
use tsc_lsproto::{self as lsproto, Position, PositionEncodingKind};
use tsc_spanmap::SpanMap;
use tsc_stringutil as stringutil;
use tsc_testrunner::test_case_parser::{
    ParseTestFilesOptions, parse_test_files_and_symlinks_with_options,
};
use tsc_testutil::Error;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath};

// ---------------------------------------------------------------------------
// Go `unicode/utf8` shim (local copy — see header).
// ---------------------------------------------------------------------------

/// `utf8.RuneError` — the "error" rune, U+FFFD.
const RUNE_ERROR: i32 = 0xFFFD;

/// `utf8.DecodeRuneInString` — RFC 3629-strict decoding: empty input ->
/// (RuneError, 0); invalid encoding -> (RuneError, 1); otherwise the decoded
/// rune and its width in bytes.
fn decode_rune_in_string(s: &[u8]) -> (i32, usize) {
    if s.is_empty() {
        return (RUNE_ERROR, 0);
    }
    let p0 = s[0];
    if p0 < 0x80 {
        return (i32::from(p0), 1);
    }
    // (size, accept range for the first continuation byte)
    let (size, lo, hi): (usize, u8, u8) = match p0 {
        0xC2..=0xDF => (2, 0x80, 0xBF),
        0xE0 => (3, 0xA0, 0xBF),
        0xE1..=0xEC => (3, 0x80, 0xBF),
        0xED => (3, 0x80, 0x9F),
        0xEE..=0xEF => (3, 0x80, 0xBF),
        0xF0 => (4, 0x90, 0xBF),
        0xF1..=0xF3 => (4, 0x80, 0xBF),
        0xF4 => (4, 0x80, 0x8F),
        _ => return (RUNE_ERROR, 1),
    };
    if s.len() < size {
        return (RUNE_ERROR, 1);
    }
    let b1 = s[1];
    if !(lo..=hi).contains(&b1) {
        return (RUNE_ERROR, 1);
    }
    let mut r = match size {
        2 => u32::from(p0 & 0x1F),
        3 => u32::from(p0 & 0x0F),
        _ => u32::from(p0 & 0x07),
    };
    r = (r << 6) | u32::from(b1 & 0x3F);
    for &b in &s[2..size] {
        if !(0x80..=0xBF).contains(&b) {
            return (RUNE_ERROR, 1);
        }
        r = (r << 6) | u32::from(b & 0x3F);
    }
    // The accept ranges above exclude surrogates and out-of-range code points.
    (char::from_u32(r).map_or(RUNE_ERROR, |c| c as i32), size)
}

/// `var rootDir` (`fourslash.go`) — the POSIX root that test file paths
/// anchor to.
///
/// PORT(deferred): the canonical definition belongs to the `fourslash.rs`
/// port; this local copy returns the same `/` root until that lands.
pub(crate) fn root_dir() -> &'static RootedDirectoryPath {
    static ROOT_DIR: LazyLock<RootedDirectoryPath> =
        LazyLock::new(|| tspath::rooted_directory_path_from_normalized("/"));
    &ROOT_DIR
}

/// `type RangeMarker struct` — inserted in source files by surrounding
/// desired text in a range with `[|` and `|]`. For example,
///
/// `[|text in range|]`
///
/// is a range with `text in range` "selected".
#[derive(Debug)]
pub struct RangeMarker {
    /// `fileName tspath.RootedFilePath`
    pub(crate) file_name: RootedFilePath,
    /// `Range core.TextRange`
    pub range: TextRange,
    /// `LSRange lsproto.Range`
    pub ls_range: lsproto::Range,
    /// `Marker *Marker`
    pub marker: Option<Rc<Marker>>,
}

impl RangeMarker {
    /// `func (r *RangeMarker) LSPos() lsproto.Position`
    pub fn ls_pos(&self) -> Position {
        self.ls_range.start
    }

    /// `func (r *RangeMarker) FileName() tspath.RootedFilePath`
    pub fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    /// `func (r *RangeMarker) GetName() *string`
    pub fn get_name(&self) -> Option<&str> {
        self.marker.as_ref().and_then(|m| m.name.as_deref())
    }

    /// `func (r *RangeMarker) LSLocation() lsproto.Location`
    pub fn ls_location(&self) -> lsproto::Location {
        lsproto::Location {
            uri: file_name_to_document_uri(&self.file_name),
            range: self.ls_range.clone(),
        }
    }
}

/// `type Marker struct`.
///
/// `Serialize` matches Go's `encoding/json` output: the unexported
/// `fileName` field is skipped and exported fields keep their Go names.
#[derive(Clone, Debug, serde::Serialize)]
pub struct Marker {
    /// `fileName tspath.RootedFilePath` — unexported in Go; not marshaled.
    #[serde(skip)]
    pub(crate) file_name: RootedFilePath,
    /// `Position int`
    #[serde(rename = "Position")]
    pub position: TextPos,
    /// `LSPosition lsproto.Position`
    #[serde(rename = "LSPosition")]
    pub ls_position: Position,
    /// `Name *string` — `None` for anonymous markers such as `{| "foo": "bar" |}`
    #[serde(rename = "Name")]
    pub name: Option<String>,
    /// `Data map[string]any`
    #[serde(rename = "Data")]
    pub data: Option<serde_json::Map<String, serde_json::Value>>,
}

impl Marker {
    /// `func (m *Marker) LSPos() lsproto.Position`
    pub fn ls_pos(&self) -> Position {
        self.ls_position
    }

    /// `func (m *Marker) FileName() tspath.RootedFilePath`
    pub fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    /// `func (m *Marker) GetName() *string`
    pub fn get_name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// `func (m *Marker) MakerWithSymlink(fileName tspath.RootedFilePath) *Marker`
    ///
    /// PORT: returns a fresh `Marker` value; callers wrap in `Rc` as needed.
    pub fn marker_with_symlink(&self, file_name: RootedFilePath) -> Marker {
        Marker {
            file_name,
            position: self.position,
            ls_position: self.ls_position,
            name: self.name.clone(),
            data: self.data.clone(),
        }
    }
}

/// `type MarkerOrRange interface` — shared accessors for marker lookups.
pub trait MarkerOrRange {
    fn file_name(&self) -> &RootedFilePath;
    fn ls_pos(&self) -> Position;
    fn get_name(&self) -> Option<&str>;
}

impl MarkerOrRange for Marker {
    fn file_name(&self) -> &RootedFilePath {
        Marker::file_name(self)
    }
    fn ls_pos(&self) -> Position {
        Marker::ls_pos(self)
    }
    fn get_name(&self) -> Option<&str> {
        Marker::get_name(self)
    }
}

impl MarkerOrRange for RangeMarker {
    fn file_name(&self) -> &RootedFilePath {
        RangeMarker::file_name(self)
    }
    fn ls_pos(&self) -> Position {
        RangeMarker::ls_pos(self)
    }
    fn get_name(&self) -> Option<&str> {
        RangeMarker::get_name(self)
    }
}

/// Blanket impl so `Rc<Marker>`/`Rc<RangeMarker>` satisfy `MarkerOrRange`
/// like Go's `*Marker`/`*RangeMarker`.
impl<T: MarkerOrRange> MarkerOrRange for Rc<T> {
    fn file_name(&self) -> &RootedFilePath {
        (**self).file_name()
    }
    fn ls_pos(&self) -> Position {
        (**self).ls_pos()
    }
    fn get_name(&self) -> Option<&str> {
        (**self).get_name()
    }
}

/// `type TestData struct`.
pub struct TestData {
    /// `Files []*TestFileInfo`
    pub files: Vec<Rc<TestFileInfo>>,
    /// `MarkerPositions map[string]*Marker`
    pub marker_positions: FxHashMap<String, Rc<Marker>>,
    /// `Markers []*Marker`
    pub markers: Vec<Rc<Marker>>,
    /// `Symlinks map[string]string`
    pub symlinks: FxHashMap<String, String>,
    /// `GlobalOptions map[string]string`
    pub global_options: FxHashMap<String, String>,
    /// `Ranges []*RangeMarker`
    pub ranges: Vec<Rc<RangeMarker>>,
}

impl TestData {
    /// `func (t *TestData) isStateBaseliningEnabled() bool`
    pub(crate) fn is_state_baselining_enabled(&self) -> bool {
        is_state_baselining_enabled(&self.global_options)
    }
}

/// `type testFileWithMarkers struct`.
struct TestFileWithMarkers {
    file: Rc<TestFileInfo>,
    markers: Vec<Rc<Marker>>,
    ranges: Vec<Rc<RangeMarker>>,
}

/// `func isStateBaseliningEnabled(globalOptions map[string]string) bool`
fn is_state_baselining_enabled(global_options: &FxHashMap<String, String>) -> bool {
    global_options.get("statebaseline").map(String::as_str) == Some("true")
}

/// `func ParseTestData(t *testing.T, contents string, fileName string) TestData`
///
/// PORT: `t.Fatalf` becomes `Err(Error)` — callers `?` or `.unwrap()`.
pub fn parse_test_data(contents: &str, file_name: &str) -> Result<TestData, Error> {
    // List of all the subfiles we've parsed out
    let mut files: Vec<Rc<TestFileInfo>> = Vec::new();

    let mut marker_positions: FxHashMap<String, Rc<Marker>> = FxHashMap::default();
    let mut markers: Vec<Rc<Marker>> = Vec::new();
    let mut ranges: Vec<Rc<RangeMarker>> = Vec::new();

    let parsed = parse_test_files_and_symlinks_with_options(
        contents,
        file_name,
        parse_file_content,
        &ParseTestFilesOptions {
            allow_implicit_first_file: true,
        },
    );
    if let Some(e) = parsed.error {
        // `t.Fatalf("Error parsing fourslash data: %s", e.Error())`
        return Err(Error::new(format!("Error parsing fourslash data: {e}")));
    }
    let files_with_marker = parsed.units;
    let symlinks = parsed.symlinks;
    let global_options = parsed.global_options;

    let mut has_ts_config = false;
    for file in files_with_marker {
        has_ts_config = has_ts_config || is_config_file(file.file.file_name.as_string());

        markers.extend(file.markers.iter().cloned());
        ranges.extend(file.ranges.iter().cloned());
        for marker in &file.markers {
            let Some(name) = &marker.name else {
                if marker.data.is_some() {
                    // The marker is an anonymous object marker, which does not need a name. Markers are only set into markerPositions if they have a name
                    continue;
                }
                return Err(Error::new(format!(
                    "Marker at position {} is unnamed",
                    marker.position
                )));
            };
            if let Some(existing) = marker_positions.get(name) {
                return Err(Error::new(format!(
                    "Duplicate marker name: \"{name}\" at {} and {}",
                    marker.position, existing.position
                )));
            }
            marker_positions.insert(name.clone(), marker.clone());
        }
        files.push(file.file);
    }

    if has_ts_config
        && has_unsupported_global_options_with_config(&global_options)
        && !is_state_baselining_enabled(&global_options)
    {
        return Err(Error::new(
            "It is not allowed to use global options along with config files.",
        ));
    }

    Ok(TestData {
        files,
        marker_positions,
        markers,
        symlinks,
        global_options,
        ranges,
    })
}

/// `func hasUnsupportedGlobalOptionsWithConfig(globalOptions map[string]string) bool`
fn has_unsupported_global_options_with_config(global_options: &FxHashMap<String, String>) -> bool {
    for option in global_options.keys() {
        match option.to_lowercase().as_str() {
            "symlink" | "link" | "usecasesensitivefilenames" => continue,
            _ => return true,
        }
    }
    false
}

/// `func isConfigFile(fileName string) bool`
fn is_config_file(file_name: &str) -> bool {
    let file_name = file_name.to_lowercase();
    file_name.ends_with("tsconfig.json") || file_name.ends_with("jsconfig.json")
}

/// `type locationInformation struct` — `position` is the offset in the
/// marker-stripped output; `source_position`/`source_line`/`source_column`
/// (one-based) locate it in the original input for error messages.
struct LocationInformation {
    position: usize,
    source_position: usize,
    source_line: usize,
    source_column: usize,
}

/// `type rangeLocationInformation struct`.
///
/// PORT: `marker *Marker` becomes `marker_index`, an index into the file's
/// `markers` vec; the shared `Rc<Marker>` is resolved once the vec is
/// finalized (markers get their `ls_position` before being published).
struct RangeLocationInformation {
    location: LocationInformation,
    marker_index: Option<usize>,
}

/// `type TestFileInfo struct` — implements [`lsconv::Script`].
#[derive(Debug)]
pub struct TestFileInfo {
    /// `fileName tspath.RootedFilePath`
    pub(crate) file_name: RootedFilePath,
    /// `Content string` — the contents of the file (with markers, etc stripped out)
    pub content: String,
    /// `emit bool`
    pub(crate) emit: bool,
    /// `open bool`
    pub(crate) open: bool,
}

/// `lsconv.Script` — Go's `var _ lsconv.Script = (*TestFileInfo)(nil)`.
impl lsconv::Script for TestFileInfo {
    /// `func (t *TestFileInfo) FileName() tspath.RootedFilePath`
    fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    /// `func (t *TestFileInfo) OriginalFileName() tspath.RootedFilePath`
    fn original_file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    /// `func (t *TestFileInfo) Text() string`
    fn text(&self) -> &[u8] {
        self.content.as_bytes()
    }

    /// `func (t *TestFileInfo) OriginalText() string`
    fn original_text(&self) -> &[u8] {
        self.content.as_bytes()
    }

    /// `func (t *TestFileInfo) SpanMap() *spanmap.SpanMap` — always nil.
    fn span_map(&self) -> Option<Arc<SpanMap>> {
        None
    }
}

/// `const emitThisFileOption`
const EMIT_THIS_FILE_OPTION: &str = "emitthisfile";
/// `const noOpenFileOption`
const NO_OPEN_FILE_OPTION: &str = "noopen";

/// `type parserState int`
#[derive(Clone, Copy, PartialEq, Eq)]
enum ParserState {
    /// `stateNone`
    None,
    /// `stateInSlashStarMarker`
    InSlashStarMarker,
    /// `stateInObjectMarker`
    InObjectMarker,
}

/// `func parseFileContent(fileName string, content string, fileOptions map[string]string) (*testFileWithMarkers, error)`
fn parse_file_content(
    file_name: &str,
    content: &str,
    file_options: &FxHashMap<String, String>,
) -> Result<TestFileWithMarkers, String> {
    parse_file_content_worker(
        tspath::to_rooted_file_path(file_name, root_dir()),
        content,
        file_options,
    )
}

/// `func parseFileContentWorker(fileName tspath.RootedFilePath, content string, fileOptions map[string]string) (*testFileWithMarkers, error)`
fn parse_file_content_worker(
    file_name: RootedFilePath,
    content: &str,
    file_options: &FxHashMap<String, String>,
) -> Result<TestFileWithMarkers, String> {
    let content: &str = &chomp_leading_space(content);
    let bytes = content.as_bytes();

    // The file content (minus metacharacters) so far
    let mut output = String::new();

    let mut markers: Vec<Marker> = Vec::new();

    // A stack of the open range markers that are still unclosed
    let mut open_ranges: Vec<RangeLocationInformation> = Vec::new();
    // A list of closed ranges we've collected so far, each paired with the
    // index of the `Marker` recorded while the range was open (Go stores the
    // `*Marker` on `rangeLocationInformation`).
    let mut range_markers: Vec<(RangeMarker, Option<usize>)> = Vec::new();

    // The total number of metacharacters removed from the file (so far)
    let mut difference: usize = 0;

    // One-based current position data
    let mut line = 1usize;
    let mut column = 1usize;

    // The current marker (or maybe multi-line comment?) we're parsing, possibly
    let mut open_marker: Option<LocationInformation> = None;

    // The latest position of the start of an unflushed plain text area
    let mut last_normal_char_position: usize = 0;

    // `flush` — copy all text from `last_normal_char_position` up to
    // `last_safe_char_index`; `-1` flushes to the end of the file.
    macro_rules! flush {
        ($last_safe_char_index:expr) => {
            match $last_safe_char_index {
                -1 => output.push_str(&content[last_normal_char_position..]),
                idx => output.push_str(&content[last_normal_char_position..idx as usize]),
            }
        };
    }

    let mut state = ParserState::None;
    let (mut previous_character, mut i) = decode_rune_in_string(bytes);
    while i < bytes.len() {
        let (current_character, size) = decode_rune_in_string(&bytes[i..]);
        match state {
            ParserState::None => {
                if previous_character == '[' as i32 && current_character == '|' as i32 {
                    // found a range start
                    open_ranges.push(RangeLocationInformation {
                        location: LocationInformation {
                            position: (i - 1) - difference,
                            source_position: i - 1,
                            source_line: line,
                            source_column: column,
                        },
                        marker_index: None,
                    });
                    // copy all text up to marker position
                    flush!((i - 1) as isize);
                    last_normal_char_position = i + 1;
                    difference += 2;
                } else if previous_character == '|' as i32
                    && current_character == ']' as i32
                {
                    // found a range end
                    let Some(range_start) = open_ranges.pop() else {
                        return Err(report_error(
                            &file_name,
                            line,
                            column,
                            "Found range end with no matching start.",
                        ));
                    };

                    range_markers.push((
                        RangeMarker {
                            file_name: file_name.clone(),
                            range: TextRange::new(
                                range_start.location.position as i32,
                                ((i - 1) - difference) as i32,
                            ),
                            ls_range: lsproto::Range::default(),
                            marker: None, // resolved from the index after the scan
                        },
                        range_start.marker_index,
                    ));

                    // copy all text up to range marker position
                    flush!((i - 1) as isize);
                    last_normal_char_position = i + 1;
                    difference += 2;
                } else if previous_character == '/' as i32
                    && current_character == '*' as i32
                    && (i + 1 >= bytes.len() || bytes[i + 1] != b'/')
                {
                    // found a possible marker start
                    state = ParserState::InSlashStarMarker;
                    open_marker = Some(LocationInformation {
                        position: (i - 1) - difference,
                        source_position: i - 1,
                        source_line: line,
                        source_column: column - 1,
                    });
                } else if previous_character == '{' as i32
                    && current_character == '|' as i32
                {
                    // found an object marker start
                    state = ParserState::InObjectMarker;
                    open_marker = Some(LocationInformation {
                        position: (i - 1) - difference,
                        source_position: i - 1,
                        source_line: line,
                        source_column: column,
                    });
                    flush!((i - 1) as isize);
                }
            }
            ParserState::InObjectMarker => {
                // Object markers are only ever terminated by |} and have no content restrictions
                if previous_character == '|' as i32 && current_character == '}' as i32 {
                    let source_position = open_marker.as_ref().unwrap().source_position;
                    let object_marker_data =
                        content[source_position + 2..i - 1].trim();
                    let marker =
                        get_object_marker(&file_name, open_marker.as_ref().unwrap(), object_marker_data)?;

                    if let Some(top) = open_ranges.last_mut() {
                        top.marker_index = Some(markers.len());
                    }
                    markers.push(marker);

                    // Set the current start to point to the end of the current marker to ignore its text
                    last_normal_char_position = i + 1;
                    difference += i + 1 - source_position;

                    // Reset the state
                    open_marker = None;
                    state = ParserState::None;
                }
            }
            ParserState::InSlashStarMarker => {
                if previous_character == '*' as i32 && current_character == '/' as i32 {
                    let (position, source_position) = {
                        let open = open_marker.as_ref().unwrap();
                        (open.position, open.source_position)
                    };
                    // Record the marker
                    // start + 2 to ignore the */, -1 on the end to ignore the * (/ is next)
                    let marker_name_text = content[source_position + 2..i - 1].trim();
                    let marker = Marker {
                        file_name: file_name.clone(),
                        position: position as i32,
                        ls_position: Position::default(),
                        name: Some(marker_name_text.to_string()),
                        data: None,
                    };
                    if let Some(top) = open_ranges.last_mut() {
                        top.marker_index = Some(markers.len());
                    }
                    markers.push(marker);

                    // Set the current start to point to the end of the current marker to ignore its text
                    flush!(source_position as isize);
                    last_normal_char_position = i + 1;
                    difference += i + 1 - source_position;

                    // Reset the state
                    open_marker = None;
                    state = ParserState::None;
                } else {
                    // `stringutil.IsDigit`/`IsASCIILetter` take a `char`; an
                    // invalid decode (RuneError) satisfies none of the
                    // predicates, so `\u{FFFD}` is a safe stand-in.
                    let cur_char =
                        char::from_u32(current_character as u32).unwrap_or(char::REPLACEMENT_CHARACTER);
                    if !(stringutil::is_digit(cur_char)
                        || stringutil::is_ascii_letter(cur_char)
                        || current_character == '$' as i32
                        || current_character == '_' as i32)
                    {
                        // Invalid marker character
                        if current_character == '*' as i32
                            && i < bytes.len() - 1
                            && bytes[i + 1] == b'/'
                        {
                            // The marker is about to be closed, ignore the 'invalid' char
                        } else {
                            // We've hit a non-valid marker character, so we were actually in a block comment
                            // Bail out the text we've gathered so far back into the output
                            flush!(i as isize);
                            last_normal_char_position = i;
                            open_marker = None;
                            state = ParserState::None;
                        }
                    }
                }
            }
        }
        if current_character == '\n' as i32 && previous_character == '\r' as i32 {
            // Ignore trailing \n after \r
        } else if current_character == '\n' as i32 || current_character == '\r' as i32 {
            line += 1;
            column = 1;
        } else {
            column += 1;
            if i >= last_normal_char_position {
                previous_character = current_character;
            } else {
                // reset to avoid accidentally reusing marker delimiters as part of other markers
                previous_character = RUNE_ERROR;
            }
        }
        i += size;
    }

    // Add the remaining text
    flush!(-1isize);

    if !open_ranges.is_empty() {
        let open_range = &open_ranges[0];
        return Err(report_error(
            &file_name,
            open_range.location.source_line,
            open_range.location.source_column,
            "Unterminated range.",
        ));
    }

    if let Some(open_marker) = &open_marker {
        return Err(report_error(
            &file_name,
            open_marker.source_line,
            open_marker.source_column,
            "Unterminated marker.",
        ));
    }

    // Set LS positions for markers
    let line_map = compute_lsp_line_starts(output.as_bytes());
    let converters = new_test_converters(new_converters(
        PositionEncodingKind::UTF8,
        |_: &RootedFilePath| -> &LspLineMap { &line_map },
    ));

    let emit = file_options.get(EMIT_THIS_FILE_OPTION).map(String::as_str) == Some("true");

    let test_file_info = TestFileInfo {
        file_name: file_name.clone(),
        content: output,
        emit,
        open: file_options.get(NO_OPEN_FILE_OPTION).map(String::as_str) != Some("true"),
    };

    // `slices.SortStableFunc` — `sort_by` is stable; key: Pos asc, then End desc.
    range_markers.sort_by(|a, b| {
        a.0.range
            .pos()
            .cmp(&b.0.range.pos())
            .then_with(|| b.0.range.end().cmp(&a.0.range.end()))
    });

    // Fill marker LSP positions, then publish as `Rc`.
    for marker in &mut markers {
        marker.ls_position =
            converters.position_to_line_and_character(&test_file_info, marker.position);
    }
    let markers: Vec<Rc<Marker>> = markers.into_iter().map(Rc::new).collect();

    // Resolve each closed range's `Marker` and fill its `ls_range`.
    let mut ranges: Vec<Rc<RangeMarker>> = Vec::with_capacity(range_markers.len());
    for (mut range_marker, marker_index) in range_markers {
        range_marker.marker = marker_index.map(|idx| markers[idx].clone());
        range_marker.ls_range = lsproto::Range {
            start: converters
                .position_to_line_and_character(&test_file_info, range_marker.range.pos()),
            end: converters
                .position_to_line_and_character(&test_file_info, range_marker.range.end()),
        };
        ranges.push(Rc::new(range_marker));
    }

    Ok(TestFileWithMarkers {
        file: Rc::new(test_file_info),
        markers,
        ranges,
    })
}

/// `type testConverters struct` + `PositionToLineAndCharacter` — the
/// fourslash.go wrapper that unwraps `(Position, Fidelity)` down to the
/// position.
///
/// PORT(deferred): the shared `testConverters` type belongs to the
/// `fourslash.rs` port; this private copy provides the one method the parser
/// needs. Replace with the shared helper when it lands.
struct TestConverters<'a> {
    converters: lsconv::Converters<'a>,
}

fn new_test_converters(converters: lsconv::Converters<'_>) -> TestConverters<'_> {
    TestConverters { converters }
}

impl TestConverters<'_> {
    /// `func (c *testConverters) PositionToLineAndCharacter(script lsconv.Script, position core.TextPos) lsproto.Position`
    fn position_to_line_and_character(
        &self,
        script: &dyn lsconv::Script,
        position: TextPos,
    ) -> Position {
        self.converters.to_lsp_position(script, position).0
    }
}

/// `func getObjectMarker(fileName tspath.RootedFilePath, location *locationInformation, text string) (*Marker, error)`
fn get_object_marker(
    file_name: &RootedFilePath,
    location: &LocationInformation,
    text: &str,
) -> Result<Marker, String> {
    // Attempt to parse the marker value as JSON
    let v: serde_json::Value = match json::unmarshal(format!("{{ {text} }}").as_bytes(), &[]) {
        Ok(v) => v,
        Err(_) => {
            return Err(report_error(
                file_name,
                location.source_line,
                location.source_column,
                &format!("Unable to parse marker text {text}"),
            ));
        }
    };
    let serde_json::Value::Object(marker_value) = v else {
        return Err(report_error(
            file_name,
            location.source_line,
            location.source_column,
            "Object markers can not be empty",
        ));
    };
    if marker_value.is_empty() {
        return Err(report_error(
            file_name,
            location.source_line,
            location.source_column,
            "Object markers can not be empty",
        ));
    }

    let mut marker = Marker {
        file_name: file_name.clone(),
        position: location.position as i32,
        ls_position: Position::default(),
        name: None,
        data: Some(marker_value),
    };

    // Object markers can be anonymous
    if let Some(serde_json::Value::String(name)) =
        marker.data.as_ref().unwrap().get("name")
        && !name.is_empty()
    {
        marker.name = Some(name.clone());
    }

    Ok(marker)
}

/// `func reportError(fileName tspath.RootedFilePath, line int, col int, message string) error`
/// — `fourslashError` is a plain `error` string wrapper.
fn report_error(file_name: &RootedFilePath, line: usize, col: usize, message: &str) -> String {
    format!(
        "{} ({line},{col}): {message}",
        file_name.as_string()
    )
}

/// `func chompLeadingSpace(content string) string`
fn chomp_leading_space(content: &str) -> Cow<'_, str> {
    for line in content.split('\n') {
        if !line.is_empty() && !line.starts_with(' ') {
            return Cow::Borrowed(content);
        }
    }

    // Every line is empty or space-indented: strip one leading space each
    // (empty lines stay empty, matching Go's `len(line) > 0` guard).
    Cow::Owned(
        content
            .split('\n')
            .map(|line| line.strip_prefix(' ').unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n"),
    )
}
