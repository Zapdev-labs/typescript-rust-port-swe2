// Ported from tsc/internal/ls/lsconv/converters.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, LazyLock};

use tsc_ast::ast::Node;
use tsc_ast::diagnostic::{DiagnosticFile, DiagnosticRef, lock_diagnostic};
use tsc_ast::ids::NodeId;
use tsc_collections::{Set, new_set_from_items};
use tsc_core::context::{Context, ContextKey};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::{TextPos, TextRange};
use tsc_debug as debug;
use tsc_diagnostics::Category;
use tsc_diagnosticwriter::write_flattened_ast_diagnostic_message;
use tsc_locale::Locale;
use tsc_lsproto::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, DiagnosticTag, DocumentUri,
    IntegerOrString, LanguageKind, Location, Position, PositionEncodingKind, Range,
    StringOrMarkupContent, dynamic_file_name_to_document_uri, get_client_capabilities,
};
use tsc_spanmap::{Feature, Fidelity, SpanMap};
use tsc_tspath::{RootedFilePath, RootedPath, split_volume_path};

use crate::linemap::LspLineMap;
use crate::runes::{decode_rune_in_string, utf16_rune_len};

/// `type Converters struct`
///
/// PORT: `getLineMap` returns `*LSPLineMap` in Go — a reference into the
/// project's line-map cache. Here it returns `&'a LspLineMap`, so the closure
/// must hand out references with the converters' own lifetime (e.g. captured
/// `&'a` maps, as in the Go tests).
pub struct Converters<'a> {
    get_line_map: Box<dyn Fn(&RootedFilePath) -> &'a LspLineMap + 'a>,
    position_encoding: PositionEncodingKind,
}

/// `type MappedSpan[T Script] struct` — a mapped span together with the script
/// it was mapped into.
///
/// PORT: Go embeds `spanmap.MappedSpan`; its `Span`/`Fidelity` fields are
/// flattened here as `span`/`fidelity`.
#[derive(Clone)]
pub struct MappedSpan<T> {
    pub script: T,
    /// `spanmap.MappedSpan.Span`
    pub span: TextRange,
    /// `spanmap.MappedSpan.Fidelity`
    pub fidelity: Fidelity,
}

/// `type MappedPosition[T Script] struct` — a mapped position together with
/// the script it was mapped into.
///
/// PORT: Go embeds `spanmap.MappedPosition`; its `Position`/`Fidelity` fields
/// are flattened here as `position`/`fidelity`.
#[derive(Clone)]
pub struct MappedPosition<T> {
    pub script: T,
    /// `spanmap.MappedPosition.Position`
    pub position: TextPos,
    /// `spanmap.MappedPosition.Fidelity`
    pub fidelity: Fidelity,
}

/// `type Script interface` — a source text the converters operate over. For a
/// content-mapped file, `text()` is the content mapper's virtual output and
/// `span_map()` returns the map from that output back to the original text
/// (`original_text()`); virtual ranges are then automatically converted to
/// original coordinates (see [`Converters::to_lsp_range`]). For an ordinary
/// file `span_map()` is `None` and `original_text()` equals `text()`.
///
/// PORT: `span_map` returns `Option<Arc<SpanMap>>` (Go: `*spanmap.SpanMap`,
/// nil-safe). `SourceFile::span_map`/`DiagnosticFile::span_map` store
/// `Arc<SpanMap>` handles, so the trait hands out clones of the handle rather
/// than references.
pub trait Script {
    fn file_name(&self) -> &RootedFilePath;
    fn original_file_name(&self) -> &RootedFilePath;
    /// PORT: `&[u8]` — Go strings may contain invalid UTF-8, which the
    /// converters deliberately decode byte-wise (`utf8.DecodeRuneInString`
    /// quirks). Rust `&str` cannot represent those bytes.
    fn text(&self) -> &[u8];
    fn span_map(&self) -> Option<Arc<SpanMap>>;
    fn original_text(&self) -> &[u8];
}

/// PORT: Go's `Script` is satisfied by reference receivers (`*SourceFile`,
/// `*testScript`); this blanket impl keeps `&T` usable wherever a `Script`
/// value is expected, including as the `T` in `MappedSpan<T>`.
impl<T: Script + ?Sized> Script for &T {
    fn file_name(&self) -> &RootedFilePath {
        (**self).file_name()
    }
    fn original_file_name(&self) -> &RootedFilePath {
        (**self).original_file_name()
    }
    fn text(&self) -> &[u8] {
        (**self).text()
    }
    fn span_map(&self) -> Option<Arc<SpanMap>> {
        (**self).span_map()
    }
    fn original_text(&self) -> &[u8] {
        (**self).original_text()
    }
}

/// `*ast.SourceFile` as a [`Script`] — the arena address of the file node plus
/// the arena that owns it (Go stores a heap pointer).
///
/// PORT: Go's `*SourceFile` implements `Script` directly. The arena port needs
/// `nodes` alongside the `NodeId` for every accessor, so this wrapper carries
/// both; callers obtain it via [`source_file_script`].
#[derive(Clone, Copy)]
pub struct SourceFileScript<'a> {
    /// `NodeId` of the `Kind::SourceFile` node.
    pub file: NodeId,
    /// The AST arena (`[]ast.Node`).
    pub nodes: &'a [Node],
}

/// `SourceFileScript` constructor.
pub fn source_file_script<'a>(file: NodeId, nodes: &'a [Node]) -> SourceFileScript<'a> {
    SourceFileScript { file, nodes }
}

impl Script for SourceFileScript<'_> {
    fn file_name(&self) -> &RootedFilePath {
        self.nodes[self.file].as_source_file().file_name()
    }
    fn original_file_name(&self) -> &RootedFilePath {
        self.nodes[self.file]
            .as_source_file()
            .original_file_name(self.nodes)
    }
    fn text(&self) -> &[u8] {
        self.nodes[self.file].as_source_file().text().as_bytes()
    }
    fn span_map(&self) -> Option<Arc<SpanMap>> {
        self.nodes[self.file].as_source_file().span_map()
    }
    fn original_text(&self) -> &[u8] {
        self.nodes[self.file]
            .as_source_file()
            .original_text()
            .as_bytes()
    }
}

impl PartialEq for SourceFileScript<'_> {
    /// PORT: Go compares `*ast.SourceFile` pointers; the arena equivalent is
    /// the `NodeId` (plus the arena itself, compared by address).
    fn eq(&self, other: &Self) -> bool {
        self.file == other.file && std::ptr::eq(self.nodes, other.nodes)
    }
}

/// `*ast.Diagnostic`'s file handle as a [`Script`]. `DiagnosticFile` snapshots
/// `FileName`/`Text`/`OriginalText`/`SpanMap`; `original_file_name` (which Go
/// computes by following `CanonicalSourceFile`) resolves through `nodes` when
/// the handle still carries a node.
pub struct DiagnosticFileScript<'a> {
    pub file: &'a DiagnosticFile,
    pub nodes: &'a [Node],
}

impl Script for DiagnosticFileScript<'_> {
    fn file_name(&self) -> &RootedFilePath {
        &self.file.file_name
    }
    fn original_file_name(&self) -> &RootedFilePath {
        diagnostic_file_original_file_name(self.file, self.nodes)
    }
    fn text(&self) -> &[u8] {
        self.file.text.as_bytes()
    }
    fn span_map(&self) -> Option<Arc<SpanMap>> {
        self.file.span_map.clone()
    }
    fn original_text(&self) -> &[u8] {
        self.file.original_text.as_bytes()
    }
}

/// `file.OriginalFileName()` for a `DiagnosticFile` handle.
///
/// PORT: Go reads `CanonicalSourceFile`/`FileName` off the live `*SourceFile`;
/// a `DiagnosticFile` snapshots only the name fields, so the canonical name is
/// resolved through `file.node` + `nodes`. A detached handle (`node == None`)
/// cannot be a supplemental file, so `file_name` is already the original name.
fn diagnostic_file_original_file_name<'a>(
    file: &'a DiagnosticFile,
    nodes: &'a [Node],
) -> &'a RootedFilePath {
    match file.node {
        Some(node) => nodes[node].as_source_file().original_file_name(nodes),
        None => &file.file_name,
    }
}

/// `originalTextScript` — presents a content-mapped file's original
/// (untransformed) text as a [`Script`], so that ranges already mapped into
/// that text convert to the correct line/character positions.
pub struct OriginalTextScript<'a> {
    pub file_name: &'a RootedFilePath,
    pub text: &'a [u8],
}

impl Script for OriginalTextScript<'_> {
    fn file_name(&self) -> &RootedFilePath {
        self.file_name
    }
    fn original_file_name(&self) -> &RootedFilePath {
        self.file_name
    }
    fn text(&self) -> &[u8] {
        self.text
    }
    fn span_map(&self) -> Option<Arc<SpanMap>> {
        None
    }
    fn original_text(&self) -> &[u8] {
        self.text
    }
}

/// `func NewConverters(...) *Converters`
pub fn new_converters<'a>(
    position_encoding: PositionEncodingKind,
    get_line_map: impl Fn(&RootedFilePath) -> &'a LspLineMap + 'a,
) -> Converters<'a> {
    Converters {
        get_line_map: Box::new(get_line_map),
        position_encoding,
    }
}

impl<'a> Converters<'a> {
    /// `ToLSPRange` converts a range in a SourceFile (or a script read from
    /// the file system after declaration mapping) to an `lsproto.Range`. If
    /// the file is a content-mapped virtual SourceFile, the range is mapped
    /// through the file's span map and the fidelity of that mapping is
    /// returned. For normal files, the second return value is
    /// `Fidelity::Exact`.
    pub fn to_lsp_range(&self, script: &dyn Script, text_range: TextRange) -> (Range, Fidelity) {
        let (script, text_range, fidelity) = virtual_range_to_original(script, text_range, None);
        (
            Range {
                start: self.position_to_line_and_character(&*script, text_range.pos()),
                end: self.position_to_line_and_character(&*script, text_range.end()),
            },
            fidelity,
        )
    }

    /// `ToLSPRangeForFeature` is [`Converters::to_lsp_range`] for an LS
    /// feature. For a content-mapped file, it returns `Fidelity::None` unless
    /// the entire virtual range is covered by contiguous segments that
    /// participate in `feature`; the returned range is still the best-effort
    /// mapped range. For normal files, it behaves like
    /// [`Converters::to_lsp_range`].
    pub fn to_lsp_range_for_feature(
        &self,
        script: &dyn Script,
        text_range: TextRange,
        feature: Feature,
    ) -> (Range, Fidelity) {
        let (script, text_range, fidelity) =
            virtual_range_to_original(script, text_range, Some(feature));
        (
            Range {
                start: self.position_to_line_and_character(&*script, text_range.pos()),
                end: self.position_to_line_and_character(&*script, text_range.end()),
            },
            fidelity,
        )
    }

    /// `ToLSPPosition` converts a position in a SourceFile (or a script read
    /// from the file system after declaration mapping) to an
    /// `lsproto.Position`. Positions in content-mapped files are mapped
    /// through the file's span map; positions in normal files return
    /// `Fidelity::Exact`.
    pub fn to_lsp_position(&self, script: &dyn Script, position: TextPos) -> (Position, Fidelity) {
        let (script, position, fidelity) = virtual_position_to_original(script, position, None);
        (
            self.position_to_line_and_character(&*script, position),
            fidelity,
        )
    }

    /// `ToLSPPositionForFeature` is [`Converters::to_lsp_position`] for an LS
    /// feature. For a content-mapped file, it returns `Fidelity::None` when
    /// the virtual position is not in a segment that participates in
    /// `feature`; the returned position is still the best-effort mapped
    /// position. For normal files, it behaves like
    /// [`Converters::to_lsp_position`].
    pub fn to_lsp_position_for_feature(
        &self,
        script: &dyn Script,
        position: TextPos,
        feature: Feature,
    ) -> (Position, Fidelity) {
        let (script, position, fidelity) =
            virtual_position_to_original(script, position, Some(feature));
        (
            self.position_to_line_and_character(&*script, position),
            fidelity,
        )
    }

    /// `ToLSPLocation` converts a range in a SourceFile or script to an
    /// `lsproto.Location`. If the file is a content-mapped virtual SourceFile,
    /// the range is mapped through the file's span map and the fidelity of
    /// that mapping is returned. For normal files, the second return value is
    /// `Fidelity::Exact`. If the file is a supplemental output of a content
    /// mapper, the file's original file name is used for the URI (e.g.
    /// App.astro.0.ts -> App.astro).
    pub fn to_lsp_location(&self, script: &dyn Script, rng: TextRange) -> (Location, Fidelity) {
        let (lsp_range, fidelity) = self.to_lsp_range(script, rng);
        (
            Location {
                uri: file_name_to_document_uri(script.original_file_name()),
                range: lsp_range,
            },
            fidelity,
        )
    }

    /// `ToLSPLocationForFeature` is [`Converters::to_lsp_location`] for an LS
    /// feature. For a content-mapped file, it returns `Fidelity::None` when
    /// the virtual position is not in a segment that participates in
    /// `feature`; the returned position is still the best-effort mapped
    /// position. For normal files, it behaves like
    /// [`Converters::to_lsp_location`].
    pub fn to_lsp_location_for_feature(
        &self,
        script: &dyn Script,
        rng: TextRange,
        feature: Feature,
    ) -> (Location, Fidelity) {
        let (lsp_range, fidelity) = self.to_lsp_range_for_feature(script, rng, feature);
        (
            Location {
                uri: file_name_to_document_uri(script.original_file_name()),
                range: lsp_range,
            },
            fidelity,
        )
    }

    /// `FromLSPRange` converts an `lsproto.Range` to offsets in one Script.
    /// For a content-mapped script, results include each virtual projection
    /// covered by segments that participate in `feature`; it returns no
    /// results when no projection qualifies. Normal scripts return one exact
    /// span.
    pub fn from_lsp_range<T: Script + Clone>(
        &self,
        script: T,
        text_range: Range,
        feature: Feature,
    ) -> Vec<MappedSpan<T>> {
        self.lsp_range_to_virtual_for_scripts(vec![script], &text_range, feature)
    }

    /// `FromLSPRangeForSourceFile` converts an `lsproto.Range` to offsets in a
    /// SourceFile. When the file has supplemental content-mapper outputs,
    /// results include every qualifying virtual projection across the
    /// canonical and supplemental files. Projections not participating in
    /// `feature` are omitted.
    ///
    /// PORT: `file *ast.SourceFile` → `file: NodeId` + `nodes: &[Node]` (arena).
    pub fn from_lsp_range_for_source_file<'s>(
        &self,
        file: NodeId,
        nodes: &'s [Node],
        text_range: Range,
        feature: Feature,
    ) -> Vec<MappedSpan<SourceFileScript<'s>>> {
        let files = source_file_projections(file, nodes);
        self.lsp_range_to_virtual_for_scripts(files, &text_range, feature)
    }

    /// `FromLSPRangeIntersectingForSourceFile` projects every feature-enabled
    /// intersection with `text_range` across the canonical and supplemental
    /// virtual files. Unlike [`Converters::from_lsp_range_for_source_file`],
    /// the original range endpoints need not be mapped. This is intended for
    /// read-only range requests such as semantic tokens and inlay hints, where
    /// an editor commonly asks for a viewport spanning host markup:
    ///
    /// ```text
    /// original: <template>...</template><script>const x = 1</script><style>...</style>
    ///           [---------------- requested viewport ---------------------------------)
    ///                                           [----------) mapped script
    /// ```
    ///
    /// The result contains the script intersection even though both viewport
    /// endpoints are outside it.
    ///
    /// PORT: `file *ast.SourceFile` → `file: NodeId` + `nodes: &[Node]` (arena).
    pub fn from_lsp_range_intersecting_for_source_file<'s>(
        &self,
        file: NodeId,
        nodes: &'s [Node],
        text_range: Range,
        feature: Feature,
    ) -> Vec<MappedSpan<SourceFileScript<'s>>> {
        let files = source_file_projections(file, nodes);
        let mut result: Vec<MappedSpan<SourceFileScript>> = Vec::with_capacity(files.len());
        for script in files {
            let Some(spans) = script.span_map() else {
                result.push(MappedSpan {
                    script,
                    span: TextRange::new(
                        self.line_and_character_to_position(&script, text_range.start),
                        self.line_and_character_to_position(&script, text_range.end),
                    ),
                    fidelity: Fidelity::Exact,
                });
                continue;
            };
            let original = OriginalTextScript {
                file_name: script.original_file_name(),
                text: script.original_text(),
            };
            let original_range = TextRange::new(
                self.line_and_character_to_position(&original, text_range.start),
                self.line_and_character_to_position(&original, text_range.end),
            );
            for mapped in SpanMap::original_to_virtual_intersecting_spans(
                Some(&*spans),
                original_range,
                feature,
            ) {
                result.push(MappedSpan {
                    script,
                    span: mapped.span,
                    fidelity: mapped.fidelity,
                });
            }
        }
        result
    }

    /// `lspRangeToVirtualForScripts`
    fn lsp_range_to_virtual_for_scripts<T: Script + Clone>(
        &self,
        scripts: Vec<T>,
        text_range: &Range,
        feature: Feature,
    ) -> Vec<MappedSpan<T>> {
        let mut result: Vec<MappedSpan<T>> = Vec::with_capacity(scripts.len());
        for script in scripts {
            for mapped in self.lsp_range_to_virtual(&script, text_range, feature) {
                result.push(MappedSpan {
                    script: script.clone(),
                    span: mapped.span,
                    fidelity: mapped.fidelity,
                });
            }
        }
        result
    }

    /// `lspRangeToVirtual`
    fn lsp_range_to_virtual(
        &self,
        script: &dyn Script,
        text_range: &Range,
        feature: Feature,
    ) -> Vec<tsc_spanmap::MappedSpan> {
        let Some(spans) = script.span_map() else {
            return vec![tsc_spanmap::MappedSpan {
                span: TextRange::new(
                    self.line_and_character_to_position(script, text_range.start),
                    self.line_and_character_to_position(script, text_range.end),
                ),
                fidelity: Fidelity::Exact,
            }];
        };
        // A content-mapped script's line map is its original text's, so convert
        // against that text and then map the resulting original range forward
        // into the virtual text.
        let original = OriginalTextScript {
            file_name: script.original_file_name(),
            text: script.original_text(),
        };
        let orig_range = TextRange::new(
            self.line_and_character_to_position(&original, text_range.start),
            self.line_and_character_to_position(&original, text_range.end),
        );
        SpanMap::original_to_virtual_spans(Some(&*spans), orig_range, feature)
    }

    /// `FromLSPPosition` converts an `lsproto.Position` to offsets in one
    /// Script. For a content-mapped script, results include each virtual
    /// projection whose segment participates in `feature`; it returns no
    /// results when no projection qualifies. Normal scripts return one exact
    /// position.
    pub fn from_lsp_position<T: Script + Clone>(
        &self,
        script: T,
        position: Position,
        feature: Feature,
    ) -> Vec<MappedPosition<T>> {
        self.lsp_position_to_virtual_for_scripts(vec![script], position, feature)
    }

    /// `FromLSPPositionForSourceFile` converts an `lsproto.Position` to
    /// offsets in a SourceFile. When the file has supplemental content-mapper
    /// outputs, results include every qualifying virtual projection across the
    /// canonical and supplemental files. Projections not participating in
    /// `feature` are omitted.
    ///
    /// PORT: `file *ast.SourceFile` → `file: NodeId` + `nodes: &[Node]` (arena).
    pub fn from_lsp_position_for_source_file<'s>(
        &self,
        file: NodeId,
        nodes: &'s [Node],
        position: Position,
        feature: Feature,
    ) -> Vec<MappedPosition<SourceFileScript<'s>>> {
        let files = source_file_projections(file, nodes);
        self.lsp_position_to_virtual_for_scripts(files, position, feature)
    }

    /// `FromLSPRangeToOriginal` converts an LSP range in a content-mapped
    /// document directly to original-text offsets.
    pub fn from_lsp_range_to_original(&self, script: &dyn Script, text_range: Range) -> TextRange {
        let original = OriginalTextScript {
            file_name: script.original_file_name(),
            text: script.original_text(),
        };
        TextRange::new(
            self.line_and_character_to_position(&original, text_range.start),
            self.line_and_character_to_position(&original, text_range.end),
        )
    }

    /// `lspPositionToVirtualForScripts`
    fn lsp_position_to_virtual_for_scripts<T: Script + Clone>(
        &self,
        scripts: Vec<T>,
        position: Position,
        feature: Feature,
    ) -> Vec<MappedPosition<T>> {
        let mut result: Vec<MappedPosition<T>> = Vec::with_capacity(scripts.len());
        for script in scripts {
            for mapped in self.lsp_position_to_virtual(&script, position, feature) {
                result.push(MappedPosition {
                    script: script.clone(),
                    position: mapped.position,
                    fidelity: mapped.fidelity,
                });
            }
        }
        result
    }

    /// `lspPositionToVirtual`
    fn lsp_position_to_virtual(
        &self,
        script: &dyn Script,
        position: Position,
        feature: Feature,
    ) -> Vec<tsc_spanmap::MappedPosition> {
        let Some(spans) = script.span_map() else {
            return vec![tsc_spanmap::MappedPosition {
                position: self.line_and_character_to_position(script, position),
                fidelity: Fidelity::Exact,
            }];
        };
        let original = OriginalTextScript {
            file_name: script.original_file_name(),
            text: script.original_text(),
        };
        let orig_offset = self.line_and_character_to_position(&original, position);
        SpanMap::original_to_virtual_positions(Some(&*spans), orig_offset, feature)
    }

    /// `lineAndCharacterToPosition` — UTF-8/16 0-indexed line and character to
    /// UTF-8 offset.
    ///
    /// PORT: Go's `core.TextPos` is `int` (64-bit); `line`/`char` are u32 on
    /// the wire and intermediate sums exceed i32 only for absurd inputs. The
    /// arithmetic below runs in `i64` so `TextPos`-as-i32 storage never
    /// diverges from Go.
    fn line_and_character_to_position(
        &self,
        script: &dyn Script,
        line_and_character: Position,
    ) -> TextPos {
        debug::assert_!(
            script.span_map().is_none(),
            "raw coordinate conversion requires a non-content-mapped script"
        );

        let line_map = (self.get_line_map)(script.file_name());

        let line = i64::from(line_and_character.line);
        let char_ = i64::from(line_and_character.character);

        let text_len = script.text().len() as i64;

        // Clamp line to valid range.
        if line >= line_map.line_starts.len() as i64 {
            return text_len as TextPos;
        }

        let start = i64::from(line_map.line_starts[line as usize]);

        // Determine the end of this line (start of next line, or end of text).
        let line_end = if line + 1 < line_map.line_starts.len() as i64 {
            i64::from(line_map.line_starts[line as usize + 1])
        } else {
            text_len
        };

        if line_map.ascii_only || self.position_encoding == PositionEncodingKind::UTF8 {
            return start.max((start + char_).min(line_end)) as TextPos;
        }

        // Scan from line start counting UTF-16 code units to find the byte position.
        // Uses DecodeRuneInString (not range + RuneLen) so that invalid UTF-8 bytes
        // advance by their actual size (1) rather than RuneLen(RuneError) == 3.
        // This matches the approach in scanner.ComputePositionOfLineAndUTF16Character.
        let mut utf16_char: i64 = 0;
        let mut pos = start as usize;
        let end = line_end as usize;
        let text = script.text();
        while pos < end {
            let (r, size) = decode_rune_in_string(&text[pos..]);
            let u16_len = i64::from(utf16_rune_len(r));
            if utf16_char + u16_len > char_ {
                break;
            }
            utf16_char += u16_len;
            pos += size;
        }

        pos as TextPos
    }

    /// `positionToLineAndCharacter` — UTF-8 offset to UTF-8/16 0-indexed line
    /// and character.
    fn position_to_line_and_character(&self, script: &dyn Script, position: TextPos) -> Position {
        debug::assert_!(
            script.span_map().is_none(),
            "raw coordinate conversion requires a non-content-mapped script"
        );

        let text = script.text();
        let position = position.clamp(0, text.len() as TextPos);

        let line_map = (self.get_line_map)(script.file_name());

        // `slices.BinarySearch` — the insertion point is the first index whose
        // line start is >= position.
        let mut line = line_map
            .line_starts
            .partition_point(|&start| start < position) as i32;
        let is_line_start = (line as usize) < line_map.line_starts.len()
            && line_map.line_starts[line as usize] == position;
        if !is_line_start {
            line -= 1;
        }
        // `max(0, min(line, len(LineStarts)-1))` — ordered this way so an
        // (impossible) empty line map yields the same out-of-bounds index
        // panic Go's `lineMap.LineStarts[0]` would, instead of a `clamp`
        // min>max panic.
        line = (line.min(line_map.line_starts.len() as i32 - 1)).max(0);

        // The current line ranges from lineMap.LineStarts[line] (or 0) to
        // lineMap.LineStarts[line+1] (or len(text)).
        let start = line_map.line_starts[line as usize];

        let character: TextPos =
            if line_map.ascii_only || self.position_encoding == PositionEncodingKind::UTF8 {
                position - start
            } else {
                // We need to rescan the text as UTF-16 to find the character offset.
                //
                // PORT: Go ranges over `text[start:position]` (utf8 range decoding,
                // RuneError advancing one byte for invalid input);
                // `decode_rune_in_string` gives the same stepping.
                let mut character: TextPos = 0;
                let mut pos = start as usize;
                while pos < position as usize {
                    let (r, size) = decode_rune_in_string(&text[pos..]);
                    character += utf16_rune_len(r);
                    pos += size;
                }
                character
            };

        Position {
            line: line as u32,
            character: character as u32,
        }
    }
}

/// `sourceFileProjections`
///
/// PORT: `file *ast.SourceFile` → `NodeId` + arena.
fn source_file_projections<'a>(file: NodeId, nodes: &'a [Node]) -> Vec<SourceFileScript<'a>> {
    let supplemental = nodes[file].as_source_file().supplemental_source_files();
    let mut files = Vec::with_capacity(1 + supplemental.len());
    files.push(SourceFileScript { file, nodes });
    for &supplemental_file in supplemental {
        files.push(SourceFileScript {
            file: supplemental_file,
            nodes,
        });
    }
    files
}

/// `virtualRangeToOriginal` maps a content mapper's virtual range back to its
/// original text. A `None` feature bypasses feature filtering for diagnostics
/// and edits.
///
/// PORT: Go returns the `Script` interface; `Box<dyn Script>` stands in for
/// the interface value, and `&dyn Script` boxes through the `Script` impl on
/// `&T`.
fn virtual_range_to_original<'s>(
    script: &'s dyn Script,
    text_range: TextRange,
    feature: Option<Feature>,
) -> (Box<dyn Script + 's>, TextRange, Fidelity) {
    let Some(span_map) = script.span_map() else {
        return (Box::new(script), text_range, Fidelity::Exact);
    };
    let (mapped, fidelity) = match feature {
        None => SpanMap::virtual_to_original_span(Some(&*span_map), text_range),
        Some(feature) => {
            SpanMap::virtual_to_original_span_for_feature(Some(&*span_map), text_range, feature)
        }
    };
    (
        Box::new(OriginalTextScript {
            file_name: script.original_file_name(),
            text: script.original_text(),
        }),
        mapped,
        fidelity,
    )
}

/// `virtualPositionToOriginal` is the single-position analog of
/// [`virtual_range_to_original`].
fn virtual_position_to_original<'s>(
    script: &'s dyn Script,
    position: TextPos,
    feature: Option<Feature>,
) -> (Box<dyn Script + 's>, TextPos, Fidelity) {
    let Some(span_map) = script.span_map() else {
        return (Box::new(script), position, Fidelity::Exact);
    };
    let (mapped, fidelity) = match feature {
        None => SpanMap::virtual_to_original_position(Some(&*span_map), position),
        Some(feature) => {
            SpanMap::virtual_to_original_position_for_feature(Some(&*span_map), position, feature)
        }
    };
    (
        Box::new(OriginalTextScript {
            file_name: script.original_file_name(),
            text: script.original_text(),
        }),
        mapped,
        fidelity,
    )
}

/// `LanguageKindToScriptKind`
pub fn language_kind_to_script_kind(language_id: &LanguageKind) -> ScriptKind {
    match language_id.as_str() {
        "typescript" => ScriptKind::Ts,
        "typescriptreact" => ScriptKind::Tsx,
        "javascript" => ScriptKind::Js,
        "javascriptreact" => ScriptKind::Jsx,
        "json" => ScriptKind::Json,
        _ => ScriptKind::Unknown,
    }
}

// https://github.com/microsoft/vscode-uri/blob/edfdccd976efaf4bb8fdeca87e97c47257721729/src/uri.ts#L455
//
// PORT: `strings.NewReplacer` — a single left-to-right pass replacing each
// listed ASCII character.
fn extra_escape_replacer(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        let escaped: &str = match c {
            ':' => "%3A",
            '/' => "%2F",
            '?' => "%3F",
            '#' => "%23",
            '[' => "%5B",
            ']' => "%5D",
            '@' => "%40",
            '!' => "%21",
            '$' => "%24",
            '&' => "%26",
            '\'' => "%27",
            '(' => "%28",
            ')' => "%29",
            '*' => "%2A",
            '+' => "%2B",
            ',' => "%2C",
            ';' => "%3B",
            '=' => "%3D",
            ' ' => "%20",
            _ => {
                out.push(c);
                continue;
            }
        };
        out.push_str(escaped);
    }
    out
}

/// `url.PathEscape` — percent-encodes `s` for use inside a URL path segment
/// (`encodePathSegment` mode: alphanumerics and `-_.~$&+:=@` pass through;
/// `/;,?` and every other byte are escaped as %XX of the UTF-8 bytes).
fn path_escape(s: &str) -> String {
    const UPPERHEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if should_escape_path_segment(b) {
            out.push('%');
            out.push(UPPERHEX[(b >> 4) as usize] as char);
            out.push(UPPERHEX[(b & 0x0f) as usize] as char);
        } else {
            out.push(b as char);
        }
    }
    out
}

/// `url.shouldEscape(c, encodePathSegment)`
fn should_escape_path_segment(c: u8) -> bool {
    // §2.3 Unreserved characters (alphanumerics)
    if c.is_ascii_alphanumeric() {
        return false;
    }
    match c {
        // §2.3 Unreserved characters (mark)
        b'-' | b'_' | b'.' | b'~' => false,
        // §2.2 Reserved characters (reserved); for a path segment the RFC
        // saves '/', ';', ',' and '?'.
        b'$' | b'&' | b'+' | b',' | b'/' | b':' | b';' | b'=' | b'?' | b'@' => {
            matches!(c, b'/' | b';' | b',' | b'?')
        }
        // Everything else must be escaped.
        _ => true,
    }
}

/// `FileNameToDocumentURI`
pub fn file_name_to_document_uri(file_name: &RootedFilePath) -> DocumentUri {
    path_to_document_uri(&file_name.as_path())
}

/// `PathToDocumentURI`
pub fn path_to_document_uri(rooted_path: &RootedPath) -> DocumentUri {
    let path = rooted_path.as_string();
    if tsc_bundled::is_bundled(path) {
        return DocumentUri(path.to_string());
    }
    if rooted_path.is_dynamic() {
        return dynamic_file_name_to_document_uri(rooted_path);
    }

    let (volume, rest, _) = split_volume_path(path);
    let volume = if volume.is_empty() {
        volume
    } else {
        format!("/{}", extra_escape_replacer(&volume))
    };

    let rest = rest.strip_prefix("//").unwrap_or(rest);

    let parts: Vec<String> = rest
        .split('/')
        .map(|part| extra_escape_replacer(&path_escape(part)))
        .collect();

    DocumentUri(format!("file://{}{}", volume, parts.join("/")))
}

/// `type diagnosticOptions struct`
struct DiagnosticOptions<'a> {
    report_style_checks_as_warnings: bool,
    related_information: bool,
    tag_value_set: &'a [DiagnosticTag],
    visual_studio: bool,
}

/// `locale.FromContext(ctx)`
///
/// PORT: `tsc_locale::from_context` is generic over the `LocaleContext` trait,
/// which `tsc_core::context::Context` does not implement (`tsc-locale` has no
/// dependencies, so the impl cannot live there, and the orphan rule forbids it
/// here). We read the same-shaped context value under an lsconv-local key —
/// `with_locale` below is `locale.WithLocale`. Nothing in the workspace stores
/// a locale on `Context` yet, so this currently always yields
/// `Locale::default()`, matching Go when no locale was attached.
struct LocaleKey;

const LOCALE_KEY: ContextKey<LocaleKey, Locale> = ContextKey::new();

/// `locale.WithLocale(ctx, locale)` — see the `locale_from_context` PORT note.
pub fn with_locale(ctx: &Context, locale: Locale) -> Context {
    ctx.with_value(LOCALE_KEY, locale)
}

/// `locale.FromContext(ctx)` — see the `LOCALE_KEY` PORT note.
fn locale_from_context(ctx: &Context) -> Locale {
    ctx.value(LOCALE_KEY).cloned().unwrap_or_default()
}

/// `DiagnosticToLSPPull` converts a diagnostic for pull diagnostics
/// (textDocument/diagnostic).
///
/// PORT: `nodes` carries the AST arena that `ast.Diagnostic` file handles
/// resolve through (Go's `File()` returns a live `*SourceFile`).
pub fn diagnostic_to_lsp_pull(
    ctx: &Context,
    converters: &Converters<'_>,
    diagnostic: &DiagnosticRef,
    nodes: &[Node],
    report_style_checks_as_warnings: bool,
) -> Diagnostic {
    let client_caps = get_client_capabilities(ctx);
    let client_diagnostic_caps = &client_caps.text_document.diagnostic;
    diagnostic_to_lsp(
        ctx,
        converters,
        diagnostic,
        nodes,
        &DiagnosticOptions {
            report_style_checks_as_warnings, // !!! get through context UserPreferences
            related_information: client_diagnostic_caps.related_information,
            tag_value_set: &client_diagnostic_caps.tag_support.value_set,
            visual_studio: client_caps.vs_supports_visual_studio_extensions,
        },
    )
}

/// `DiagnosticToLSPPush` converts a diagnostic for push diagnostics
/// (textDocument/publishDiagnostics).
///
/// PORT: `nodes` carries the AST arena that `ast.Diagnostic` file handles
/// resolve through (Go's `File()` returns a live `*SourceFile`).
pub fn diagnostic_to_lsp_push(
    ctx: &Context,
    converters: &Converters<'_>,
    diagnostic: &DiagnosticRef,
    nodes: &[Node],
) -> Diagnostic {
    let client_caps = get_client_capabilities(ctx);
    let client_diagnostic_caps = &client_caps.text_document.publish_diagnostics;
    diagnostic_to_lsp(
        ctx,
        converters,
        diagnostic,
        nodes,
        &DiagnosticOptions {
            report_style_checks_as_warnings: false,
            related_information: client_diagnostic_caps.related_information,
            tag_value_set: &client_diagnostic_caps.tag_support.value_set,
            visual_studio: client_caps.vs_supports_visual_studio_extensions,
        },
    )
}

// https://github.com/microsoft/vscode/blob/93e08afe0469712706ca4e268f778cfadf1a43ef/extensions/typescript-language-features/src/typeScriptServiceClientHost.ts#L40C7-L40C29
static STYLE_CHECK_DIAGNOSTICS: LazyLock<Set<i32>> = LazyLock::new(|| {
    new_set_from_items([
        tsc_diagnostics::X_0_is_declared_but_never_used.code(),
        tsc_diagnostics::X_0_is_declared_but_its_value_is_never_read.code(),
        tsc_diagnostics::Property_0_is_declared_but_its_value_is_never_read.code(),
        tsc_diagnostics::All_imports_in_import_declaration_are_unused.code(),
        tsc_diagnostics::Unreachable_code_detected.code(),
        tsc_diagnostics::Unused_label.code(),
        tsc_diagnostics::Fallthrough_case_in_switch.code(),
        tsc_diagnostics::Not_all_code_paths_return_a_value.code(),
    ])
});

/// `diagnosticToLSP`
fn diagnostic_to_lsp(
    ctx: &Context,
    converters: &Converters<'_>,
    diagnostic: &DiagnosticRef,
    nodes: &[Node],
    opts: &DiagnosticOptions<'_>,
) -> Diagnostic {
    let locale = locale_from_context(ctx);
    let (
        severity,
        diagnostic_file,
        loc,
        source,
        code,
        reports_unnecessary,
        reports_deprecated,
        related_information,
    ) = {
        // PORT: the lock is taken once to snapshot every field the conversion
        // reads; the guard is dropped before any nested `lock_diagnostic`
        // (related diagnostics, `message_chain_to_string`'s flattening) so
        // self-referential chains cannot deadlock Go's unlocked recursion.
        let d = lock_diagnostic(diagnostic);
        let mut severity = diagnostic_severity(d.category());
        if opts.report_style_checks_as_warnings
            && severity == DiagnosticSeverity::Error
            && STYLE_CHECK_DIAGNOSTICS.has(&d.code())
        {
            severity = DiagnosticSeverity::Warning;
        }
        (
            severity,
            d.file().cloned(),
            d.loc(),
            d.source().to_string(),
            d.code(),
            d.reports_unnecessary(),
            d.reports_deprecated(),
            d.related_information().to_vec(),
        )
    };

    let mut related_information_out: Vec<DiagnosticRelatedInformation> = Vec::new();
    if opts.related_information {
        related_information_out = Vec::with_capacity(related_information.len());
        for related in &related_information {
            let (related_file, related_loc, related_source, related_message) = {
                let r = lock_diagnostic(related);
                (
                    r.file().cloned(),
                    r.loc(),
                    r.source().to_string(),
                    r.localize(&locale),
                )
            };
            // PORT: Go's `related.File().OriginalFileName()` nil-pointer
            // panics when a related diagnostic has no file; fail fast with a
            // message instead.
            let Some(related_file) = related_file else {
                debug::fail("related diagnostic without a file")
            };
            let (script, loc) =
                diagnostic_script_and_range(&related_file, related_loc, &related_source, nodes);
            let (mut related_range, fidelity) = converters.to_lsp_range(&*script, loc);
            if fidelity.is_none() {
                // Related diagnostic information cannot omit its location. Use an explicit file-level
                // location instead of presenting the synthesized span's insertion point as related source.
                related_range = Range::default();
            }
            related_information_out.push(DiagnosticRelatedInformation {
                location: Location {
                    uri: file_name_to_document_uri(diagnostic_file_original_file_name(
                        &related_file,
                        nodes,
                    )),
                    range: related_range,
                },
                message: related_message,
            });
        }
    }

    let mut tags: Vec<DiagnosticTag> = Vec::new();
    if !opts.tag_value_set.is_empty() && (reports_unnecessary || reports_deprecated) {
        tags.reserve(2);
        if reports_unnecessary && opts.tag_value_set.contains(&DiagnosticTag::Unnecessary) {
            tags.push(DiagnosticTag::Unnecessary);
        }
        if reports_deprecated && opts.tag_value_set.contains(&DiagnosticTag::Deprecated) {
            tags.push(DiagnosticTag::Deprecated);
        }
    }

    // For diagnostics without a file (e.g., program diagnostics), use a zero range
    let mut lsp_range = Range::default();
    if let Some(file) = &diagnostic_file {
        let (script, loc) = diagnostic_script_and_range(file, loc, &source, nodes);
        let fidelity;
        (lsp_range, fidelity) = converters.to_lsp_range(&*script, loc);
        if fidelity.is_none() {
            // Diagnostics must carry a range. A zero range honestly means "this file" when the
            // diagnostic arose entirely in synthesized code and has no original source span.
            lsp_range = Range::default();
        }
    }

    let mut source_text = source;
    if source_text.is_empty() {
        source_text = "ts".to_string();
    }
    let code = if opts.visual_studio {
        IntegerOrString {
            integer: None,
            string: Some(format!("TS{code}")),
        }
    } else {
        IntegerOrString {
            integer: Some(code),
            string: None,
        }
    };

    Diagnostic {
        range: lsp_range,
        code: Some(code),
        severity: Some(severity),
        message: StringOrMarkupContent {
            string: Some(message_chain_to_string(diagnostic, nodes, &locale)),
            markup_content: None,
        },
        source: Some(source_text),
        related_information: ptr_to_slice_if_non_empty(related_information_out),
        tags: ptr_to_slice_if_non_empty(tags),
        ..Default::default()
    }
}

/// `diagnosticScriptAndRange` resolves the text basis and range to report a
/// diagnostic against. For a content-mapped file it maps the diagnostic's
/// virtual range back to the original text so the range lines up with what
/// the editor shows; the original text's line map is already what `getLineMap`
/// returns for the file. A range in synthesized code has no original
/// counterpart, so it is surfaced at the top of the file. Non-mapped files
/// are returned unchanged.
///
/// PORT: `file *ast.SourceFile` → `&DiagnosticFile` + `nodes` (the
/// diagnostic's file handle resolves through the arena). Go permits a nil
/// file here (it returns it unchanged and the subsequent `script.SpanMap()`
/// call nil-panics); callers pass `Option` handles that are already known
/// non-nil.
fn diagnostic_script_and_range<'a>(
    file: &'a DiagnosticFile,
    loc: TextRange,
    source: &str,
    nodes: &'a [Node],
) -> (Box<dyn Script + 'a>, TextRange) {
    if file.span_map.is_none() {
        return (Box::new(DiagnosticFileScript { file, nodes }), loc);
    }
    let original: Box<dyn Script + 'a> = Box::new(OriginalTextScript {
        file_name: diagnostic_file_original_file_name(file, nodes),
        text: file.original_text.as_bytes(),
    });
    if !source.is_empty() {
        // A content mapper's own diagnostics already carry original-text ranges.
        return (original, loc);
    }
    let (mapped, fidelity) = SpanMap::virtual_to_original_span(file.span_map.as_deref(), loc);
    if fidelity.is_none() {
        // Entirely synthesized code has no original location; surface it at the top of the file.
        return (original, TextRange::new(0, 0));
    }
    (original, mapped)
}

/// `diagnosticSeverity` maps a diagnostic category to its LSP severity.
fn diagnostic_severity(category: Category) -> DiagnosticSeverity {
    match category {
        Category::Suggestion => DiagnosticSeverity::Hint,
        Category::Message => DiagnosticSeverity::Information,
        Category::Warning => DiagnosticSeverity::Warning,
        // PORT: Go's `default` arm; `Category` has no other variants.
        Category::Error => DiagnosticSeverity::Error,
    }
}

/// `messageChainToString`
fn message_chain_to_string(diagnostic: &DiagnosticRef, nodes: &[Node], locale: &Locale) -> String {
    if lock_diagnostic(diagnostic).message_chain().is_empty() {
        return lock_diagnostic(diagnostic).localize(locale);
    }
    // PORT: `nodes` is threaded through so the AST diagnostic's file handle
    // can resolve against the arena inside `diagnosticwriter` (Go's
    // `File()` returns a live `*SourceFile`).
    let mut b = Vec::new();
    write_flattened_ast_diagnostic_message(&mut b, diagnostic, nodes, "\n", locale);
    String::from_utf8_lossy(&b).into_owned()
}

/// `ptrToSliceIfNonEmpty`
fn ptr_to_slice_if_non_empty<T>(s: Vec<T>) -> Option<Vec<T>> {
    if s.is_empty() { None } else { Some(s) }
}
