// Ported from tsc/internal/spanmap/spanmap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// PORT: the Go doc comments below contain tab-indented ASCII diagrams; kept
// verbatim per the porting contract.
#![allow(clippy::tabs_in_doc_comments)]

// Package spanmap provides bidirectional span-aware mapping between a content mapper's virtual text
// and its original, untransformed source. Unlike a source map, which records
// point correspondences and leaves spans and "no origin" implicit, a SpanMap records explicit segments
// for the parts of the virtual text that correspond to the original; positions not covered by any
// segment are synthesized (virtual content with no original counterpart). All positions are absolute
// offsets (core.TextPos), matching the compiler's TextRange model.

// Keep this in sync with spanMap.ts

use std::fmt;
use std::sync::OnceLock;

use tsc_core::text::{TextPos, TextRange};
use tsc_json as json;

/// Kind describes how positions inside a segment relate the virtual span to the original span.
///
/// PORT: `type Kind int32` → newtype `Kind(pub i32)`. An enum is not used
/// because unmarshalled tuples may carry invalid kind values that
/// `validate` must be able to report.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Kind(pub i32);

// PORT: associated consts keep the Go constant names minus the type prefix
// (`KindVerbatim` → `Kind::Verbatim`); the allow preserves the Go casing.
#[allow(non_upper_case_globals)]
impl Kind {
    /// KindVerbatim segments are length-preserving: the virtual and original spans have the same
    /// length and interior positions map 1:1 (OriginalPos = pos - VirtualStart + OriginalStart). A virtual span
    /// fully within a verbatim segment maps to an exact original span.
    pub const Verbatim: Kind = Kind(0);
    /// KindAtom segments map a virtual span to an original span as a whole; interior positions are not
    /// interpolatable (the lengths may differ), so positions within clamp to the segment's endpoints.
    /// Used for renamed identifiers or short expressions.
    pub const Atom: Kind = Kind(1);
    /// KindAlias has atom geometry, but additionally asserts that the virtual and original texts are
    /// names for the same logical entity. Diagnostic presentation may substitute the original name.
    pub const Alias: Kind = Kind(2);
}

/// Feature selects which language-service operations may use a segment. Diagnostics are intentionally not
/// represented: diagnostics on virtual text may not opt out of reporting. Text edits additionally require exact
/// verbatim geometry regardless of feature participation.
///
/// PORT: `type Feature int32` → newtype `Feature(pub i32)` (a bitmask, so a
/// Rust enum cannot represent combined values).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Feature(pub i32);

// PORT: Go's `Feature = 1 << iota` block → explicit `1 << n` values.
#[allow(non_upper_case_globals)]
impl Feature {
    pub const Hover: Feature = Feature(1 << 0);
    pub const SignatureHelp: Feature = Feature(1 << 1);
    pub const Completion: Feature = Feature(1 << 2);
    pub const Definition: Feature = Feature(1 << 3);
    pub const TypeDefinition: Feature = Feature(1 << 4);
    pub const Implementation: Feature = Feature(1 << 5);
    pub const References: Feature = Feature(1 << 6);
    pub const DocumentHighlights: Feature = Feature(1 << 7);
    pub const Rename: Feature = Feature(1 << 8);
    pub const CallHierarchy: Feature = Feature(1 << 9);
    pub const CodeActions: Feature = Feature(1 << 10);
    pub const Formatting: Feature = Feature(1 << 11);
    pub const InlayHints: Feature = Feature(1 << 12);
    pub const SemanticTokens: Feature = Feature(1 << 13);
    pub const FoldingRanges: Feature = Feature(1 << 14);
    pub const SelectionRanges: Feature = Feature(1 << 15);
    pub const LinkedEditing: Feature = Feature(1 << 16);
    pub const AutoInsert: Feature = Feature(1 << 17);
    pub const DocumentSymbols: Feature = Feature(1 << 18);
    pub const CodeLens: Feature = Feature(1 << 19);
    pub const None: Feature = Feature(0);
    pub const All: Feature = Feature((Feature::CodeLens.0 << 1) - 1);
}

const FEATURE_MASK: Feature = Feature::All;

// Go's `|` on Feature values.
impl std::ops::BitOr for Feature {
    type Output = Feature;
    fn bitor(self, rhs: Feature) -> Feature {
        Feature(self.0 | rhs.0)
    }
}

// Go's `&` on Feature values.
impl std::ops::BitAnd for Feature {
    type Output = Feature;
    fn bitand(self, rhs: Feature) -> Feature {
        Feature(self.0 & rhs.0)
    }
}

// Go's `&^` (AND NOT) becomes `& !`.
impl std::ops::Not for Feature {
    type Output = Feature;
    fn not(self) -> Feature {
        Feature(!self.0)
    }
}

// Mixed comparisons with untyped constants (`segment.Features&feature != 0`
// in Go) compare against i32.
impl PartialEq<i32> for Feature {
    fn eq(&self, other: &i32) -> bool {
        self.0 == *other
    }
}

/// Fidelity describes how faithfully a mapped span reflects the original.
///
/// PORT: `type Fidelity int32` → newtype `Fidelity(pub i32)` (same shape as
/// `Kind`; Go's named int types are open sets).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Fidelity(pub i32);

#[allow(non_upper_case_globals)]
impl Fidelity {
    /// FidelityExact means the span fell entirely within a single verbatim segment and maps precisely.
    pub const Exact: Fidelity = Fidelity(0);
    /// FidelityAtom means the span fell within a single atom segment and maps to that atom's span.
    pub const Atom: Fidelity = Fidelity(1);
    /// FidelityApproximate means the span crossed segment boundaries; its endpoints were mapped and clamped.
    pub const Approximate: Fidelity = Fidelity(2);
    /// FidelityNone means the span had no original counterpart (it was entirely synthesized).
    pub const None: Fidelity = Fidelity(3);
}

impl Fidelity {
    /// IsExact reports whether the mapping was fully faithful — the input fell within a single verbatim span —
    /// so the result maps 1:1 and can host a text edit written back to the original.
    pub fn is_exact(self) -> bool {
        self == Fidelity::Exact
    }

    /// IsSingleSegment reports whether the input fell within one segment, verbatim or atom, so the result is a
    /// concrete location rather than a best-effort approximation across boundaries or a synthesized gap.
    pub fn is_single_segment(self) -> bool {
        self == Fidelity::Exact || self == Fidelity::Atom
    }

    /// IsNone reports whether the input had no original counterpart, meaning the mapped result is a synthesized
    /// gap that does not correspond to any location in the original text.
    pub fn is_none(self) -> bool {
        self == Fidelity::None
    }
}

/// Segment maps the half-open virtual range [VirtualStart, VirtualEnd) to the half-open original range
/// [OriginalStart, OriginalEnd). Features controls language-service participation; diagnostics and exact edit mapping
/// deliberately bypass it.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct Segment {
    pub virtual_start: TextPos,
    pub virtual_end: TextPos,
    pub original_start: TextPos,
    pub original_end: TextPos,
    pub kind: Kind,
    pub features: Feature,
}

/// MappedPosition is one virtual projection of an original position and its mapping fidelity.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct MappedPosition {
    pub position: TextPos,
    pub fidelity: Fidelity,
}

/// MappedSpan is one virtual projection of an original range and its mapping fidelity.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct MappedSpan {
    pub span: TextRange,
    pub fidelity: Fidelity,
}

// PORT: tsc_core's TextRange does not implement Debug yet; format the span as
// a (pos, end) tuple so assert_eq! output stays useful.
impl fmt::Debug for MappedSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MappedSpan")
            .field("span", &(self.span.pos(), self.span.end()))
            .field("fidelity", &self.fidelity)
            .finish()
    }
}

/// SpanMap is a sparse, ordered set of segments over a content mapper's virtual text. Segments do not
/// need to cover the whole text: any virtual position not inside a segment is synthesized (it has no
/// original counterpart). An empty SpanMap therefore describes fully synthesized virtual text.
///
/// PORT: Go's `*SpanMap` methods all accept a nil receiver (a nil map maps
/// identically); they take `this: Option<&SpanMap>` here — call as
/// `SpanMap::virtual_to_original_span(m.as_ref(), r)`.
pub struct SpanMap {
    segments: Vec<Segment>,

    /// origOnce guards lazy construction of the interval index used for original-to-virtual lookups.
    /// PORT: `origOnce sync.Once` + `originalIndex *originalIndex` collapse
    /// into a single `OnceLock` (same once-only lazy semantics).
    original_index: OnceLock<OriginalIndex>,
}

/// Validation failures. A content mapper is required to provide a valid span map; these describe the
/// ways a map can be malformed, so the compiler can attribute the failure to the mapper precisely and
/// point the mapper's author at the offending location.
///
/// PORT: `type MappingErrorKind int` → newtype `MappingErrorKind(pub i32)`;
/// kept open so `error`'s `default` arm remains reachable.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct MappingErrorKind(pub i32);

#[allow(non_upper_case_globals)]
impl MappingErrorKind {
    /// MappingErrorKindOverlap means the segments overlap, run backwards, or extend past the end of the
    /// virtual text (they must be ordered and disjoint in virtual space).
    pub const Overlap: MappingErrorKind = MappingErrorKind(0);
    /// MappingErrorKindOutOfBounds means a segment's original span lies outside the original text.
    pub const OutOfBounds: MappingErrorKind = MappingErrorKind(1);
    /// MappingErrorKindVerbatimMismatch means a verbatim segment's virtual and original text differ.
    pub const VerbatimMismatch: MappingErrorKind = MappingErrorKind(2);
    /// MappingErrorKindKind means a segment uses an unsupported mapping kind.
    pub const Kind: MappingErrorKind = MappingErrorKind(3);
    /// MappingErrorKindFeature means a feature annotation contains unsupported flags.
    pub const Feature: MappingErrorKind = MappingErrorKind(4);
}

/// MappingError describes a single span map validation failure, including the offsets involved so the mapper's
/// author can locate it. VirtualPos is an offset into the virtual text; OriginalPos is an offset into the
/// original content. Either may be unused (zero) depending on Kind.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct MappingError {
    pub kind: MappingErrorKind,
    pub virtual_pos: TextPos,
    pub original_pos: TextPos,
}

/// Error describes the invalid mapping and the coordinate at which it was detected.
///
/// PORT: Go's `func (p *MappingError) Error() string` becomes `fmt::Display`
/// plus the `std::error::Error` impl below; the switch's `default` arm is the
/// trailing `_` arm (reachable because `MappingErrorKind` is an open i32).
impl fmt::Display for MappingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            MappingErrorKind::Overlap => write!(
                f,
                "content mapper position mappings overlap or are out of order near virtual offset {}",
                self.virtual_pos
            ),
            MappingErrorKind::OutOfBounds => write!(
                f,
                "content mapper position mapping points outside the original content at original offset {}",
                self.original_pos
            ),
            MappingErrorKind::VerbatimMismatch => write!(
                f,
                "content mapper verbatim mapping does not match the original content at virtual offset {}, original offset {}",
                self.virtual_pos, self.original_pos
            ),
            MappingErrorKind::Kind => write!(
                f,
                "content mapper position mapping has an invalid kind at virtual offset {}",
                self.virtual_pos
            ),
            MappingErrorKind::Feature => write!(
                f,
                "content mapper position mappings have invalid features near original offset {}",
                self.original_pos
            ),
            _ => write!(f, "content mapper produced an invalid position mapping"),
        }
    }
}

impl std::error::Error for MappingError {}

impl SpanMap {
    /// Validate enforces the content-mapper span map contract against the virtual and original text: the
    /// segments must be ordered and disjoint in virtual space and stay within the virtual text, every
    /// original span must lie within the original text, and every verbatim segment's text must match the
    /// original exactly. Gaps are allowed (they map as synthesized) and an empty map is valid. It returns the
    /// first violation found, or nil if the map is valid.
    ///
    /// PORT: `*MappingError` return → `Option<MappingError>`; nil receiver →
    /// `this: Option<&SpanMap>`. `r#virtual`/`original` are compared as bytes
    /// (Go slices strings by byte offset; `str` indexing would panic on
    /// non-char boundaries). Go's `virtual` parameter is a Rust keyword →
    /// `r#virtual`.
    pub fn validate(
        this: Option<&SpanMap>,
        r#virtual: &str,
        original: &str,
    ) -> Option<MappingError> {
        let m = this?;
        let virtual_len: TextPos = r#virtual.len() as TextPos;
        let orig_len: TextPos = original.len() as TextPos;
        let mut previous_virtual_end: TextPos = 0;
        for s in &m.segments {
            if s.virtual_start < previous_virtual_end
                || s.virtual_end < s.virtual_start
                || s.virtual_end > virtual_len
            {
                return Some(MappingError {
                    kind: MappingErrorKind::Overlap,
                    virtual_pos: s.virtual_start,
                    ..MappingError::default()
                });
            }
            previous_virtual_end = s.virtual_end;
            if s.original_start < 0
                || s.original_end < s.original_start
                || s.original_end > orig_len
            {
                return Some(MappingError {
                    kind: MappingErrorKind::OutOfBounds,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_end,
                });
            }
            if s.kind != Kind::Verbatim && s.kind != Kind::Atom && s.kind != Kind::Alias {
                return Some(MappingError {
                    kind: MappingErrorKind::Kind,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_start,
                });
            }
            if s.kind == Kind::Verbatim
                && (s.virtual_end - s.virtual_start != s.original_end - s.original_start
                    || r#virtual.as_bytes()[s.virtual_start as usize..s.virtual_end as usize]
                        != original.as_bytes()[s.original_start as usize..s.original_end as usize])
            {
                return Some(MappingError {
                    kind: MappingErrorKind::VerbatimMismatch,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_start,
                });
            }
            if s.features & !FEATURE_MASK != 0 {
                return Some(MappingError {
                    kind: MappingErrorKind::Feature,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_start,
                });
            }
        }
        None
    }

    /// New builds a SpanMap from segments, sorted by virtual start. Segments describe only the parts of the
    /// virtual text that correspond to the original; anything not covered maps as synthesized.
    ///
    /// PORT: Go returns `*SpanMap` (always non-nil) → value return. Go clones
    /// the input slice; taking `&[Segment]` and `to_vec` preserves that.
    /// `slices.SortFunc` is unstable → `sort_unstable_by`.
    pub fn new(segments: &[Segment]) -> SpanMap {
        let mut sorted = segments.to_vec();
        sorted.sort_unstable_by(|a, b| a.virtual_start.wrapping_sub(b.virtual_start).cmp(&0));
        SpanMap {
            segments: sorted,
            original_index: OnceLock::new(),
        }
    }

    /// Segments returns the map's segments ordered by virtual start.
    ///
    /// PORT: Go returns `slices.Clone(m.segments)` (nil for a nil map) →
    /// `Vec::new()` for `None`.
    pub fn segments(this: Option<&SpanMap>) -> Vec<Segment> {
        let Some(m) = this else {
            return Vec::new();
        };
        m.segments.clone()
    }

    /// VirtualToOriginalSpan maps a virtual range to an original range, along with the fidelity of the result. A virtual
    /// range that lies entirely in a gap between segments (or in an empty map) is synthesized: it maps to the
    /// insertion point in the original with FidelityNone. A nil SpanMap maps identically.
    pub fn virtual_to_original_span(this: Option<&SpanMap>, r: TextRange) -> (TextRange, Fidelity) {
        let Some(m) = this else {
            return (r, Fidelity::Exact);
        };
        let virtual_start: TextPos = r.pos();
        let virtual_end = r.end().max(virtual_start);
        if virtual_start == virtual_end {
            let (position, fidelity) = Self::virtual_to_original_position(this, virtual_start);
            return (TextRange::new(position, position), fidelity);
        }

        let (start_idx, start_in) = m.segment_index_at(virtual_start);
        let end_probe = virtual_end - 1;
        let (end_idx, end_in) = m.segment_index_at(end_probe);

        if start_idx == end_idx && start_in == end_in {
            if start_in {
                let seg = &m.segments[start_idx as usize];
                if seg.kind == Kind::Verbatim {
                    let orig_start = clamp(
                        seg.original_start + (virtual_start - seg.virtual_start),
                        seg.original_start,
                        seg.original_end,
                    );
                    let orig_end = clamp(
                        seg.original_start + (virtual_end - seg.virtual_start),
                        orig_start,
                        seg.original_end,
                    );
                    return (TextRange::new(orig_start, orig_end), Fidelity::Exact);
                }
                return (
                    TextRange::new(seg.original_start, seg.original_end),
                    Fidelity::Atom,
                );
            }
            // Entirely within a single synthesized gap.
            let pos = m.insertion_point(start_idx);
            return (TextRange::new(pos, pos), Fidelity::None);
        }

        let orig_start = m.map_low(virtual_start, start_idx, start_in);
        let orig_end = m.map_high(virtual_end, end_idx, end_in).max(orig_start);
        (TextRange::new(orig_start, orig_end), Fidelity::Approximate)
    }

    /// VirtualToOriginalSpanForFeature maps r only when every virtual position in the non-empty range is
    /// covered by contiguous segments participating in feature. A zero-length range requires its containing
    /// segment to participate. Diagnostics and edit write-back intentionally use VirtualToOriginalSpan instead.
    pub fn virtual_to_original_span_for_feature(
        this: Option<&SpanMap>,
        r: TextRange,
        feature: Feature,
    ) -> (TextRange, Fidelity) {
        let (mapped, fidelity) = Self::virtual_to_original_span(this, r);
        if this.is_none_or(|m| m.virtual_span_supports_feature(r, feature)) {
            return (mapped, fidelity);
        }
        (mapped, Fidelity::None)
    }

    fn virtual_span_supports_feature(&self, r: TextRange, feature: Feature) -> bool {
        let start: TextPos = r.pos();
        let end = r.end().max(start);
        if start == end {
            let (index, inside) = self.segment_index_at(start);
            return inside && supports_feature(self.segments[index as usize], feature);
        }
        let (mut index, inside) = self.segment_index_at(start);
        if !inside {
            return false;
        }
        let mut covered_through = start;
        while index < self.segments.len() as i32 && covered_through < end {
            let segment = self.segments[index as usize];
            if segment.virtual_start > covered_through
                || segment.virtual_end <= covered_through
                || !supports_feature(segment, feature)
            {
                return false;
            }
            covered_through = segment.virtual_end;
            index += 1;
        }
        covered_through >= end
    }

    /// VirtualToOriginalPosition maps a single virtual position to the corresponding original position, along with the
    /// fidelity of the result. It is the single-position analog of VirtualToOriginalSpan: a position in a gap (or in an empty
    /// map) is synthesized and maps to the insertion point with FidelityNone. A nil SpanMap maps identically.
    pub fn virtual_to_original_position(
        this: Option<&SpanMap>,
        pos: TextPos,
    ) -> (TextPos, Fidelity) {
        let Some(m) = this else {
            return (pos, Fidelity::Exact);
        };
        let (idx, inside) = m.segment_index_at(pos);
        if !inside {
            return (m.insertion_point(idx), Fidelity::None);
        }
        let seg = &m.segments[idx as usize];
        if seg.kind == Kind::Verbatim {
            return (
                clamp(
                    seg.original_start + (pos - seg.virtual_start),
                    seg.original_start,
                    seg.original_end,
                ),
                Fidelity::Exact,
            );
        }
        (seg.original_start, Fidelity::Atom)
    }

    /// VirtualToOriginalPositionExact maps a position only when it is unambiguously in verbatim content.
    /// A boundary touching an atom is rejected because the same virtual position can describe either side.
    pub fn virtual_to_original_position_exact(
        this: Option<&SpanMap>,
        pos: TextPos,
    ) -> (TextPos, bool) {
        let (mapped, fidelity) = Self::virtual_to_original_position(this, pos);
        if fidelity != Fidelity::Exact || this.is_none() {
            return (mapped, fidelity == Fidelity::Exact);
        }
        let m = this.unwrap();
        let (index, inside) = m.segment_index_at(pos);
        if !inside || m.segments[index as usize].kind != Kind::Verbatim {
            return (mapped, false);
        }
        if index > 0 {
            let previous = m.segments[index as usize - 1];
            if previous.virtual_end == pos
                && (previous.kind != Kind::Verbatim
                    || previous.original_end != m.segments[index as usize].original_start)
            {
                return (mapped, false);
            }
        }
        (mapped, true)
    }

    /// VirtualToOriginalPositionForFeature maps pos only when its virtual segment participates in feature.
    /// Diagnostics and edit write-back intentionally use VirtualToOriginalPosition instead.
    pub fn virtual_to_original_position_for_feature(
        this: Option<&SpanMap>,
        pos: TextPos,
        feature: Feature,
    ) -> (TextPos, Fidelity) {
        let (mapped, fidelity) = Self::virtual_to_original_position(this, pos);
        let Some(m) = this else {
            return (mapped, fidelity);
        };
        let (index, inside) = m.segment_index_at(pos);
        if !inside || !supports_feature(m.segments[index as usize], feature) {
            return (mapped, Fidelity::None);
        }
        (mapped, fidelity)
    }

    /// AliasForVirtualSpan returns the alias segment exactly covering r. Partial overlap does not qualify:
    /// diagnostic text may be substituted only when the diagnostic identifies the complete virtual alias.
    ///
    /// PORT: `(Segment, bool)` → `Option<Segment>` (the `false` result's zero
    /// `Segment{}` carried no information).
    pub fn alias_for_virtual_span(this: Option<&SpanMap>, r: TextRange) -> Option<Segment> {
        let m = this?;
        let (index, inside) = m.segment_index_at(r.pos());
        if !inside {
            return None;
        }
        let segment = m.segments[index as usize];
        (segment.kind == Kind::Alias
            && r.pos() == segment.virtual_start
            && r.end() == segment.virtual_end)
            .then_some(segment)
    }

    /// segmentIndexAt returns the index of the segment containing pos and true, or, when pos lies in a gap,
    /// the index of the segment immediately before pos (-1 if none) and false.
    ///
    /// PORT: the `int` index may be -1 → `i32`; `slices.BinarySearchFunc` is
    /// `sort.Search(cmp >= 0)` + `cmp == 0` → `partition_point` + equality,
    /// which also preserves Go's first-match guarantee on duplicate
    /// `virtual_start`s (Rust's `binary_search_by` is unspecified there).
    fn segment_index_at(&self, pos: TextPos) -> (i32, bool) {
        let idx = self
            .segments
            .partition_point(|s| s.virtual_start.wrapping_sub(pos) < 0);
        let found = idx < self.segments.len() && self.segments[idx].virtual_start == pos;
        let idx = idx as i32;
        if found {
            return (idx, true);
        }
        let prev = idx - 1;
        if prev >= 0
            && (pos < self.segments[prev as usize].virtual_end
                || prev == self.segments.len() as i32 - 1
                    && pos == self.segments[prev as usize].virtual_end)
        {
            return (prev, true);
        }
        (prev, false)
    }

    /// insertionPoint returns the original offset where synthesized content following segment prev sits: the
    /// original end of that segment, or 0 before the first segment.
    fn insertion_point(&self, prev: i32) -> TextPos {
        if prev < 0 {
            return 0;
        }
        self.segments[prev as usize].original_end
    }

    /// mapLow maps a virtual lower range boundary to original coordinates. A boundary in a synthesized
    /// gap uses that gap's insertion point; an atom uses its original start.
    fn map_low(&self, pos: TextPos, idx: i32, inside: bool) -> TextPos {
        if !inside {
            return self.insertion_point(idx);
        }
        let seg = &self.segments[idx as usize];
        if seg.kind == Kind::Verbatim {
            return clamp(
                seg.original_start + (pos - seg.virtual_start),
                seg.original_start,
                seg.original_end,
            );
        }
        seg.original_start
    }

    /// mapHigh maps a virtual upper range boundary to original coordinates. A boundary in a synthesized
    /// gap uses that gap's insertion point; an atom uses its original end.
    fn map_high(&self, pos: TextPos, idx: i32, inside: bool) -> TextPos {
        if !inside {
            return self.insertion_point(idx);
        }
        let seg = &self.segments[idx as usize];
        if seg.kind == Kind::Verbatim {
            return clamp(
                seg.original_start + (pos - seg.virtual_start),
                seg.original_start,
                seg.original_end,
            );
        }
        seg.original_end
    }

    /// OriginalToVirtualPositions returns every virtual projection of an original position whose segment
    /// participates in feature. Segment ends are inclusive for point mapping, so a position shared by adjacent
    /// original spans returns projections from both sides. Results are ordered by virtual position. It returns
    /// no results for an uncovered position or when all touching segments reject feature. A nil SpanMap maps identically.
    pub fn original_to_virtual_positions(
        this: Option<&SpanMap>,
        pos: TextPos,
        feature: Feature,
    ) -> Vec<MappedPosition> {
        let Some(m) = this else {
            return vec![MappedPosition {
                position: pos,
                fidelity: Fidelity::Exact,
            }];
        };
        let groups = m.orig_index().segment_groups_at_original_position(pos);
        if groups.is_empty() {
            return Vec::new();
        }
        let mut results = Vec::new();
        for group in &groups {
            for segment in &group.segments {
                if !supports_feature(*segment, feature) {
                    continue;
                }
                let mut mapped = MappedPosition {
                    fidelity: Fidelity::Atom,
                    ..MappedPosition::default()
                };
                if segment.kind == Kind::Verbatim {
                    mapped.position = clamp(
                        segment.virtual_start + (pos - segment.original_start),
                        segment.virtual_start,
                        segment.virtual_end,
                    );
                    mapped.fidelity = Fidelity::Exact;
                } else if group.at_end {
                    mapped.position = segment.virtual_end;
                } else {
                    mapped.position = segment.virtual_start;
                }
                if !results.contains(&mapped) {
                    results.push(mapped);
                }
            }
        }
        results.sort_unstable_by(|a, b| a.position.wrapping_sub(b.position).cmp(&0));
        results
    }

    /// OriginalToVirtualSpans returns every feature-compatible virtual projection of an original range.
    /// A range contained by one or more segments produces one exact or atom result per matching segment.
    ///
    /// A range that starts in one group and ends in another can have several possible virtual ranges. For
    /// example, suppose two original segments are each copied twice into the virtual text:
    ///
    ///	original:   [ A ][ B ]
    ///	               [---)       range from inside A to inside B
    ///
    ///	virtual:    [ A ][ B ]      [ A ][ B ]
    ///	               ^   ^          ^   ^
    ///	             start end      start end
    ///	               1   3          11  13
    ///
    /// The map says that the range may start at 1 or 11 and end at 3 or 13, but it does not say which copy of A
    /// belongs with which copy of B. We choose the smallest range around each possible location, producing [1,3)
    /// and [11,13). We do not return [1,13), because it contains both smaller candidates and would include code
    /// that may be unrelated to the original range. These cross-group results have approximate fidelity.
    /// If either boundary is uncovered or disabled for feature, there are no results. A nil SpanMap maps identically.
    ///
    /// PORT: `slices.Sort`/`slices.BinarySearch` (unstable ordering, first-
    /// index semantics) → `sort_unstable`/`partition_point`.
    pub fn original_to_virtual_spans(
        this: Option<&SpanMap>,
        r: TextRange,
        feature: Feature,
    ) -> Vec<MappedSpan> {
        let Some(m) = this else {
            return vec![MappedSpan {
                span: r,
                fidelity: Fidelity::Exact,
            }];
        };
        let start: TextPos = r.pos();
        let end = r.end().max(start);
        if start == end {
            // `core.Map` → iterator collect.
            return Self::original_to_virtual_positions(Some(m), start, feature)
                .into_iter()
                .map(|position| MappedSpan {
                    span: TextRange::new(position.position, position.position),
                    fidelity: position.fidelity,
                })
                .collect();
        }
        let last_character = end - 1;
        let original_index = m.orig_index();
        let (start_segments, start_inside) = original_index.segments_at_original_position(start);
        let (end_segments, end_inside) =
            original_index.segments_at_original_position(last_character);
        if !start_inside || !end_inside {
            return Vec::new();
        }
        let mut containing = Vec::new();
        for segment in &start_segments {
            if end <= segment.original_end {
                containing.push(*segment);
            }
        }
        if !containing.is_empty() {
            let mut results =
                original_to_virtual_spans_in_segments(&containing, start, end, feature);
            if !results.is_empty() {
                // PORT: Go compares `a.Span.Pos() - b.Span.Pos()` in `int`
                // (64-bit, non-wrapping) — equivalent to a key sort.
                results.sort_unstable_by_key(|a| a.span.pos());
                return results;
            }
        }
        let mut starts = original_start_projections(&start_segments, start, feature);
        let mut ends = original_end_projections(&end_segments, end, feature);
        if starts.is_empty() || ends.is_empty() {
            return Vec::new();
        }
        starts.sort_unstable();
        ends.sort_unstable();
        let mut results = Vec::with_capacity(starts.len().min(ends.len()));
        for (i, virtual_start) in starts.iter().enumerate() {
            // PORT: `slices.BinarySearch` = `sort.Search(ends[i] >= x)` →
            // `partition_point`; Go's `found` bool is discarded (`_`).
            let end_index = ends.partition_point(|e| e < virtual_start);
            if end_index == ends.len() || i + 1 < starts.len() && starts[i + 1] <= ends[end_index] {
                continue;
            }
            results.push(MappedSpan {
                span: TextRange::new(*virtual_start, ends[end_index]),
                fidelity: Fidelity::Approximate,
            });
        }
        results
    }

    /// OriginalToVirtualIntersectingSpans maps every feature-enabled segment intersection with r.
    /// Unlike OriginalToVirtualSpans, uncovered range endpoints do not suppress covered interior segments.
    pub fn original_to_virtual_intersecting_spans(
        this: Option<&SpanMap>,
        r: TextRange,
        feature: Feature,
    ) -> Vec<MappedSpan> {
        let Some(m) = this else {
            return vec![MappedSpan {
                span: r,
                fidelity: Fidelity::Exact,
            }];
        };
        if r.pos() == r.end() {
            return Self::original_to_virtual_spans(Some(m), r, feature);
        }
        let mut results = Vec::new();
        for segment in &m.segments {
            if !supports_feature(*segment, feature) {
                continue;
            }
            let start = r.pos().max(segment.original_start);
            let end = r.end().min(segment.original_end);
            if start >= end {
                continue;
            }
            if segment.kind == Kind::Verbatim {
                results.push(MappedSpan {
                    span: TextRange::new(
                        segment.virtual_start + (start - segment.original_start),
                        segment.virtual_start + (end - segment.original_start),
                    ),
                    fidelity: Fidelity::Exact,
                });
            } else {
                results.push(MappedSpan {
                    span: TextRange::new(segment.virtual_start, segment.virtual_end),
                    fidelity: Fidelity::Atom,
                });
            }
        }
        results
    }
}

/// originalStartProjections maps the inclusive start of an original range through every matching segment.
/// Verbatim segments preserve the offset within the segment; atoms map to their virtual start.
///
/// For duplicate verbatim segments, the start keeps the same relative offset in every copy:
///
///	original:       [---------)
///	                   ^ start
///
///	virtual:    [---------)   [---------)
///	               ^             ^
///	             result        result
fn original_start_projections(
    segments: &[Segment],
    start: TextPos,
    feature: Feature,
) -> Vec<TextPos> {
    let mut results = Vec::with_capacity(segments.len());
    for segment in segments {
        if !supports_feature(*segment, feature) {
            continue;
        }
        if segment.kind == Kind::Verbatim {
            results.push(clamp(
                segment.virtual_start + (start - segment.original_start),
                segment.virtual_start,
                segment.virtual_end,
            ));
        } else {
            results.push(segment.virtual_start);
        }
    }
    results
}

/// originalEndProjections maps the exclusive end of an original range through every matching segment.
/// The caller uses end-1 to find the segment containing the final character, while this helper maps the end
/// boundary itself. Verbatim segments preserve that boundary; atoms map to their virtual end.
///
/// The lookup uses end-1 so an end at a segment boundary selects the segment on its left, not the next one:
///
///	original:       [---------)[ next segment )
///	                         ^`-- end
///	                         `--- end-1
///
///	virtual:    [---------)   [---------)
///	                      ^             ^
///	                    result        result
fn original_end_projections(segments: &[Segment], end: TextPos, feature: Feature) -> Vec<TextPos> {
    let mut results = Vec::with_capacity(segments.len());
    for segment in segments {
        if !supports_feature(*segment, feature) {
            continue;
        }
        if segment.kind == Kind::Verbatim {
            results.push(clamp(
                segment.virtual_start + (end - segment.original_start),
                segment.virtual_start,
                segment.virtual_end,
            ));
        } else {
            results.push(segment.virtual_end);
        }
    }
    results
}

/// originalToVirtualSpansInSegments maps a range fully contained by each segment.
fn original_to_virtual_spans_in_segments(
    segments: &[Segment],
    start: TextPos,
    end: TextPos,
    feature: Feature,
) -> Vec<MappedSpan> {
    let mut results = Vec::with_capacity(segments.len());
    for segment in segments {
        if !supports_feature(*segment, feature) {
            continue;
        }
        if segment.kind == Kind::Verbatim {
            let virtual_start = clamp(
                segment.virtual_start + (start - segment.original_start),
                segment.virtual_start,
                segment.virtual_end,
            );
            let virtual_end = clamp(
                segment.virtual_start + (end - segment.original_start),
                virtual_start,
                segment.virtual_end,
            );
            results.push(MappedSpan {
                span: TextRange::new(virtual_start, virtual_end),
                fidelity: Fidelity::Exact,
            });
        } else {
            results.push(MappedSpan {
                span: TextRange::new(segment.virtual_start, segment.virtual_end),
                fidelity: Fidelity::Atom,
            });
        }
    }
    results
}

/// sameOriginalRange reports whether two segments belong to the same duplicate group.
fn same_original_range(left: Segment, right: Segment) -> bool {
    left.original_start == right.original_start && left.original_end == right.original_end
}

/// originalIndex stores segments in original-text order and a complete binary tree whose leaves correspond
/// to those segments. Each internal node stores the maximum OriginalEnd below it, allowing point lookups to
/// discard a whole subtree when none of its segments can reach the queried position.
struct OriginalIndex {
    segments: Vec<Segment>,
    leaf_count: usize,
    max_ends: Vec<TextPos>,
}

impl SpanMap {
    /// origIndex builds the immutable original-text interval index on first use. Sorting dominates the O(n) tree
    /// construction, so the first lookup remains O(n log n); later point lookups visit only tree branches that can
    /// contain a match.
    ///
    /// PORT: `origOnce.Do` → `OnceLock::get_or_init` (same once-only lazy
    /// semantics; `sync.Once`'s poisoning behavior has no analog needed here).
    fn orig_index(&self) -> &OriginalIndex {
        self.original_index.get_or_init(|| {
            let mut segments = self.segments.clone();
            segments.sort_unstable_by(|a, b| {
                let c = a.original_start.wrapping_sub(b.original_start);
                if c != 0 {
                    return c.cmp(&0);
                }
                let c = a.original_end.wrapping_sub(b.original_end);
                if c != 0 {
                    return c.cmp(&0);
                }
                a.virtual_start.wrapping_sub(b.virtual_start).cmp(&0)
            });
            let mut leaf_count = 1usize;
            while leaf_count < segments.len() {
                leaf_count *= 2;
            }
            let mut max_ends: Vec<TextPos> = vec![0; 2 * leaf_count];
            for (i, segment) in segments.iter().enumerate() {
                max_ends[leaf_count + i] = segment.original_end;
            }
            let mut i = leaf_count - 1;
            while i > 0 {
                max_ends[i] = max_ends[2 * i].max(max_ends[2 * i + 1]);
                i -= 1;
            }
            OriginalIndex {
                segments,
                leaf_count,
                max_ends,
            }
        })
    }
}

impl OriginalIndex {
    /// segmentsAtOriginalPosition returns every mapping segment containing the original-text position pos.
    /// Segment ends are exclusive; a segment start, including a zero-length segment, is considered contained.
    ///
    /// PORT: `sort.Search` → `partition_point` on the complementary predicate.
    fn segments_at_original_position(&self, pos: TextPos) -> (Vec<Segment>, bool) {
        // Query intervals that contain pos strictly before their exclusive end. Segments starting exactly at pos
        // are appended separately so zero-length segments are included without preventing maxEnd <= pos pruning.
        let start = self.segments.partition_point(|s| s.original_start < pos);
        let mut results = self.segments_ending_after_position(start, pos);
        let end = self.segments.partition_point(|s| s.original_start <= pos);
        results.extend_from_slice(&self.segments[start..end]);
        let found = !results.is_empty();
        (results, found)
    }

    /// segmentsEndingAfterPosition returns segments among [0, limit) whose OriginalEnd is greater than pos.
    fn segments_ending_after_position(&self, limit: usize, pos: TextPos) -> Vec<Segment> {
        let mut results = Vec::new();
        self.collect_segments_ending_at_or_after(
            1,
            0,
            self.leaf_count,
            limit,
            pos,
            false,
            &mut results,
        );
        results
    }

    /// collectSegmentsEndingAtOrAfter walks the flat max-end tree left-to-right, preserving original-text order.
    /// Nodes beyond limit or whose maximum end cannot reach pos are discarded without visiting their leaves.
    #[allow(clippy::too_many_arguments)] // PORT: signature mirrors the Go original.
    fn collect_segments_ending_at_or_after(
        &self,
        node: usize,
        start: usize,
        end: usize,
        limit: usize,
        pos: TextPos,
        include_end: bool,
        results: &mut Vec<Segment>,
    ) {
        if start >= limit || self.max_ends[node] < pos || !include_end && self.max_ends[node] == pos
        {
            return;
        }
        if end - start == 1 {
            results.push(self.segments[start]);
            return;
        }
        let middle = start + (end - start) / 2;
        self.collect_segments_ending_at_or_after(
            2 * node,
            start,
            middle,
            limit,
            pos,
            include_end,
            results,
        );
        self.collect_segments_ending_at_or_after(
            2 * node + 1,
            middle,
            end,
            limit,
            pos,
            include_end,
            results,
        );
    }
}

struct SegmentGroupAtOriginalPosition {
    segments: Vec<Segment>,
    at_end: bool,
}

impl OriginalIndex {
    /// segmentGroupsAtOriginalPosition returns every group of equal-range mapping segments containing or touching
    /// the original-text position pos. Segment ends are included for point mapping.
    ///
    /// At a shared boundary, segments ending at pos and segments starting there form separate groups:
    ///
    ///	original:  [--- A ---)[--- B ---)
    ///	                      ^ pos
    ///
    ///	virtual:   [ A1 ) [ A2 )    [ B1 ) [ B2 )
    ///	             left group       right group
    ///	             atEnd: true      atEnd: false
    fn segment_groups_at_original_position(
        &self,
        pos: TextPos,
    ) -> Vec<SegmentGroupAtOriginalPosition> {
        let limit = self.segments.partition_point(|s| s.original_start <= pos);
        let mut segments = Vec::new();
        self.collect_segments_ending_at_or_after(
            1,
            0,
            self.leaf_count,
            limit,
            pos,
            true,
            &mut segments,
        );
        let mut groups = Vec::new();
        let mut start = 0;
        while start < segments.len() {
            let mut end = start + 1;
            while end < segments.len() && same_original_range(segments[start], segments[end]) {
                end += 1;
            }
            let segment = segments[start];
            if pos <= segment.original_end {
                groups.push(SegmentGroupAtOriginalPosition {
                    segments: segments[start..end].to_vec(),
                    at_end: pos == segment.original_end && pos != segment.original_start,
                });
            }
            start = end;
        }
        groups
    }
}

/// supportsFeature reports whether segment participates in feature.
fn supports_feature(segment: Segment, feature: Feature) -> bool {
    segment.features & feature != 0
}

/// clamp confines v to the inclusive interval [lo, hi].
fn clamp(v: TextPos, lo: TextPos, hi: TextPos) -> TextPos {
    lo.max(v.min(hi))
}

/// UnmarshalError is the failure mode of `unmarshal`.
///
/// PORT: Go's `(*SpanMap, error)` — either a jsontext decode error or
/// `fmt.Errorf("span map segment %d: expected 5 or 6 values, got %d")` —
/// becomes a single error enum; messages keep the Go text.
#[derive(Debug)]
pub enum UnmarshalError {
    Json(serde_json::Error),
    SegmentLength { index: usize, count: usize },
}

impl fmt::Display for UnmarshalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnmarshalError::Json(e) => write!(f, "{e}"),
            UnmarshalError::SegmentLength { index, count } => {
                write!(
                    f,
                    "span map segment {index}: expected 5 or 6 values, got {count}"
                )
            }
        }
    }
}

impl std::error::Error for UnmarshalError {}

impl From<serde_json::Error> for UnmarshalError {
    fn from(e: serde_json::Error) -> UnmarshalError {
        UnmarshalError::Json(e)
    }
}

/// Unmarshal decodes a SpanMap from the JSON tuple form produced by an out-of-process content mapper.
/// Five-element tuples omit features and are normalized to FeatureAll; six-element tuples preserve the
/// explicit feature mask, including FeatureNone.
///
/// PORT: `Option<Vec<_>>` mirrors Go's `json.Unmarshal`, which accepts a
/// top-level `null` as a nil slice (serde would otherwise error).
pub fn unmarshal(data: &[u8]) -> Result<SpanMap, UnmarshalError> {
    let tuples: Option<Vec<Vec<i32>>> = json::unmarshal(data, &[])?;
    let tuples = tuples.unwrap_or_default();
    let mut segments = Vec::with_capacity(tuples.len());
    for (i, t) in tuples.iter().enumerate() {
        if t.len() != 5 && t.len() != 6 {
            return Err(UnmarshalError::SegmentLength {
                index: i,
                count: t.len(),
            });
        }
        // PORT: `t[0] + t[1]`/`t[2] + t[3]` wrap in Go; keep the wrap so
        // malformed tuples produce a bad segment for `validate` to reject
        // rather than a panic (SPEC §7.6 wraparound site).
        let mut segment = Segment {
            virtual_start: t[0],
            virtual_end: t[0].wrapping_add(t[1]),
            original_start: t[2],
            original_end: t[2].wrapping_add(t[3]),
            kind: Kind(t[4]),
            features: Feature::All,
        };
        if t.len() == 6 {
            segment.features = Feature(t[5]);
        }
        segments.push(segment);
    }
    Ok(SpanMap::new(&segments))
}

impl SpanMap {
    /// Marshal encodes a SpanMap into the JSON tuple form. FeatureAll uses the backward-compatible five-element
    /// tuple; every other feature mask is emitted as a sixth element.
    ///
    /// PORT: `&self` — Go has no nil guard here, so a nil `*SpanMap` would
    /// panic on field access; `&self` rules it out statically.
    pub fn marshal(&self) -> Result<Vec<u8>, serde_json::Error> {
        let mut tuples: Vec<Vec<i32>> = Vec::with_capacity(self.segments.len());
        for s in &self.segments {
            // PORT: `VirtualEnd - VirtualStart`/`OriginalEnd - OriginalStart`
            // wrap in Go even for invalid segments → wrapping_sub.
            let mut tuple = vec![
                s.virtual_start,
                s.virtual_end.wrapping_sub(s.virtual_start),
                s.original_start,
                s.original_end.wrapping_sub(s.original_start),
                s.kind.0,
            ];
            if s.features != Feature::All {
                tuple.push(s.features.0);
            }
            tuples.push(tuple);
        }
        json::marshal(&tuples, &[])
    }
}
