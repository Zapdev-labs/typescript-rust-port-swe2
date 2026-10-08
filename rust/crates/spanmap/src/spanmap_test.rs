// Ported from tsc/internal/spanmap/spanmap_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::text::{TextPos, TextRange};

use crate::spanmap::*;

// PORT: tsc_core's TextRange does not implement Debug yet, so range equality
// is asserted through (pos, end) tuples.
fn assert_text_range_eq(got: TextRange, want: TextRange) {
    assert_eq!((got.pos(), got.end()), (want.pos(), want.end()));
}

#[test]
fn test_virtual_to_original_span_verbatim() {
    // Virtual [0,10) is a verbatim copy of original [100,110).
    let m = SpanMap::new(&[Segment {
        virtual_start: 0,
        virtual_end: 10,
        original_start: 100,
        original_end: 110,
        kind: Kind::Verbatim,
        features: Feature::All,
    }]);

    let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(3, 7));
    assert_eq!(got.pos(), 103);
    assert_eq!(got.end(), 107);
    assert_eq!(fidelity, Fidelity::Exact);
}

#[test]
fn test_virtual_to_original_span_atom() {
    // Virtual [0,3) is a synthesized gap; [3,14) ("MyComponent") is an atom of the original [60,71).
    let m = SpanMap::new(&[Segment {
        virtual_start: 3,
        virtual_end: 14,
        original_start: 60,
        original_end: 71,
        kind: Kind::Atom,
        features: Feature::All,
    }]);

    // A span inside the atom maps to the whole atom span.
    let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(5, 9));
    assert_eq!(got.pos(), 60);
    assert_eq!(got.end(), 71);
    assert_eq!(fidelity, Fidelity::Atom);
}

#[test]
fn test_virtual_alias() {
    let m = SpanMap::new(&[Segment {
        virtual_start: 3,
        virtual_end: 6,
        original_start: 10,
        original_end: 11,
        kind: Kind::Alias,
        features: Feature::All,
    }]);

    let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(3, 6));
    assert_text_range_eq(got, TextRange::new(10, 11));
    assert_eq!(fidelity, Fidelity::Atom);
    let alias = SpanMap::alias_for_virtual_span(Some(&m), TextRange::new(3, 6));
    assert!(alias.is_some());
    assert_eq!(alias.unwrap().kind, Kind::Alias);
    let partial = SpanMap::alias_for_virtual_span(Some(&m), TextRange::new(4, 6));
    assert!(partial.is_none());

    let data = m.marshal().unwrap();
    let decoded = unmarshal(&data).unwrap();
    assert_eq!(SpanMap::segments(Some(&decoded))[0].kind, Kind::Alias);
}

#[test]
fn test_virtual_to_original_span_synthesized_gap() {
    // A gap between two verbatim segments is synthesized: it maps to the insertion point (the preceding
    // segment's original end) with no fidelity.
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 30,
            original_start: 200,
            original_end: 210,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
    ]);

    let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(12, 15));
    assert_eq!(got.pos(), 110);
    assert_eq!(got.end(), 110);
    assert_eq!(fidelity, Fidelity::None);
}

#[test]
fn test_original_to_virtual_intersecting_spans_allows_uncovered_endpoints() {
    let m = SpanMap::new(&[Segment {
        virtual_start: 10,
        virtual_end: 20,
        original_start: 100,
        original_end: 110,
        kind: Kind::Verbatim,
        features: Feature::SemanticTokens | Feature::InlayHints,
    }]);

    for feature in [Feature::SemanticTokens, Feature::InlayHints] {
        let got = SpanMap::original_to_virtual_intersecting_spans(
            Some(&m),
            TextRange::new(90, 120),
            feature,
        );
        assert_eq!(got.len(), 1);
        assert_text_range_eq(got[0].span, TextRange::new(10, 20));
        assert_eq!(got[0].fidelity, Fidelity::Exact);
    }
}

#[test]
fn test_virtual_to_original_span_empty_is_synthesized() {
    // An empty map describes fully synthesized output: everything maps to the start with no fidelity.
    let m = SpanMap::new(&[]);
    let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(5, 10));
    assert_eq!(got.pos(), 0);
    assert_eq!(got.end(), 0);
    assert_eq!(fidelity, Fidelity::None);
}

#[test]
fn test_virtual_to_original_span_crossing_segments() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            ..Segment::default()
        },
        Segment {
            virtual_start: 10,
            virtual_end: 20,
            original_start: 200,
            original_end: 210,
            kind: Kind::Verbatim,
            ..Segment::default()
        },
    ]);

    let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(5, 15));
    assert_eq!(got.pos(), 105);
    assert_eq!(got.end(), 205);
    assert_eq!(fidelity, Fidelity::Approximate);
}

#[test]
fn test_virtual_to_original_span_nil_identity() {
    let m: Option<&SpanMap> = None;
    let (got, fidelity) = SpanMap::virtual_to_original_span(m, TextRange::new(3, 7));
    assert_eq!(got.pos(), 3);
    assert_eq!(got.end(), 7);
    assert_eq!(fidelity, Fidelity::Exact);
}

#[test]
fn test_virtual_to_original_position() {
    // Virtual [0,10) is a verbatim copy of original [100,110); [10,20) is an atom of original [200,210).
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 30,
            original_start: 200,
            original_end: 210,
            kind: Kind::Atom,
            features: Feature::All,
        },
    ]);

    let test_cases = [
        ("verbatim interpolates", 3, 103, Fidelity::Exact),
        ("atom maps to its start", 25, 200, Fidelity::Atom),
        ("gap maps to insertion point", 15, 110, Fidelity::None),
    ];
    for (name, pos, want, want_fidelity) in test_cases {
        // t.Run(tc.name, ...) — subtest name carried into assertion messages.
        let (got, fidelity) = SpanMap::virtual_to_original_position(Some(&m), pos);
        assert_eq!(got, want, "{name}");
        assert_eq!(fidelity, want_fidelity, "{name}");
        // VirtualToOriginalPosition must agree with VirtualToOriginalSpan on a zero-length range.
        let (span, span_fidelity) =
            SpanMap::virtual_to_original_span(Some(&m), TextRange::new(pos, pos));
        assert_eq!(got, span.pos(), "{name}");
        assert_eq!(fidelity, span_fidelity, "{name}");
    }
}

#[test]
fn test_virtual_to_original_position_exact() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
        Segment {
            virtual_start: 10,
            virtual_end: 20,
            original_start: 110,
            original_end: 120,
            kind: Kind::Atom,
            features: Feature::All,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 30,
            original_start: 120,
            original_end: 130,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
    ]);

    for test in [
        (5, 105, true),
        (10, 110, false),
        (15, 110, false),
        (20, 120, false),
        (25, 125, true),
    ] {
        let (pos, want, want_ok) = test;
        let (got, ok) = SpanMap::virtual_to_original_position_exact(Some(&m), pos);
        assert_eq!(got, want);
        assert_eq!(ok, want_ok);
    }
}

#[test]
fn test_virtual_to_original_position_exact_rejects_discontinuous_boundary() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 0,
            original_end: 10,
            kind: Kind::Verbatim,
            ..Segment::default()
        },
        Segment {
            virtual_start: 10,
            virtual_end: 20,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            ..Segment::default()
        },
    ]);

    let (mapped, ok) = SpanMap::virtual_to_original_position_exact(Some(&m), 10);
    assert_eq!(mapped, 100);
    assert!(!ok);
}

#[test]
fn test_zero_length_spans_at_segment_ends() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 30,
            original_start: 200,
            original_end: 210,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
    ]);

    let (position, fidelity) = SpanMap::virtual_to_original_position(Some(&m), 30);
    assert_eq!(position, 210);
    assert_eq!(fidelity, Fidelity::Exact);
    let (virtual_span, fidelity) =
        SpanMap::virtual_to_original_span(Some(&m), TextRange::new(30, 30));
    assert_text_range_eq(virtual_span, TextRange::new(210, 210));
    assert_eq!(fidelity, Fidelity::Exact);

    for test in [("before gap", 110), ("final", 210)] {
        let (_name, original_end) = test;
        // t.Run(test.name, ...)
        let positions =
            SpanMap::original_to_virtual_positions(Some(&m), original_end, Feature::Hover);
        let spans = SpanMap::original_to_virtual_spans(
            Some(&m),
            TextRange::new(original_end, original_end),
            Feature::Hover,
        );
        assert_eq!(positions.len(), 1);
        assert_eq!(spans.len(), 1);
        assert_text_range_eq(
            spans[0].span,
            TextRange::new(positions[0].position, positions[0].position),
        );
        assert_eq!(spans[0].fidelity, positions[0].fidelity);
    }
}

#[test]
fn test_map_position_nil_identity() {
    let m: Option<&SpanMap> = None;
    let (got, fidelity) = SpanMap::virtual_to_original_position(m, 7);
    assert_eq!(got, 7);
    assert_eq!(fidelity, Fidelity::Exact);
}

#[test]
fn test_original_to_virtual_span_verbatim() {
    // Virtual [0,10) is a verbatim copy of original [100,110).
    let m = SpanMap::new(&[Segment {
        virtual_start: 0,
        virtual_end: 10,
        original_start: 100,
        original_end: 110,
        kind: Kind::Verbatim,
        features: Feature::All,
    }]);

    let results =
        SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(103, 107), Feature::All);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].span.pos(), 3);
    assert_eq!(results[0].span.end(), 7);
    assert_eq!(results[0].fidelity, Fidelity::Exact);
}

#[test]
fn test_original_to_virtual_span_atom() {
    // Virtual [3,14) is an atom of the original [60,71).
    let m = SpanMap::new(&[Segment {
        virtual_start: 3,
        virtual_end: 14,
        original_start: 60,
        original_end: 71,
        kind: Kind::Atom,
        features: Feature::All,
    }]);

    // A span inside the original atom maps to the whole virtual span.
    let results =
        SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(63, 67), Feature::All);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].span.pos(), 3);
    assert_eq!(results[0].span.end(), 14);
    assert_eq!(results[0].fidelity, Fidelity::Atom);
}

#[test]
fn test_original_to_virtual_span_gap() {
    // An original range with no covering segment has no virtual counterpart.
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 30,
            original_start: 200,
            original_end: 210,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
    ]);

    assert_eq!(
        SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(150, 160), Feature::All).len(),
        0
    );
}

#[test]
fn test_original_to_virtual_span_nil_identity() {
    let m: Option<&SpanMap> = None;
    let results = SpanMap::original_to_virtual_spans(m, TextRange::new(3, 7), Feature::All);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].span.pos(), 3);
    assert_eq!(results[0].span.end(), 7);
    assert_eq!(results[0].fidelity, Fidelity::Exact);
}

#[test]
fn test_original_to_virtual_positions() {
    // Original [100,110) is a verbatim copy of virtual [0,10); [200,210) is an atom of virtual [20,30).
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 30,
            original_start: 200,
            original_end: 210,
            kind: Kind::Atom,
            features: Feature::All,
        },
    ]);

    let test_cases = [
        ("verbatim interpolates", 103, 3, Fidelity::Exact),
        ("atom maps to its start", 205, 20, Fidelity::Atom),
        ("gap has no projection", 150, 0, Fidelity::None),
    ];
    for (name, pos, want, want_fidelity) in test_cases {
        // t.Run(tc.name, ...) — Go's `return` exits the subtest → `continue`.
        let positions = SpanMap::original_to_virtual_positions(Some(&m), pos, Feature::All);
        let spans =
            SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(pos, pos), Feature::All);
        if want_fidelity.is_none() {
            assert_eq!(positions.len(), 0, "{name}");
            assert_eq!(spans.len(), 0, "{name}");
            continue;
        }
        assert_eq!(positions.len(), 1, "{name}");
        assert_eq!(positions[0].position, want, "{name}");
        assert_eq!(positions[0].fidelity, want_fidelity, "{name}");
        assert_eq!(spans.len(), 1, "{name}");
        assert_eq!(spans[0].span.pos(), want, "{name}");
        assert_eq!(spans[0].fidelity, want_fidelity, "{name}");
    }
}

#[test]
fn test_original_to_virtual_positions_at_endpoint() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 2,
            virtual_end: 5,
            original_start: 10,
            original_end: 13,
            kind: Kind::Verbatim,
            features: Feature::Completion,
        },
        Segment {
            virtual_start: 8,
            virtual_end: 11,
            original_start: 13,
            original_end: 16,
            kind: Kind::Verbatim,
            features: Feature::Completion,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 23,
            original_start: 30,
            original_end: 35,
            kind: Kind::Atom,
            features: Feature::Completion,
        },
    ]);

    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 13, Feature::Completion),
        [
            MappedPosition {
                position: 5,
                fidelity: Fidelity::Exact
            },
            MappedPosition {
                position: 8,
                fidelity: Fidelity::Exact
            },
        ]
    );
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 35, Feature::Completion),
        [MappedPosition {
            position: 23,
            fidelity: Fidelity::Atom
        }]
    );

    let filtered = SpanMap::new(&[
        Segment {
            virtual_start: 20,
            virtual_end: 23,
            original_start: 10,
            original_end: 13,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 2,
            virtual_end: 5,
            original_start: 13,
            original_end: 16,
            kind: Kind::Verbatim,
            features: Feature::Completion,
        },
    ]);
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&filtered), 13, Feature::All),
        [
            MappedPosition {
                position: 2,
                fidelity: Fidelity::Exact
            },
            MappedPosition {
                position: 23,
                fidelity: Fidelity::Exact
            },
        ]
    );
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&filtered), 13, Feature::Completion),
        [MappedPosition {
            position: 2,
            fidelity: Fidelity::Exact
        }]
    );
}

#[test]
fn test_original_to_virtual_duplicate_group() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 3,
            original_start: 10,
            original_end: 13,
            kind: Kind::Verbatim,
            features: Feature::Definition,
        },
        Segment {
            virtual_start: 10,
            virtual_end: 13,
            original_start: 10,
            original_end: 13,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 25,
            original_start: 10,
            original_end: 13,
            kind: Kind::Atom,
            features: Feature::Definition,
        },
    ]);

    let semantic = SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::Hover);
    assert_eq!(semantic.len(), 1);
    assert_eq!(semantic[0].position, 11);
    assert_eq!(semantic[0].fidelity, Fidelity::Exact);

    let navigation = SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::Definition);
    assert_eq!(navigation.len(), 2);
    assert_eq!(navigation[0].position, 1);
    assert_eq!(navigation[0].fidelity, Fidelity::Exact);
    assert_eq!(navigation[1].position, 20);
    assert_eq!(navigation[1].fidelity, Fidelity::Atom);

    let spans =
        SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(10, 13), Feature::Definition);
    assert_eq!(spans.len(), 2);
    assert_eq!(spans[0].span.pos(), 0);
    assert_eq!(spans[0].span.end(), 3);
    assert_eq!(spans[1].span.pos(), 20);
    assert_eq!(spans[1].span.end(), 25);
}

#[test]
fn test_original_to_virtual_overlapping_spans() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 6,
            original_start: 0,
            original_end: 6,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 10,
            virtual_end: 12,
            original_start: 2,
            original_end: 4,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 20,
            virtual_end: 24,
            original_start: 3,
            original_end: 7,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
    ]);

    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 3, Feature::Hover),
        [
            MappedPosition {
                position: 3,
                fidelity: Fidelity::Exact
            },
            MappedPosition {
                position: 11,
                fidelity: Fidelity::Exact
            },
            MappedPosition {
                position: 20,
                fidelity: Fidelity::Exact
            },
        ]
    );
    let spans = SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(3, 4), Feature::Hover);
    let want_spans = [
        MappedSpan {
            span: TextRange::new(3, 4),
            fidelity: Fidelity::Exact,
        },
        MappedSpan {
            span: TextRange::new(11, 12),
            fidelity: Fidelity::Exact,
        },
        MappedSpan {
            span: TextRange::new(20, 21),
            fidelity: Fidelity::Exact,
        },
    ];
    assert_eq!(spans.len(), want_spans.len());
    for i in 0..spans.len() {
        assert_eq!(spans[i], want_spans[i]);
    }
}

#[test]
fn test_original_to_virtual_position_finds_early_covering_segment() {
    // Binary search lands near [90,95), which does not contain 97. The interval index must still find the
    // earlier [0,100) segment without scanning every segment whose start precedes the query.
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 100,
            original_start: 0,
            original_end: 100,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 100,
            virtual_end: 105,
            original_start: 80,
            original_end: 85,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 105,
            virtual_end: 110,
            original_start: 90,
            original_end: 95,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 110,
            virtual_end: 113,
            original_start: 100,
            original_end: 103,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
    ]);

    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 97, Feature::Hover),
        [MappedPosition {
            position: 97,
            fidelity: Fidelity::Exact
        }]
    );
    let mut spans =
        SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(97, 98), Feature::Hover);
    assert_eq!(spans.len(), 1);
    assert_eq!(
        spans[0],
        MappedSpan {
            span: TextRange::new(97, 98),
            fidelity: Fidelity::Exact
        }
    );

    // Point lookup includes both sides of a shared endpoint, including an early interval found through the
    // max-end tree. Nonempty span lookup treats segment ends as exclusive and uses only the right segment.
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 100, Feature::Hover),
        [
            MappedPosition {
                position: 100,
                fidelity: Fidelity::Exact
            },
            MappedPosition {
                position: 110,
                fidelity: Fidelity::Exact
            },
        ]
    );
    spans = SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(100, 101), Feature::Hover);
    assert_eq!(spans.len(), 1);
    assert_eq!(
        spans[0],
        MappedSpan {
            span: TextRange::new(110, 111),
            fidelity: Fidelity::Exact
        }
    );
}

// PORT: Go's `testing.B` benchmark becomes a smoke test — stable Rust has no
// `#[bench]`; it still builds the lazy index once and re-queries it.
#[test]
fn benchmark_original_to_virtual_position_near_end() {
    const SEGMENT_COUNT: usize = 10_000;
    let mut segments = Vec::with_capacity(SEGMENT_COUNT);
    for i in 0..SEGMENT_COUNT {
        let start: TextPos = 2 * i as TextPos;
        segments.push(Segment {
            virtual_start: start,
            virtual_end: start + 1,
            original_start: start,
            original_end: start + 1,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        });
    }
    let m = SpanMap::new(&segments);
    let position: TextPos = 2 * (SEGMENT_COUNT - 1) as TextPos;
    SpanMap::original_to_virtual_positions(Some(&m), position, Feature::Hover); // Build the lazy index outside the benchmark.
    for _ in 0..1_000 {
        SpanMap::original_to_virtual_positions(Some(&m), position, Feature::Hover);
    }
}

#[test]
fn test_original_to_virtual_overlap_falls_back_from_disabled_container() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 6,
            original_start: 0,
            original_end: 6,
            kind: Kind::Verbatim,
            features: Feature::Definition,
        },
        Segment {
            virtual_start: 10,
            virtual_end: 13,
            original_start: 0,
            original_end: 3,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 13,
            virtual_end: 16,
            original_start: 3,
            original_end: 6,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
    ]);

    let spans = SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(1, 5), Feature::Hover);
    assert_eq!(spans.len(), 1);
    assert_eq!(
        spans[0],
        MappedSpan {
            span: TextRange::new(11, 15),
            fidelity: Fidelity::Approximate
        }
    );
}

#[test]
fn test_original_to_virtual_cross_group_projections() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 2,
            original_start: 0,
            original_end: 2,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 2,
            virtual_end: 4,
            original_start: 2,
            original_end: 4,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 10,
            virtual_end: 12,
            original_start: 0,
            original_end: 2,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 12,
            virtual_end: 14,
            original_start: 2,
            original_end: 4,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
    ]);

    let spans = SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(1, 3), Feature::Hover);
    assert_eq!(spans.len(), 2);
    assert_text_range_eq(spans[0].span, TextRange::new(1, 3));
    assert_text_range_eq(spans[1].span, TextRange::new(11, 13));
    for mapped in &spans {
        assert_eq!(mapped.fidelity, Fidelity::Approximate);
    }
}

#[test]
fn test_original_to_virtual_explicit_zero_features() {
    let m = SpanMap::new(&[Segment {
        virtual_start: 0,
        virtual_end: 3,
        original_start: 10,
        original_end: 13,
        kind: Kind::Verbatim,
        features: Feature::None,
    }]);

    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::Hover).len(),
        0
    );
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::Definition).len(),
        0
    );
    assert_eq!(
        SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(10, 13), Feature::Hover).len(),
        0
    );

    let data = m.marshal().unwrap();
    assert_eq!(data.as_slice(), b"[[0,3,10,3,0,0]]".as_slice());
    let decoded = unmarshal(&data).unwrap();
    let segments = SpanMap::segments(Some(&decoded));
    assert_eq!(segments[0].features, Feature::None);

    let legacy = unmarshal(b"[[0,3,10,3,0]]").unwrap();
    assert_eq!(SpanMap::segments(Some(&legacy))[0].features, Feature::All);
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&legacy), 11, Feature::Hover).len(),
        1
    );
}

#[test]
fn test_feature_participation_original_and_virtual() {
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 3,
            original_start: 10,
            original_end: 13,
            kind: Kind::Verbatim,
            features: Feature::Hover,
        },
        Segment {
            virtual_start: 3,
            virtual_end: 6,
            original_start: 20,
            original_end: 23,
            kind: Kind::Verbatim,
            features: Feature::Completion,
        },
    ]);

    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::Hover).len(),
        1
    );
    assert_eq!(
        SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::Completion).len(),
        0
    );

    let (mapped, fidelity) = SpanMap::virtual_to_original_span_for_feature(
        Some(&m),
        TextRange::new(0, 3),
        Feature::Hover,
    );
    assert_text_range_eq(mapped, TextRange::new(10, 13));
    assert_eq!(fidelity, Fidelity::Exact);
    let (_, fidelity) = SpanMap::virtual_to_original_span_for_feature(
        Some(&m),
        TextRange::new(0, 3),
        Feature::Completion,
    );
    assert_eq!(fidelity, Fidelity::None);

    // Diagnostics and edit safety use unfiltered geometry and cannot be disabled by feature flags.
    let (mapped, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(0, 3));
    assert_text_range_eq(mapped, TextRange::new(10, 13));
    assert_eq!(fidelity, Fidelity::Exact);
}

#[test]
fn test_original_to_virtual_span_round_trip() {
    // Original spans are out of order relative to virtual spans, exercising the reverse index.
    let m = SpanMap::new(&[
        Segment {
            virtual_start: 0,
            virtual_end: 10,
            original_start: 200,
            original_end: 210,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
        Segment {
            virtual_start: 10,
            virtual_end: 20,
            original_start: 100,
            original_end: 110,
            kind: Kind::Verbatim,
            features: Feature::All,
        },
    ]);

    for r in [TextRange::new(2, 8), TextRange::new(12, 18)] {
        let (orig, fidelity) = SpanMap::virtual_to_original_span(Some(&m), r);
        assert_eq!(fidelity, Fidelity::Exact);
        let back = SpanMap::original_to_virtual_spans(Some(&m), orig, Feature::All);
        assert_eq!(back.len(), 1);
        assert_eq!(back[0].fidelity, Fidelity::Exact);
        assert_eq!(back[0].span.pos(), r.pos());
        assert_eq!(back[0].span.end(), r.end());
    }
}

#[test]
fn test_marshal_round_trip() {
    let original = SpanMap::new(&[
        Segment {
            virtual_start: 3,
            virtual_end: 14,
            original_start: 60,
            original_end: 71,
            kind: Kind::Atom,
            ..Segment::default()
        },
        Segment {
            virtual_start: 14,
            virtual_end: 24,
            original_start: 71,
            original_end: 81,
            kind: Kind::Verbatim,
            ..Segment::default()
        },
    ]);

    let data = original.marshal().unwrap();
    let decoded = unmarshal(&data).unwrap();

    for r in [
        TextRange::new(1, 2),
        TextRange::new(4, 10),
        TextRange::new(16, 20),
    ] {
        let (want_range, want_fidelity) = SpanMap::virtual_to_original_span(Some(&original), r);
        let (got_range, got_fidelity) = SpanMap::virtual_to_original_span(Some(&decoded), r);
        assert_eq!(
            (got_range.pos(), got_range.end()),
            (want_range.pos(), want_range.end())
        );
        assert_eq!(got_fidelity, want_fidelity);
    }
}

#[test]
fn test_validate() {
    const TRANSFORMED: &str = "const greeting = 1;\n";
    const ORIGINAL: &str = "<x>const greeting = 1;\n</x>";
    let script_start = 3; // index of "const" in original

    #[derive(Default)]
    struct TestCase {
        name: &'static str,
        // PORT: `Vec` used for `[]Segment`; `segs: nil` → `vec![]`.
        segs: Vec<Segment>,
        want_kind: MappingErrorKind,
        want_ok: bool,
    }

    let test_cases = [
        TestCase {
            name: "valid verbatim",
            segs: vec![Segment {
                virtual_start: 0,
                virtual_end: TRANSFORMED.len() as TextPos,
                original_start: script_start,
                original_end: script_start + TRANSFORMED.len() as TextPos,
                kind: Kind::Verbatim,
                ..Segment::default()
            }],
            want_ok: true,
            ..TestCase::default()
        },
        TestCase {
            name: "empty is valid",
            segs: vec![],
            want_ok: true,
            ..TestCase::default()
        },
        TestCase {
            name: "gap is allowed",
            segs: vec![Segment {
                virtual_start: 3,
                virtual_end: TRANSFORMED.len() as TextPos,
                original_start: 0,
                original_end: 0,
                kind: Kind::Atom,
                ..Segment::default()
            }],
            want_ok: true,
            ..TestCase::default()
        },
        TestCase {
            name: "overlap",
            segs: vec![
                Segment {
                    virtual_start: 0,
                    virtual_end: 10,
                    original_start: 0,
                    original_end: 0,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
                Segment {
                    virtual_start: 5,
                    virtual_end: TRANSFORMED.len() as TextPos,
                    original_start: 0,
                    original_end: 0,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
            ],
            want_kind: MappingErrorKind::Overlap,
            ..TestCase::default()
        },
        TestCase {
            name: "original out of bounds",
            segs: vec![Segment {
                virtual_start: 0,
                virtual_end: TRANSFORMED.len() as TextPos,
                original_start: 0,
                original_end: ORIGINAL.len() as TextPos + 10,
                kind: Kind::Atom,
                ..Segment::default()
            }],
            want_kind: MappingErrorKind::OutOfBounds,
            ..TestCase::default()
        },
        TestCase {
            name: "verbatim text mismatch",
            segs: vec![Segment {
                virtual_start: 0,
                virtual_end: TRANSFORMED.len() as TextPos,
                original_start: 0,
                original_end: TRANSFORMED.len() as TextPos,
                kind: Kind::Verbatim,
                ..Segment::default()
            }],
            want_kind: MappingErrorKind::VerbatimMismatch,
            ..TestCase::default()
        },
        TestCase {
            name: "unknown kind",
            segs: vec![Segment {
                virtual_start: 0,
                virtual_end: 1,
                original_start: 0,
                original_end: 1,
                kind: Kind(3),
                ..Segment::default()
            }],
            want_kind: MappingErrorKind::Kind,
            ..TestCase::default()
        },
    ];

    for tc in &test_cases {
        // t.Run(tc.name, ...)
        let m = SpanMap::new(&tc.segs);
        let problem = SpanMap::validate(Some(&m), TRANSFORMED, ORIGINAL);
        if tc.want_ok {
            assert!(problem.is_none(), "expected valid, got {:?}", problem);
            continue;
        }
        let problem = problem.expect("expected a problem");
        assert_eq!(problem.kind, tc.want_kind, "{}", tc.name);
    }
}

#[test]
fn test_validate_original_overlap_and_features() {
    #[derive(Default)]
    struct TestCase {
        name: &'static str,
        segments: Vec<Segment>,
        want_kind: MappingErrorKind,
        valid: bool,
    }

    let tests = [
        TestCase {
            name: "identical duplicate group",
            segments: vec![
                Segment {
                    virtual_start: 0,
                    virtual_end: 3,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Verbatim,
                    features: Feature::Definition,
                },
                Segment {
                    virtual_start: 3,
                    virtual_end: 6,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Verbatim,
                    features: Feature::Hover,
                },
            ],
            valid: true,
            ..TestCase::default()
        },
        TestCase {
            name: "partial original overlap is valid",
            segments: vec![
                Segment {
                    virtual_start: 0,
                    virtual_end: 3,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
                Segment {
                    virtual_start: 3,
                    virtual_end: 6,
                    original_start: 2,
                    original_end: 5,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
            ],
            valid: true,
            ..TestCase::default()
        },
        TestCase {
            name: "nested original overlap is valid",
            segments: vec![
                Segment {
                    virtual_start: 0,
                    virtual_end: 5,
                    original_start: 0,
                    original_end: 5,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
                Segment {
                    virtual_start: 5,
                    virtual_end: 6,
                    original_start: 1,
                    original_end: 4,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
            ],
            valid: true,
            ..TestCase::default()
        },
        TestCase {
            name: "duplicate without explicit features is tolerant",
            segments: vec![
                Segment {
                    virtual_start: 0,
                    virtual_end: 3,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Atom,
                    ..Segment::default()
                },
                Segment {
                    virtual_start: 3,
                    virtual_end: 6,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Atom,
                    features: Feature::Definition,
                },
            ],
            valid: true,
            ..TestCase::default()
        },
        TestCase {
            name: "duplicate with shared feature members is tolerant",
            segments: vec![
                Segment {
                    virtual_start: 0,
                    virtual_end: 3,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Atom,
                    features: Feature::Hover,
                },
                Segment {
                    virtual_start: 3,
                    virtual_end: 6,
                    original_start: 0,
                    original_end: 3,
                    kind: Kind::Atom,
                    features: Feature::Hover | Feature::Definition,
                },
            ],
            valid: true,
            ..TestCase::default()
        },
        TestCase {
            name: "features on sole cover are valid",
            segments: vec![Segment {
                virtual_start: 0,
                virtual_end: 3,
                original_start: 0,
                original_end: 3,
                kind: Kind::Atom,
                features: Feature::Definition,
            }],
            valid: true,
            ..TestCase::default()
        },
        TestCase {
            name: "unknown feature flag",
            segments: vec![Segment {
                virtual_start: 0,
                virtual_end: 3,
                original_start: 0,
                original_end: 3,
                kind: Kind::Atom,
                features: Feature(1 << 22),
            }],
            want_kind: MappingErrorKind::Feature,
            ..TestCase::default()
        },
    ];

    for test in &tests {
        // t.Run(test.name, ...)
        let m = SpanMap::new(&test.segments);
        let problem = SpanMap::validate(Some(&m), "abcabc", "abcdef");
        if test.valid {
            assert!(problem.is_none(), "expected valid, got {:?}", problem);
            continue;
        }
        let problem = problem.expect("expected a problem");
        assert_eq!(problem.kind, test.want_kind, "{}", test.name);
    }
}

#[test]
fn test_validate_nil_is_valid() {
    let m: Option<&SpanMap> = None;
    assert!(SpanMap::validate(m, "abc", "abc").is_none());
}
