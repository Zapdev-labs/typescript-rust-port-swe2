// Ported from tsc/internal/ast/positionmap_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The Go benchmarks (BenchmarkComputePositionMap_ASCII/NonASCII/CheckerTS,
// BenchmarkUTF8ToUTF16_ASCII/NonASCII, BenchmarkUTF16ToUTF8_NonASCII) are
// omitted — there is no stable-Rust benchmark harness for `testing.B`.

use tsc_stringutil::encode_js_string_rune;

use crate::positionmap::compute_position_map;

#[test]
fn test_position_map_ascii() {
    let text = "const x = 1;";
    let pm = compute_position_map(text.as_bytes());
    assert!(pm.is_ascii_only(), "expected ASCII-only");
    for i in 0..=text.len() {
        assert_eq!(pm.utf8_to_utf16(i), i, "utf8_to_utf16({i})");
        assert_eq!(pm.utf16_to_utf8(i), i, "utf16_to_utf8({i})");
    }
}

#[test]
fn test_position_map_two_byte() {
    // "café" — é (U+00E9) is 2 bytes UTF-8, 1 code unit UTF-16
    let text = "const café = 1;\nconst x = 2;";
    let pm = compute_position_map(text.as_bytes());
    assert!(!pm.is_ascii_only(), "expected non-ASCII");

    // Everything before é (byte offset 9) should be identity
    for i in 0..10 {
        assert_eq!(pm.utf8_to_utf16(i), i, "before é: utf8_to_utf16({i})");
    }

    // é starts at UTF-8 byte 9, UTF-16 offset 9: same
    assert_eq!(pm.utf8_to_utf16(9), 9, "at é");

    // After é (byte 11 in UTF-8 = code unit 10 in UTF-16), delta is 1
    // ' ' after café: UTF-8 byte 11, UTF-16 offset 10
    assert_eq!(pm.utf8_to_utf16(11), 10, "after é");

    // 'x' on second line: UTF-8 byte 23, UTF-16 offset 22
    let x_utf8 = text.rfind('x').unwrap();
    assert_eq!(pm.utf8_to_utf16(x_utf8), x_utf8 - 1, "at x");

    // Reverse: UTF-16 offset 22 should map to UTF-8 byte 23
    let x_utf16 = x_utf8 - 1;
    assert_eq!(pm.utf16_to_utf8(x_utf16), x_utf8, "reverse at x");
}

#[test]
fn test_position_map_four_byte() {
    // 🎉 (U+1F389) is 4 bytes UTF-8, 2 code units UTF-16
    let text = "const a = \"🎉\";\nconst b = 2;";
    let pm = compute_position_map(text.as_bytes());
    assert!(!pm.is_ascii_only(), "expected non-ASCII");

    // 🎉 starts at byte 11 (after `const a = "`)
    // UTF-8: bytes 11-14 (4 bytes), UTF-16: units 11-12 (2 code units)
    // After 🎉: UTF-8 byte 15, UTF-16 offset 13. Delta = 2.

    // 'b' on second line
    let b_utf8 = text.rfind('b').unwrap();
    let b_utf16 = b_utf8 - 2; // delta of 2 from emoji
    assert_eq!(pm.utf8_to_utf16(b_utf8), b_utf16, "at b");
    assert_eq!(pm.utf16_to_utf8(b_utf16), b_utf8, "reverse at b");
}

#[test]
fn test_position_map_multiple_non_ascii() {
    // Mix of 2-byte and 4-byte characters
    // "à" (U+00E0) = 2 bytes UTF-8, 1 code unit UTF-16 (delta +1)
    // "🎉" (U+1F389) = 4 bytes UTF-8, 2 code units UTF-16 (delta +2)
    let text = "à🎉x";
    let pm = compute_position_map(text.as_bytes());

    // à: UTF-8 [0,2), UTF-16 [0,1)
    // 🎉: UTF-8 [2,6), UTF-16 [1,3)
    // x: UTF-8 [6,7), UTF-16 [3,4)
    let tests: [(usize, usize); 4] = [
        (0, 0),
        (2, 1), // start of 🎉
        (6, 3), // x
        (7, 4), // end
    ];
    for (utf8, utf16) in tests {
        assert_eq!(pm.utf8_to_utf16(utf8), utf16, "utf8_to_utf16({utf8})");
        assert_eq!(pm.utf16_to_utf8(utf16), utf8, "utf16_to_utf8({utf16})");
    }
}

#[test]
fn test_position_map_lone_surrogate_sentinel() {
    let mut text = b"a".to_vec();
    text.extend_from_slice(&encode_js_string_rune(0xD800));
    text.extend_from_slice(b"b");
    let pm = compute_position_map(&text);
    assert!(!pm.is_ascii_only(), "expected non-ASCII");

    assert_eq!(pm.utf8_to_utf16(text.len()), 3);
    assert_eq!(pm.utf16_to_utf8(2), text.len() - 1);
}

#[test]
fn test_position_map_roundtrip() {
    let text = "let café = \"🎉\"; // naïve";
    let pm = compute_position_map(text.as_bytes());

    // Convert every valid UTF-16 position to UTF-8 and back
    let utf16_len = pm.utf8_to_utf16(text.len());
    for i in 0..=utf16_len {
        let utf8_pos = pm.utf16_to_utf8(i);
        let back = pm.utf8_to_utf16(utf8_pos);
        assert_eq!(
            back, i,
            "roundtrip UTF16->UTF8->UTF16: {i} -> {utf8_pos} -> {back}"
        );
    }
}
