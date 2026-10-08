// Shared Go `unicode/utf8` + `unicode/utf16` shims for the lsconv port
// (baseline ec47d33c23e464a17cdf2475632cba629bee8763).
//
// PORT: these are byte-for-byte ports of the Go stdlib routines, copied from
// the same local implementations in `tsc-scanner` (the `unicode` module in
// `tsc-stringutil` is crate-private, so each consumer keeps its own copy).

/// `utf8.RuneError` — the "error" rune, U+FFFD.
pub(crate) const RUNE_ERROR: i32 = 0xFFFD;

/// `utf8.RuneSelf` — characters below are represented as single bytes.
pub(crate) const RUNE_SELF: i32 = 0x80;

/// PORT: mirrors Go's `utf8.DecodeRuneInString` (RFC 3629-strict decoding):
/// empty input -> (RuneError, 0); invalid encoding -> (RuneError, 1);
/// otherwise the decoded rune and its width in bytes.
pub(crate) fn decode_rune_in_string(s: &[u8]) -> (i32, usize) {
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

/// `utf16.RuneLen` — 1 for BMP code points, 2 for non-BMP, -1 for values that
/// are negative, in the surrogate range, or above `utf8.MaxRune`.
pub(crate) fn utf16_rune_len(r: i32) -> i32 {
    const SURR1: i32 = 0xD800;
    const SURR3: i32 = 0xE000;
    const SURR_SELF: i32 = 0x10000;
    const MAX_RUNE: i32 = 0x10FFFF;
    if r < 0 {
        -1
    } else if r < SURR1 || (SURR3..SURR_SELF).contains(&r) {
        // Go: `case 0 <= r && r < surr1, surr3 <= r && r < surrSelf:`
        // (the `0 <= r` half is subsumed by the `r < 0` check above).
        1
    } else if (SURR_SELF..=MAX_RUNE).contains(&r) {
        2
    } else {
        -1
    }
}
