// Ported from tsc/internal/jsnum @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(shim): helpers standing in for the pieces of Go's `math/big` that
// num-bigint does not provide out of the box.
//
//   * `new(big.Int).SetString(s, 0)` auto-detects the base from a literal
//     prefix and accepts `_` digit separators; num-bigint's parsers do
//     neither, so the detection is replicated in `set_string_base0`.
//   * `Int.Float64()` / `new(big.Float).SetPrec(256).SetInt(x).Float64()`
//     convert to the nearest float64 with round-half-even. num-bigint has no
//     f64 conversion in scope, so `float64_from_big_int*` implement the exact
//     IEEE-754 conversion (including Go's two-step rounding at 256 bits for
//     the exponentiate path).

use num_bigint::{BigInt, BigUint, Sign};

// `new(big.Int).SetString(s, 0)` — base 0 auto-detects:
//   "0b"/"0B" → binary, "0o"/"0O" → octal, "0x"/"0X" → hex,
//   leading "0" → legacy octal, otherwise decimal. An optional leading sign
//   is accepted, and "_" may appear between digits / after the base prefix
//   (as in Go integer literals).
//
// Callers in this port only ever pass strings already validated as well-formed
// Go/JS integer literals, so the permissive "strip all underscores" handling
// is equivalent to Go's stricter placement rules.
pub(crate) fn set_string_base0(s: &str) -> Option<BigInt> {
    let (s, negative) = match s.strip_prefix('-') {
        Some(rest) => (rest, true),
        None => (s.strip_prefix('+').unwrap_or(s), false),
    };
    let (radix, digits) = match s.get(..2) {
        Some("0x") | Some("0X") => (16, &s[2..]),
        Some("0b") | Some("0B") => (2, &s[2..]),
        Some("0o") | Some("0O") => (8, &s[2..]),
        _ if s.len() > 1 && s.starts_with('0') => (8, &s[1..]),
        _ => (10, s),
    };
    let digits: String = digits.chars().filter(|&c| c != '_').collect();
    let mut bi = BigInt::parse_bytes(digits.as_bytes(), radix)?;
    if negative {
        bi = -bi;
    }
    Some(bi)
}

// `bi.Float64()` — the float64 nearest to bi (round-half-even, single
// correctly-rounded step: `new(big.Float).SetInt(x)` uses enough precision
// to represent x exactly, then Float64 rounds to 53 bits).
#[allow(dead_code)]
pub(crate) fn float64_from_big_int(bi: &BigInt) -> f64 {
    float64_from_big_int_prec(bi, u64::MAX)
}

// `new(big.Float).SetPrec(prec).SetInt(bi).Float64()` — the magnitude is
// first rounded to `prec` significant bits (round-half-even), then converted
// to float64 with a second round-half-even. Pass prec >= the bit length of bi
// (or u64::MAX) for a single correctly-rounded conversion.
pub(crate) fn float64_from_big_int_prec(bi: &BigInt, prec: u64) -> f64 {
    let sign = match bi.sign() {
        Sign::NoSign => return 0.0,
        Sign::Minus => -1.0,
        Sign::Plus => 1.0,
    };
    let mag = bi.magnitude();
    let n = mag.bits(); // >= 1

    // First rounding step: keep the top `prec` bits of the magnitude.
    // After this, value == keep * 2^shift with keep.bits() <= prec.
    let (keep, shift) = round_to_precision(mag, prec);

    // Second rounding step: keep the top 53 bits (the f64 significand,
    // including the implicit leading 1).
    let (mant, shift2) = round_to_precision(&keep, 53);

    // value == mant * 2^(shift+shift2) exactly, with mant < 2^53.
    let mant = u64::try_from(&mant).expect("mantissa fits in 53 bits");
    let e2 = shift + shift2;
    // mant is exactly representable; multiplying by a power of two is exact
    // except for overflow, which correctly saturates to ±Inf.
    sign * (mant as f64) * 2f64.powi(e2.min(i32::MAX as u64) as i32)
}

// Round `mag` (nonzero) to `prec` significant bits, round-half-even.
// Returns (keep, shift) such that value == keep * 2^shift and
// keep.bits() <= prec.
fn round_to_precision(mag: &BigUint, prec: u64) -> (BigUint, u64) {
    let n = mag.bits();
    if n <= prec {
        return (mag.clone(), 0);
    }
    let shift = n - prec;
    let mut keep = mag >> shift;
    let guard = mag.bit(shift - 1);
    // Sticky: any nonzero bit below the guard bit.
    let sticky = mag.trailing_zeros().is_none_or(|tz| tz < shift - 1);
    if guard && (sticky || keep.bit(0)) {
        keep += 1u32;
        if keep.bits() > prec {
            // Rounding carried out of the kept bits; the new value is
            // exactly 2^prec, represented with one more bit of shift.
            keep >>= 1u32;
            return (keep, shift + 1);
        }
    }
    (keep, shift)
}
