// Ported from tsc/internal/jsnum/string.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;

use crate::Number;
use crate::bigint_shim;
use crate::jsnum::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER, inf, nan};
use tsc_stringutil as stringutil;

impl Number {
    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-tostring
    pub fn string(self) -> String {
        let n = self.0;
        if self.is_nan() {
            return "NaN".to_string();
        }
        if self.is_inf() {
            return if n < 0.0 { "-Infinity" } else { "Infinity" }.to_string();
        }

        // Fast path: for safe integers, directly convert to string.
        if (MIN_SAFE_INTEGER.0..=MAX_SAFE_INTEGER.0).contains(&n) {
            let i = n as i64;
            if i as f64 == n {
                return i.to_string(); // strconv.FormatInt(i, 10)
            }
        }

        // Otherwise, the Go json package handles this correctly.
        // PORT: Go delegates to json.Marshal(float64), which formats per
        // ECMAScript Number::toString (shortest round-trip digits, decimal
        // notation iff -6 < n <= 21). Implemented directly here — see
        // format_ecmascript below.
        format_ecmascript(n)
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.string())
    }
}

// PORT: ECMAScript §6.1.6.1.20 Number::toString for finite non-safe-integer
// values (replacing Go's json.Marshal delegation). Rust's `{:e}` formatter
// emits a shortest round-tripping digit string `d[.ddd]e<exp>` whose length k
// is the spec's minimal k — but when several k-digit decimals round-trip,
// Rust may pick a different s than ECMAScript/Go (e.g. {:e} of 2^-25 yields
// "2.9802322387695313e-8" where JS prints "2.9802322387695312e-8"). The spec
// requires the k-digit decimal *closest* to the true binary value (ties →
// even s); correctly-rounded formatting is NOT a substitute — it can pick a
// decimal that doesn't even round-trip (e.g. rounding 2^-695 to 16 digits
// yields "...511" which parses to the adjacent float; only "...512" is in
// the rounding interval). So we take k from `{:e}`, enumerate every k-digit
// decimal that round-trips (they form a contiguous interval), and pick the
// closest by exact big-integer distance.
fn format_ecmascript(n: f64) -> String {
    let mut out = String::new();
    if n.is_sign_negative() {
        out.push('-');
    }
    // Rust's LowerExp format yields "d", "d.ddd", followed by "e" and the
    // decimal exponent, e.g. "5e-324", "1e21", "1.2345678e6".
    let shortest = format!("{:e}", n.abs());
    let epos = shortest.find('e').expect("LowerExp always contains 'e'");
    let exp: i32 = shortest[epos + 1..]
        .parse()
        .expect("LowerExp exponent is an integer");
    let digits_str: String = shortest[..epos].chars().filter(|&c| c != '.').collect();
    let s0: u64 = digits_str
        .parse()
        .expect("shortest digits fit in u64 (k <= 17)");
    let k = digits_str.len() as i32; // number of digits of s
    let n10 = exp + 1; // the spec's n: value = s * 10^(n - k)
    let s = select_round_trip_s(n.abs(), s0, k, n10 - k);
    let digits = s.to_string();
    debug_assert_eq!(digits.len() as i32, k);

    if k <= n10 && n10 <= 21 {
        // s followed by n-k zeros → integer.
        out.push_str(&digits);
        out.push_str(&"0".repeat((n10 - k) as usize));
    } else if 0 < n10 && n10 <= 21 {
        // Decimal point inside the digits.
        out.push_str(&digits[..n10 as usize]);
        out.push('.');
        out.push_str(&digits[n10 as usize..]);
    } else if -6 < n10 && n10 <= 0 {
        // "0." followed by -n zeros and the digits.
        out.push_str("0.");
        out.push_str(&"0".repeat(-n10 as usize));
        out.push_str(&digits);
    } else {
        // Exponential notation: d[.ddd]e±(n-1).
        out.push_str(&digits[..1]);
        if k > 1 {
            out.push('.');
            out.push_str(&digits[1..]);
        }
        out.push('e');
        let m = n10 - 1;
        if m >= 0 {
            out.push('+');
        }
        out.push_str(&m.to_string());
    }
    out
}

// The k-digit integers s for which s * 10^q round-trips to the same f64 form
// a contiguous interval (the IEEE-754 rounding interval of that float).
// Collect them all by scanning outward from a known-valid s0, then return the
// one closest to the exact value (the spec's s; ties resolve to even s).
fn select_round_trip_s(n_abs: f64, s0: u64, k: i32, q: i32) -> u64 {
    let lo = 10u64.pow((k - 1) as u32);
    let hi = 10u64.pow(k as u32) - 1;
    let round_trips = |s: u64| -> bool {
        // Rust's f64 parse is correctly rounded: `s * 10^q` parses back to
        // n_abs iff the decimal lies within its rounding interval.
        format!("{s}e{q}")
            .parse::<f64>()
            .is_ok_and(|v| v.to_bits() == n_abs.to_bits())
    };
    debug_assert!(round_trips(s0));

    // Decompose n_abs = mant * 2^exp2 exactly.
    let bits = n_abs.to_bits();
    let frac = bits & ((1 << 52) - 1);
    let biased = (bits >> 52) as i32;
    let (mant, exp2) = if biased == 0 {
        (frac, -1074) // subnormal
    } else {
        (frac | (1 << 52), biased - 1075)
    };

    let mut best_s = s0;
    let mut best_diff = decimal_distance(s0, q, mant, exp2);
    // Scan the contiguous interval of valid candidates outward from s0.
    for step in 1..=64u64 {
        let mut progressed = false;
        if let Some(c) = s0.checked_add(step).filter(|&c| c <= hi) {
            if round_trips(c) {
                progressed = true;
                let d = decimal_distance(c, q, mant, exp2);
                if d < best_diff || (d == best_diff && c % 2 == 0 && best_s % 2 == 1) {
                    best_s = c;
                    best_diff = d;
                }
            }
        }
        if let Some(c) = s0.checked_sub(step).filter(|&c| c >= lo) {
            if round_trips(c) {
                progressed = true;
                let d = decimal_distance(c, q, mant, exp2);
                if d < best_diff || (d == best_diff && c % 2 == 0 && best_s % 2 == 1) {
                    best_s = c;
                    best_diff = d;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    best_s
}

// |mant * 2^exp2 - s * 10^q| computed exactly, scaled by the positive factor
// 2^-min(exp2, q, 0) * 5^max(0, -q) so both terms are integers; the scale is
// identical for all candidates of one call site, so comparisons are valid.
fn decimal_distance(s: u64, q: i32, mant: u64, exp2: i32) -> num_bigint::BigUint {
    use num_bigint::BigInt;
    let shift = exp2.min(q).min(0);
    let g = (-q).max(0) as u32;
    // left = mant * 2^(exp2-shift) * 5^g
    let mut left = BigInt::from(mant);
    if g > 0 {
        left *= BigInt::from(5u32).pow(g);
    }
    left <<= (exp2 - shift) as usize;
    // right = s * 2^(q-shift) * 5^max(q,0)
    let mut right = BigInt::from(s);
    if q > 0 {
        right *= BigInt::from(5u32).pow(q as u32);
    }
    right <<= (q - shift) as usize;
    (left - right).magnitude().clone()
}

// https://tc39.es/ecma262/2024/multipage/abstract-operations.html#sec-stringtonumber
pub fn from_string(s: &str) -> Number {
    // Implementing StringToNumber exactly as written in the spec involves
    // writing a parser, along with the conversion of the parsed AST into the
    // actual value.
    //
    // We've already implemented a number parser in the scanner, but we can't
    // import it here. We also do not have the conversion implemented since we
    // previously just wrote `+literal` and let the runtime handle it.
    //
    // The strategy below is to instead break the number apart and fix it up
    // such that Go's own parsing functionality can handle it. This won't be
    // the fastest method, but it saves us from writing the full parser and
    // conversion logic.

    let s = s.trim_matches(is_str_white_space);

    match s {
        "" => return Number(0.0),
        "Infinity" | "+Infinity" => return inf(1),
        "-Infinity" => return inf(-1),
        _ => {}
    }

    for r in s.chars() {
        if !is_number_rune(r) {
            return nan();
        }
    }

    if let Some(n) = try_parse_int(s) {
        return n;
    }

    // Cut this off first so we can ensure -0 is returned as -0.
    let (s, negative) = match s.strip_prefix('-') {
        Some(rest) => (rest, true),
        None => (s, false),
    };

    let s = if !negative {
        s.strip_prefix('+').unwrap_or(s)
    } else {
        s
    };

    // utf8.DecodeRuneInString returns utf8.RuneError (U+FFFD) for the empty string.
    let first = s.chars().next().unwrap_or('\u{FFFD}');
    if !stringutil::is_digit(first) && first != '.' {
        return nan();
    }

    let f = parse_float_string(s);
    if f.is_nan() {
        return nan();
    }

    let sign = if negative { -1.0 } else { 1.0 };
    Number(f.copysign(sign))
}

fn is_str_white_space(r: char) -> bool {
    // This is different than stringutil.IsWhiteSpaceLike.

    // https://tc39.es/ecma262/2024/multipage/ecmascript-language-lexical-grammar.html#prod-LineTerminator
    // https://tc39.es/ecma262/2024/multipage/ecmascript-language-lexical-grammar.html#prod-WhiteSpace

    match r {
        // LineTerminator
        '\n' | '\r' | '\u{2028}' | '\u{2029}' => return true,
        // WhiteSpace
        '\t' | '\u{b}' | '\u{c}' | '\u{FEFF}' => return true,
        _ => {}
    }

    // WhiteSpace
    // unicode.Is(unicode.Zs, r): the Zs (space separator) category is exactly
    // these code points.
    matches!(
        r,
        ' ' | '\u{A0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200A}' | '\u{202F}' | '\u{205F}' | '\u{3000}'
    )
}

// PORT: `var errUnknownPrefix = errors.New("unknown number prefix")` — declared
// but unused in the Go source; kept for parity.
#[allow(dead_code)]
const ERR_UNKNOWN_PREFIX: &str = "unknown number prefix";

// PORT: Go returns (Number, bool); Rust returns Option<Number> (None = (0, false)).
fn try_parse_int(s: &str) -> Option<Number> {
    let mut s = s;
    let mut i: i64 = 0;
    let mut err = false;
    let mut has_int_result = false;

    if s.len() > 2 {
        let (prefix, rest) = s.split_at(2);
        match prefix {
            "0b" | "0B" => {
                if !is_all_binary_digits(rest) {
                    return Some(nan());
                }
                match i64::from_str_radix(rest, 2) {
                    Ok(v) => i = v,
                    Err(_) => err = true,
                }
                has_int_result = true;
            }
            "0o" | "0O" => {
                if !is_all_octal_digits(rest) {
                    return Some(nan());
                }
                match i64::from_str_radix(rest, 8) {
                    Ok(v) => i = v,
                    Err(_) => err = true,
                }
                has_int_result = true;
            }
            "0x" | "0X" => {
                if !is_all_hex_digits(rest) {
                    return Some(nan());
                }
                match i64::from_str_radix(rest, 16) {
                    Ok(v) => i = v,
                    Err(_) => err = true,
                }
                has_int_result = true;
            }
            _ => {}
        }
    }

    if !has_int_result {
        // StringToNumber does not parse leading zeros as octal.
        s = trim_leading_zeros(s);
        if !is_all_digits(s) {
            return None;
        }
        match s.parse::<i64>() {
            Ok(v) => i = v,
            Err(_) => err = true,
        }
        has_int_result = true;
    }

    if has_int_result && !err {
        return Some(Number(i as f64));
    }

    // Using this to parse large integers.
    // Go: new(big.Int).SetString(s, 0)
    let Some(bi) = bigint_shim::set_string_base0(s) else {
        return Some(nan());
    };

    // Go: bi.Float64()
    Some(Number(bigint_shim::float64_from_big_int(&bi)))
}

fn parse_float_string(s: &str) -> f64 {
    // <a>
    // <a>.<b>
    // <a>.<b>e<c>
    // <a>e<c>
    let a: &str;
    let b: &str;
    let c: &str;
    let has_exp: bool;

    let (a0, rest, has_dot) = match s.split_once('.') {
        Some((a, rest)) => (a, rest, true),
        None => (s, "", false),
    };
    if has_dot {
        // <a>.<b>
        // <a>.<b>e<c>
        (b, c, has_exp) = cut_any(rest, "eE");
        a = a0;
    } else {
        // <a>
        // <a>e<c>
        (a, c, has_exp) = cut_any(s, "eE");
        b = "";
    }

    let mut sb = String::with_capacity(a.len() + b.len() + c.len() + 3);

    if a.is_empty() {
        if has_dot && b.is_empty() {
            return f64::NAN;
        }
        if has_exp && c.is_empty() {
            return f64::NAN;
        }
        sb.push('0');
    } else {
        let a = trim_leading_zeros(a);
        if !is_all_digits(a) {
            return f64::NAN;
        }
        sb.push_str(a);
    }

    if has_dot {
        sb.push('.');
        if b.is_empty() {
            sb.push('0');
        } else {
            let b = trim_trailing_zeros(b);
            if !is_all_digits(b) {
                return f64::NAN;
            }
            sb.push_str(b);
        }
    }

    if has_exp {
        sb.push('e');

        let (c, negative) = match c.strip_prefix('-') {
            Some(rest) => (rest, true),
            None => (c, false),
        };
        if negative {
            sb.push('-');
        }
        let c = if !negative {
            c.strip_prefix('+').unwrap_or(c)
        } else {
            c
        };
        let c = trim_leading_zeros(c);
        if !is_all_digits(c) {
            return f64::NAN;
        }
        sb.push_str(c);
    }

    string_to_float64(&sb)
}

fn cut_any<'a>(s: &'a str, cutset: &str) -> (&'a str, &'a str, bool) {
    if let Some(i) = s.find(|c| cutset.contains(c)) {
        let before = &s[..i];
        let after_and_found = &s[i..];
        // utf8.DecodeRuneInString: skip the (single) rune at position i.
        let size = after_and_found.chars().next().map_or(0, char::len_utf8);
        let after = &after_and_found[size..];
        return (before, after, true);
    }
    (s, "", false)
}

fn trim_leading_zeros(s: &str) -> &str {
    if s.starts_with('0') {
        let s = s.trim_start_matches('0');
        if s.is_empty() {
            return "0";
        }
        return s;
    }
    s
}

fn trim_trailing_zeros(s: &str) -> &str {
    if s.ends_with('0') {
        let s = s.trim_end_matches('0');
        if s.is_empty() {
            return "0";
        }
        return s;
    }
    s
}

fn string_to_float64(s: &str) -> f64 {
    // PORT: Go's strconv.ParseFloat returns the value alongside ErrRange for
    // over/underflow; Rust's f64::from_str saturates to ±Inf / denormal or 0
    // with no error, which is the same value Go returns.
    s.parse::<f64>().unwrap_or(f64::NAN)
}

fn is_all_digits(s: &str) -> bool {
    for r in s.chars() {
        if !stringutil::is_digit(r) {
            return false;
        }
    }
    true
}

fn is_all_binary_digits(s: &str) -> bool {
    for r in s.chars() {
        if r != '0' && r != '1' {
            return false;
        }
    }
    true
}

fn is_all_octal_digits(s: &str) -> bool {
    for r in s.chars() {
        if !stringutil::is_octal_digit(r) {
            return false;
        }
    }
    true
}

fn is_all_hex_digits(s: &str) -> bool {
    for r in s.chars() {
        if !stringutil::is_hex_digit(r) {
            return false;
        }
    }
    true
}

fn is_number_rune(r: char) -> bool {
    if stringutil::is_digit(r) {
        return true;
    }

    if ('a'..='f').contains(&r) {
        return true;
    }

    if ('A'..='F').contains(&r) {
        return true;
    }

    matches!(r, '.' | '-' | '+' | 'x' | 'X' | 'o' | 'O')
}
