// Ported from tsc/internal/jsnum/string.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;

use crate::bigint_shim;
use crate::jsnum::{inf, nan, MAX_SAFE_INTEGER, MIN_SAFE_INTEGER};
use crate::stringutil_shim as stringutil;
use crate::Number;

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
        if MIN_SAFE_INTEGER.0 <= n && n <= MAX_SAFE_INTEGER.0 {
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
// emits the shortest round-tripping digit string `d[.ddd]e<exp>` — the same
// digits ECMAScript's `s` selects (minimal k, nearest value, ties to even) —
// so only the placement rules (where to put the point / how many zeros /
// which notation) need implementing here.
fn format_ecmascript(n: f64) -> String {
    let mut out = String::new();
    if n.is_sign_negative() {
        out.push('-');
    }
    // Rust's LowerExp format yields "d", "d.ddd", followed by "e" and the
    // decimal exponent, e.g. "5e-324", "1e21", "1.2345678e6".
    let sci = format!("{:e}", n.abs());
    let epos = sci.rfind('e').expect("LowerExp always contains 'e'");
    let exp: i32 = sci[epos + 1..].parse().expect("LowerExp exponent is an integer");
    let digits: String = sci[..epos].chars().filter(|&c| c != '.').collect();
    let k = digits.len() as i32; // number of digits of s
    let n10 = exp + 1; // the spec's n: value = s * 10^(n - k)

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

    let s = if !negative { s.strip_prefix('+').unwrap_or(s) } else { s };

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
        ' ' | '\u{A0}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200A}'
            | '\u{202F}'
            | '\u{205F}'
            | '\u{3000}'
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
        match i64::from_str_radix(s, 10) {
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
        let c = if !negative { c.strip_prefix('+').unwrap_or(c) } else { c };
        let c = trim_leading_zeros(c);
        if !is_all_digits(c) {
            return f64::NAN;
        }
        sb.push_str(c);
    }

    string_to_float64(&sb)
}

fn cut_any(s: &str, cutset: &str) -> (&str, &str, bool) {
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
