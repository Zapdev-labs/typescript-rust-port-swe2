// PORT(shim): tsc-stringutil is being ported concurrently and does not yet
// expose these helpers. Faithful minimal ports of the functions jsnum needs
// from tsc/internal/stringutil/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763.
// Replace `use crate::stringutil_shim as stringutil` with `use tsc_stringutil as
// stringutil` once the real crate lands.

#![allow(dead_code)]

// Ported from tsc/internal/stringutil/util.go (IsDigit).
pub(crate) fn is_digit(ch: char) -> bool {
    ch.is_ascii_digit()
}

// Ported from tsc/internal/stringutil/util.go (IsOctalDigit).
pub(crate) fn is_octal_digit(ch: char) -> bool {
    ('0'..='7').contains(&ch)
}

// Ported from tsc/internal/stringutil/util.go (IsHexDigit).
pub(crate) fn is_hex_digit(ch: char) -> bool {
    ch.is_ascii_hexdigit()
}
