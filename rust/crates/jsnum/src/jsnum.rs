// Ported from tsc/internal/jsnum/jsnum.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Package jsnum provides JS-like number handling.

use num_bigint::BigInt;

use crate::bigint_shim;

pub const MAX_SAFE_INTEGER: Number = Number(9007199254740991.0); // 1<<53 - 1
pub const MIN_SAFE_INTEGER: Number = Number(-9007199254740991.0); // -MaxSafeInteger

// Number represents a JS-like number.
//
// All operations that can be performed directly on this type
// (e.g., conversion, arithmetic, etc.) behave as they would in JavaScript,
// but any other operation should use this type's methods,
// not the "math" package and conversions.
//
// PORT: `type Number float64` → newtype `Number(pub f64)`. Go's `float64(n)`
// and `Number(f)` conversions become `n.0` and `Number(f)` / `f.into()`.
#[derive(Clone, Copy, Default, Debug, PartialEq, PartialOrd)]
pub struct Number(pub f64);

impl From<f64> for Number {
    fn from(f: f64) -> Number {
        Number(f)
    }
}

impl From<Number> for f64 {
    fn from(n: Number) -> f64 {
        n.0
    }
}

// JS `+ - * /` on numbers are exactly the IEEE-754 float64 operations
// (including -0 and NaN propagation), so Go's `leftNum * rightNum` etc.
// port directly to these ops.
impl std::ops::Add for Number {
    type Output = Number;
    fn add(self, rhs: Number) -> Number {
        Number(self.0 + rhs.0)
    }
}

impl std::ops::Sub for Number {
    type Output = Number;
    fn sub(self, rhs: Number) -> Number {
        Number(self.0 - rhs.0)
    }
}

impl std::ops::Mul for Number {
    type Output = Number;
    fn mul(self, rhs: Number) -> Number {
        Number(self.0 * rhs.0)
    }
}

impl std::ops::Div for Number {
    type Output = Number;
    fn div(self, rhs: Number) -> Number {
        Number(self.0 / rhs.0)
    }
}

impl std::ops::Neg for Number {
    type Output = Number;
    fn neg(self) -> Number {
        Number(-self.0)
    }
}

// Mixed comparisons with untyped constants (`n == 0`, `numValue.Abs() >= 32`
// in Go) compare against float64.
impl PartialEq<f64> for Number {
    fn eq(&self, other: &f64) -> bool {
        self.0 == *other
    }
}
impl PartialEq<Number> for f64 {
    fn eq(&self, other: &Number) -> bool {
        *self == other.0
    }
}
impl PartialOrd<f64> for Number {
    fn partial_cmp(&self, other: &f64) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}
impl PartialOrd<Number> for f64 {
    fn partial_cmp(&self, other: &Number) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.0)
    }
}

pub const fn nan() -> Number {
    Number(f64::NAN)
}

impl Number {
    pub fn is_nan(self) -> bool {
        self.0.is_nan()
    }
}

pub const fn inf(sign: i32) -> Number {
    Number(if sign >= 0 {
        f64::INFINITY
    } else {
        f64::NEG_INFINITY
    })
}

impl Number {
    pub fn is_inf(self) -> bool {
        self.0.is_infinite()
    }
}

fn is_non_finite(x: f64) -> bool {
    // This is equivalent to checking `math.IsNaN(x) || math.IsInf(x, 0)` in one operation.
    const MASK: u64 = 0x7FF0000000000000;
    x.to_bits() & MASK == MASK
}

impl Number {
    // https://tc39.es/ecma262/2024/multipage/abstract-operations.html#sec-touint32
    // PORT: unexported in Go (package-private) → pub(crate).
    pub(crate) fn to_uint32(self) -> u32 {
        // The only difference between ToUint32 and ToInt32 is the interpretation of the bits.
        self.to_int32() as u32
    }

    // https://tc39.es/ecma262/2024/multipage/abstract-operations.html#sec-toint32
    pub(crate) fn to_int32(self) -> i32 {
        let x = self.0;

        // Fast path: if the number is in the range (-2^31, 2^32), i.e. an SMI,
        // then we don't need to do any special mapping.
        // PORT: Go's `int32(x)` for out-of-range/NaN floats is implementation-
        // defined (amd64/arm64 yield MinInt32); Rust's `as` saturates and maps
        // NaN to 0. Both never satisfy `smi as f64 == x` in those cases, so the
        // slow path is reached identically.
        let smi = x as i32;
        if smi as f64 == x {
            return smi;
        }

        // 2. If number is not finite or number is either +0𝔽 or -0𝔽, return +0𝔽.
        // Zero was covered by the test above.
        if is_non_finite(x) {
            return 0;
        }

        // Let int be truncate(ℝ(number)).
        let x = x.trunc();
        // Let int32bit be int modulo 2**32.
        let x = x % 4294967296.0; // math.Mod(x, 1<<32)
        // If int32bit ≥ 2**31, return 𝔽(int32bit - 2**32); otherwise return 𝔽(int32bit).
        (x as i64) as i32
    }

    fn to_shift_count(self) -> u32 {
        self.to_uint32() & 31
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-signedRightShift
    pub fn signed_right_shift(self, y: Number) -> Number {
        Number((self.to_int32() >> y.to_shift_count()) as f64)
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-unsignedRightShift
    pub fn unsigned_right_shift(self, y: Number) -> Number {
        Number((self.to_uint32() >> y.to_shift_count()) as f64)
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-leftShift
    pub fn left_shift(self, y: Number) -> Number {
        Number((self.to_int32() << y.to_shift_count()) as f64)
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-bitwiseNOT
    pub fn bitwise_not(self) -> Number {
        Number(!self.to_int32() as f64)
    }

    // The below are implemented by https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numberbitwiseop.

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-bitwiseOR
    pub fn bitwise_or(self, y: Number) -> Number {
        Number((self.to_int32() | y.to_int32()) as f64)
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-bitwiseAND
    pub fn bitwise_and(self, y: Number) -> Number {
        Number((self.to_int32() & y.to_int32()) as f64)
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-bitwiseXOR
    pub fn bitwise_xor(self, y: Number) -> Number {
        Number((self.to_int32() ^ y.to_int32()) as f64)
    }

    // PORT: unexported in Go and currently unused; retained for parity.
    #[allow(dead_code)]
    pub(crate) fn trunc(self) -> Number {
        Number(self.0.trunc())
    }

    pub fn floor(self) -> Number {
        Number(self.0.floor())
    }

    pub fn abs(self) -> Number {
        Number(self.0.abs())
    }
}

// PORT: Go `var negativeZero = Number(math.Copysign(0, -1))` → const.
// Package-private in Go; only used by tests in this port.
#[allow(dead_code)]
pub(crate) const NEGATIVE_ZERO: Number = Number(-0.0);

impl Number {
    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-remainder
    pub fn remainder(self, d: Number) -> Number {
        let n = self;
        if n.is_nan() || d.is_nan() {
            return nan();
        }
        if n.is_inf() {
            return nan();
        }
        if d.is_inf() {
            return n;
        }
        if d == 0.0 {
            return nan();
        }
        if n == 0.0 {
            return n;
        }
        // math.Mod is IEEE-754 fmod; Rust's `%` on f64 has identical semantics.
        Number(n.0 % d.0)
    }

    // https://tc39.es/ecma262/2024/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-exponentiate
    pub fn exponentiate(self, exponent: Number) -> Number {
        let base = self;
        if (base == 1.0 || base == -1.0) && exponent.is_inf() {
            return nan();
        }
        if base == 1.0 && exponent.is_nan() {
            return nan();
        }

        let b = base.0;
        let e = exponent.0;

        // For integer base ** integer exponent where the result exceeds 53 bits,
        // math.Pow can be off by multiple ULPs vs JS engines. Use exact big.Int
        // arithmetic and IEEE 754 round-to-nearest-even conversion instead.
        // The ES spec (§6.1.6.1.3) says exponentiate returns an
        // "implementation-approximated" value, so engines are allowed to differ.
        // This won't exactly match every engine (V8's fdlibm-compiled pow can
        // round halfway ties differently), but will always be within 1 ULP
        // (unit in the last place, i.e. the least significant bit of the result).
        //
        // PORT: `b >= math.MinInt64 && b <= math.MaxInt64` — converting Go's
        // untyped int64 bounds to float64 yields exactly -2^63 and 2^63;
        // `i64::MIN as f64` / `i64::MAX as f64` produce the same values.
        if b >= i64::MIN as f64
            && b <= i64::MAX as f64
            && b == b.trunc()
            && e >= 0.0
            && e <= i64::MAX as f64
            && e == e.trunc()
            && !e.is_infinite()
        {
            let magnitude = e * b.abs().log2();
            if magnitude > 53.0 && magnitude <= f64::MAX.log2() {
                // PORT: Go's `int64(b)` conversion is implementation-defined for
                // out-of-range floats; on amd64/arm64, b == 2^63 (the only value
                // passing the bound above that doesn't fit int64) converts to
                // math.MinInt64. Rust's `as` saturates to i64::MAX instead —
                // replicate Go's observable behavior exactly.
                let bi = if b == 9_223_372_036_854_775_808.0 {
                    i64::MIN
                } else {
                    b as i64
                };
                // Go: new(big.Int).Exp(big.NewInt(int64(b)), big.NewInt(int64(e)), nil)
                let ri = BigInt::from(bi).pow(e as u32);
                // Go: new(big.Float).SetPrec(256).SetInt(ri).Float64()
                let result = bigint_shim::float64_from_big_int_prec(&ri, 256);
                return Number(result);
            }
        }

        Number(b.powf(e))
    }
}
