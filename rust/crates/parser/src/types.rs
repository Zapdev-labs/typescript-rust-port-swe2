// Ported from tsc/internal/parser/types.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::ops::{BitAnd, BitOr, BitOrAssign};

// ParseFlags

/// `type ParseFlags uint32`
///
/// PORT: `flag_type!` is crate-internal to `tsc-ast`, so the handful of bit
/// operators the parser needs are implemented inline.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct ParseFlags(pub u32);

impl ParseFlags {
    /// `ParseFlagsNone`
    pub const NONE: ParseFlags = ParseFlags(0);
    /// `ParseFlagsYield`
    pub const YIELD: ParseFlags = ParseFlags(1 << 0);
    /// `ParseFlagsAwait`
    pub const AWAIT: ParseFlags = ParseFlags(1 << 1);
    /// `ParseFlagsType`
    pub const TYPE: ParseFlags = ParseFlags(1 << 2);
    /// `ParseFlagsIgnoreMissingOpenBrace`
    pub const IGNORE_MISSING_OPEN_BRACE: ParseFlags = ParseFlags(1 << 4);
    /// `ParseFlagsJSDoc`
    pub const JSDOC: ParseFlags = ParseFlags(1 << 5);

    /// `flags & f != 0`
    #[inline]
    pub const fn intersects(self, f: ParseFlags) -> bool {
        self.0 & f.0 != 0
    }
}

impl BitOr for ParseFlags {
    type Output = ParseFlags;
    #[inline]
    fn bitor(self, rhs: ParseFlags) -> ParseFlags {
        ParseFlags(self.0 | rhs.0)
    }
}

impl BitOrAssign for ParseFlags {
    #[inline]
    fn bitor_assign(&mut self, rhs: ParseFlags) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for ParseFlags {
    type Output = ParseFlags;
    #[inline]
    fn bitand(self, rhs: ParseFlags) -> ParseFlags {
        ParseFlags(self.0 & rhs.0)
    }
}
