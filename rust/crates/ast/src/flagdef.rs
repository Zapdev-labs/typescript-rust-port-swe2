// Shared definition macro for the bitmask flag newtypes ported from
// tsc/internal/ast/{nodeflags,modifierflags,tokenflags,symbolflags,checkflags,functionflags,flow}.go.

/// Defines a bitmask newtype over an unsigned integer, mirroring the Go
/// `type XFlags uint32` declarations. Provides the bit operators used by the
/// Go sources (`|`, `&`, `&^`, `^`) plus `contains`/`insert`/`remove` helpers.
macro_rules! flag_type {
    (
        $(#[$meta:meta])*
        pub struct $name:ident(pub $repr:ty);
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        pub struct $name(pub $repr);

        impl $name {
            /// The empty flag set, mirroring the Go `XFlagsNone` constant.
            pub const NONE: Self = Self(0);

            /// `self & flags != 0`
            #[inline]
            pub const fn intersects(self, flags: Self) -> bool {
                self.0 & flags.0 != 0
            }

            /// `self & flags == flags`
            #[inline]
            pub const fn contains(self, flags: Self) -> bool {
                self.0 & flags.0 == flags.0
            }

            /// `self | flags`
            #[inline]
            pub const fn with(self, flags: Self) -> Self {
                Self(self.0 | flags.0)
            }

            /// `self & !flags`
            #[inline]
            pub const fn without(self, flags: Self) -> Self {
                Self(self.0 & !flags.0)
            }

            /// `self |= flags`
            #[inline]
            pub fn insert(&mut self, flags: Self) {
                self.0 |= flags.0;
            }

            /// `self &= !flags`
            #[inline]
            pub fn remove(&mut self, flags: Self) {
                self.0 &= !flags.0;
            }

            /// `self == 0`
            #[inline]
            pub const fn is_empty(self) -> bool {
                self.0 == 0
            }

            /// The raw bit representation.
            #[inline]
            pub const fn bits(self) -> $repr {
                self.0
            }
        }

        impl ::core::ops::BitOr for $name {
            type Output = Self;
            #[inline]
            fn bitor(self, rhs: Self) -> Self {
                Self(self.0 | rhs.0)
            }
        }

        impl ::core::ops::BitOrAssign for $name {
            #[inline]
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }

        impl ::core::ops::BitAnd for $name {
            type Output = Self;
            #[inline]
            fn bitand(self, rhs: Self) -> Self {
                Self(self.0 & rhs.0)
            }
        }

        impl ::core::ops::BitAndAssign for $name {
            #[inline]
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0;
            }
        }

        impl ::core::ops::Not for $name {
            type Output = Self;
            #[inline]
            fn not(self) -> Self {
                Self(!self.0)
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                write!(f, concat!(stringify!($name), "({:#x})"), self.0)
            }
        }
    };
}

pub(crate) use flag_type;
