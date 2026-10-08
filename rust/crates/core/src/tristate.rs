// Ported from tsc/internal/core/tristate.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
//go:generate npx hereby generate:tristate

// Tristate

use serde::de::{self, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u8)]
pub enum Tristate {
    #[default]
    Unknown = 0,
    False = 1,
    True = 2,
}

// Aliases matching the Go package-level constant names.
pub const TS_UNKNOWN: Tristate = Tristate::Unknown;
pub const TS_FALSE: Tristate = Tristate::False;
pub const TS_TRUE: Tristate = Tristate::True;

impl Tristate {
    pub fn is_true(&self) -> bool {
        *self == TS_TRUE
    }

    pub fn is_true_or_unknown(&self) -> bool {
        *self == TS_TRUE || *self == TS_UNKNOWN
    }

    pub fn is_false(&self) -> bool {
        *self == TS_FALSE
    }

    pub fn is_false_or_unknown(&self) -> bool {
        *self == TS_FALSE || *self == TS_UNKNOWN
    }

    pub fn is_unknown(&self) -> bool {
        *self == TS_UNKNOWN
    }

    pub fn default_if_unknown(&self, value: Tristate) -> Tristate {
        if *self == TS_UNKNOWN {
            return value;
        }
        *self
    }
}

// PORT: Go's `UnmarshalJSON` maps "true"→TSTrue, "false"→TSFalse and
// *everything else* (null, numbers, strings, ...) to TSUnknown without
// erroring. serde's deserialize_any + catch-all visitor reproduces that.
impl<'de> Deserialize<'de> for Tristate {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct TristateVisitor;

        impl<'de> Visitor<'de> for TristateVisitor {
            type Value = Tristate;

            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a JSON boolean")
            }

            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Self::Value, E> {
                Ok(bool_to_tristate(v))
            }

            // `null` and any non-boolean value decode to TSUnknown.
            fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
                Ok(TS_UNKNOWN)
            }

            fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
                Ok(TS_UNKNOWN)
            }

            fn visit_some<D: Deserializer<'de>>(
                self,
                deserializer: D,
            ) -> Result<Self::Value, D::Error> {
                Tristate::deserialize(deserializer)
            }

            fn visit_i64<E: de::Error>(self, _v: i64) -> Result<Self::Value, E> {
                Ok(TS_UNKNOWN)
            }

            fn visit_u64<E: de::Error>(self, _v: u64) -> Result<Self::Value, E> {
                Ok(TS_UNKNOWN)
            }

            fn visit_f64<E: de::Error>(self, _v: f64) -> Result<Self::Value, E> {
                Ok(TS_UNKNOWN)
            }

            fn visit_str<E: de::Error>(self, _v: &str) -> Result<Self::Value, E> {
                Ok(TS_UNKNOWN)
            }

            fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                while seq.next_element::<de::IgnoredAny>()?.is_some() {}
                Ok(TS_UNKNOWN)
            }

            fn visit_map<A: de::MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                while map
                    .next_entry::<de::IgnoredAny, de::IgnoredAny>()?
                    .is_some()
                {}
                Ok(TS_UNKNOWN)
            }
        }

        deserializer.deserialize_any(TristateVisitor)
    }
}

// PORT: Go's `MarshalJSON` emits `true`/`false`/`null`.
impl Serialize for Tristate {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match *self {
            TS_TRUE => serializer.serialize_bool(true),
            TS_FALSE => serializer.serialize_bool(false),
            _ => serializer.serialize_unit(),
        }
    }
}

pub fn bool_to_tristate(b: bool) -> Tristate {
    if b { TS_TRUE } else { TS_FALSE }
}
