// Ported from tsc/internal/packagejson/expected.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use rustc_hash::FxHashMap;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer};
use serde_json::value::RawValue;
use tsc_collections::OrderedMap;
use tsc_json as json;

/// `type Expected[T any] struct`
///
/// Expected is a field with an expected type. Its `IsValid` method returns
/// false if the field is not present or if its type does not match the
/// expected type.
///
/// PORT: `actualJSONType`/`Null`/`Valid`/`Value` keep Go's field order;
/// `null`/`valid`/`value` are exported like their Go counterparts.
#[derive(Clone, Debug, Default)]
pub struct Expected<T> {
    actual_json_type: &'static str,
    pub null: bool,
    pub valid: bool,
    pub value: T,
}

// PORT: the Go tests compare `Expected` with `cmpopts.IgnoreUnexported`, which
// excludes `actualJSONType`; equality compares the exported fields only.
impl<T: PartialEq> PartialEq for Expected<T> {
    fn eq(&self, other: &Self) -> bool {
        self.null == other.null && self.valid == other.valid && self.value == other.value
    }
}

/// The JSON-type name `ExpectedJSONType` reports for `T` (Go:
/// `reflect.TypeFor[T]().Kind()` in a switch).
///
/// PORT: Rust has no reflection; field types declare their expected JSON type
/// name through this trait. `unknown` is Go's `default` arm — Go kinds that
/// map there include `reflect.Struct`, `reflect.Interface`, `reflect.Func`,
/// and `reflect.Ptr`.
pub trait ExpectedJSONType {
    fn expected_json_type() -> &'static str;
}

// reflect.String
impl ExpectedJSONType for String {
    fn expected_json_type() -> &'static str {
        "string"
    }
}

// reflect.Bool
impl ExpectedJSONType for bool {
    fn expected_json_type() -> &'static str {
        "boolean"
    }
}

// reflect.Slice, reflect.Array
impl<E> ExpectedJSONType for Vec<E> {
    fn expected_json_type() -> &'static str {
        "array"
    }
}

// reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
// reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64
macro_rules! impl_expected_json_type_number {
    ($($t:ty),*) => {
        $(impl ExpectedJSONType for $t {
            fn expected_json_type() -> &'static str {
                "number"
            }
        })*
    };
}
impl_expected_json_type_number!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);

impl<T> Expected<T> {
    /// `func (e *Expected[T]) UnmarshalJSON(data []byte) error`
    ///
    /// PORT: returns `()` — the Go implementation never produces a non-nil
    /// error. On a failed value decode Go may leave `e.Value` partially
    /// populated by the unmarshaler; here `e.value` keeps its previous (or
    /// default) contents, and `e.valid` is likewise left untouched on
    /// failure — matching Go's `err == nil` gating exactly.
    pub fn unmarshal_json(&mut self, data: &[u8])
    where
        T: DeserializeOwned + Default,
    {
        // Check for null explicitly because "null" unmarshals into anything without error.
        if data == b"null" {
            *self = Expected {
                null: true,
                actual_json_type: "null",
                ..Expected::default()
            };
            return;
        }

        if let Ok(value) = json::unmarshal::<T>(data, &[]) {
            self.value = value;
            self.valid = true;
        }

        // !!!!! NEVER DERIVE THIS LIST FROM `ExpectedJSONType` OR SWITCH ON
        // !!!!! `reflect.TypeFor[T]().Kind()`. THAT IS THE EXPECTED TYPE; THIS
        // !!!!! IS THE ACTUAL TYPE.
        self.actual_json_type = match data[0] {
            b'"' => "string",
            b't' | b'f' => "boolean",
            b'[' => "array",
            b'{' => "object",
            _ => "number",
        };
    }

    /// `func (e *Expected[T]) IsPresent() bool`
    pub fn is_present(&self) -> bool {
        !self.actual_json_type.is_empty()
    }

    /// `func (e *Expected[T]) GetValue() (value T, ok bool)`
    ///
    /// PORT: `None` is `!ok`. Go returns `e.Value` even when invalid, but the
    /// value is only meaningfully populated on success (see `unmarshal_json`),
    /// so `None` stands in for the zero/partial value.
    pub fn get_value(&self) -> Option<&T> {
        self.valid.then_some(&self.value)
    }

    /// `func (e *Expected[T]) IsValid() bool`
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    /// `func (e *Expected[T]) ActualJSONType() string`
    pub fn actual_json_type(&self) -> &'static str {
        self.actual_json_type
    }
}

impl<T: ExpectedJSONType> Expected<T> {
    /// `func (e *Expected[T]) ExpectedJSONType() string`
    pub fn expected_json_type(&self) -> &'static str {
        T::expected_json_type()
    }
}

// PORT: serde bridge for `UnmarshalJSON` — the serde equivalent of encoding
// raw member bytes to the field. `&RawValue` captures the member value's
// bytes, which `unmarshal_json` then decodes (suppressing type-mismatch
// errors by design).
impl<'de, T> Deserialize<'de> for Expected<T>
where
    T: DeserializeOwned + Default,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let raw = <&RawValue>::deserialize(deserializer)?;
        let mut e = Expected::default();
        e.unmarshal_json(raw.get().as_bytes());
        Ok(e)
    }
}

/// `func ExpectedOf[T any](value T) Expected[T]` — create an expected field
/// that is present, non-null, valid, and has the given value.
///
/// PORT: used by package.json consumers (and tests) constructing an expected
/// `Fields` to compare against.
pub fn expected_of<T: ExpectedJSONType>(value: T) -> Expected<T> {
    Expected {
        actual_json_type: T::expected_json_type(),
        null: false,
        valid: true,
        value,
    }
}

// ExpectedJSONType impls for the collection types used as `Expected[...]`
// targets — Go derives these from `reflect.Kind`.

// reflect.Map
impl<V> ExpectedJSONType for FxHashMap<String, V> {
    fn expected_json_type() -> &'static str {
        "object"
    }
}

// reflect.Map
impl<K, V> ExpectedJSONType for OrderedMap<K, V> {
    fn expected_json_type() -> &'static str {
        "object"
    }
}

// reflect.Interface — `Expected[any]` unmarshals into the parsed-any slot.
impl ExpectedJSONType for serde_json::Value {
    fn expected_json_type() -> &'static str {
        "unknown"
    }
}
