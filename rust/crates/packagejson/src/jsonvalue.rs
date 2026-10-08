// Ported from tsc/internal/packagejson/jsonvalue.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::io;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer};
use tsc_collections::OrderedMap;
use tsc_json as json;

/// `type JSONValueType int8`
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(i8)]
pub enum JSONValueType {
    #[default]
    NotPresent = 0, // JSONValueTypeNotPresent
    Null,    // JSONValueTypeNull
    String,  // JSONValueTypeString
    Number,  // JSONValueTypeNumber
    Boolean, // JSONValueTypeBoolean
    Array,   // JSONValueTypeArray
    Object,  // JSONValueTypeObject
}

/// `func (t JSONValueType) String() string`
impl fmt::Display for JSONValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JSONValueType::Null => f.write_str("null"),
            JSONValueType::String => f.write_str("string"),
            JSONValueType::Number => f.write_str("number"),
            JSONValueType::Boolean => f.write_str("boolean"),
            JSONValueType::Array => f.write_str("array"),
            JSONValueType::Object => f.write_str("object"),
            // PORT: Go's `default` arm prints `unknown(%d)` for NotPresent and
            // any out-of-range ordinal; a Rust enum cannot be out of range.
            JSONValueType::NotPresent => write!(f, "unknown({})", *self as i8),
        }
    }
}

/// `Value any` of `JSONValue` — PORT: the `any` payload becomes a tagged enum.
/// The element type parameter covers Go's `unmarshalJSONValueFrom[T]`: a
/// `JSONValue` decodes `[]JSONValue`/`*OrderedMap[string, JSONValue]` into it,
/// an `ExportsOrImports` decodes `[]ExportsOrImports`/
/// `*OrderedMap[string, ExportsOrImports]`. `Null` is Go's nil (shared by
/// `NotPresent` and `Null` types).
#[derive(Clone, Debug, Default)]
pub enum JSONValueData<E> {
    #[default]
    Null,
    String(String),
    Number(f64),
    Boolean(bool),
    Array(Vec<E>),
    Object(OrderedMap<String, E>),
}

// PORT: equality compares by variant and value (Go's `Value` is an `any`, so
// `==`/DeepEqual do dynamic-type comparison); OrderedMap has no `==`, so the
// object arm compares keys in order and values by `PartialEq`, mirroring
// `reflect.DeepEqual` on `*OrderedMap` (which dereferences the pointer and
// compares key order and values).
impl<E: PartialEq> PartialEq for JSONValueData<E> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (JSONValueData::Null, JSONValueData::Null) => true,
            (JSONValueData::String(a), JSONValueData::String(b)) => a == b,
            (JSONValueData::Number(a), JSONValueData::Number(b)) => a == b,
            (JSONValueData::Boolean(a), JSONValueData::Boolean(b)) => a == b,
            (JSONValueData::Array(a), JSONValueData::Array(b)) => a == b,
            (JSONValueData::Object(a), JSONValueData::Object(b)) => {
                OrderedMap::equal_func(Some(a), Some(b), |x, y| x == y)
            }
            _ => false,
        }
    }
}

/// `type JSONValue struct`
#[derive(Clone, Debug, Default)]
pub struct JSONValue {
    /// `Type JSONValueType`
    pub type_: JSONValueType,
    /// `Value any`
    pub value: JSONValueData<JSONValue>,
}

// PORT: DeepEqual compares the exported fields (Type and Value — both are
// exported in Go, so `cmpopts.IgnoreUnexported` does not exclude anything).
impl PartialEq for JSONValue {
    fn eq(&self, other: &Self) -> bool {
        self.type_ == other.type_ && self.value == other.value
    }
}

impl JSONValue {
    /// `func (v *JSONValue) IsPresent() bool`
    pub fn is_present(&self) -> bool {
        self.type_ != JSONValueType::NotPresent
    }

    /// `func (v *JSONValue) IsFalsy() bool`
    pub fn is_falsy(&self) -> bool {
        value_is_falsy(self.type_, &self.value)
    }

    /// `func (v JSONValue) AsObject() *collections.OrderedMap[string, JSONValue]`
    ///
    /// PORT: Go returns `*OrderedMap` by asserting on `Value`; a `&` borrow
    /// carries the same liveness (the map is immutable after parse).
    pub fn as_object(&self) -> &OrderedMap<String, JSONValue> {
        if self.type_ != JSONValueType::Object {
            panic!("expected object, got {}", self.type_);
        }
        match &self.value {
            JSONValueData::Object(object) => object,
            // Go: `v.Value.(*OrderedMap[string, JSONValue])` assertion panic.
            _ => panic!("expected object, got {}", self.type_),
        }
    }

    /// `func (v JSONValue) AsArray() []JSONValue`
    pub fn as_array(&self) -> &[JSONValue] {
        if self.type_ != JSONValueType::Array {
            panic!("expected array, got {}", self.type_);
        }
        match &self.value {
            JSONValueData::Array(elements) => elements,
            _ => panic!("expected array, got {}", self.type_),
        }
    }

    /// `func (v JSONValue) AsString() string`
    ///
    /// PORT: returns `&str`; Go copies the string header.
    pub fn as_string(&self) -> &str {
        value_as_string(self.type_, &self.value)
    }
}

// `var _ json.UnmarshalerFrom = (*JSONValue)(nil)`
impl json::UnmarshalerFrom for JSONValue {
    /// `func (v *JSONValue) UnmarshalJSONFrom(dec *json.Decoder) error`
    fn unmarshal_json_from<R: io::Read>(
        &mut self,
        dec: &mut json::Decoder<R>,
    ) -> Result<(), serde_json::Error> {
        let (type_, value) = unmarshal_json_value_from(dec)?;
        self.type_ = type_;
        self.value = value;
        Ok(())
    }
}

// PORT: serde equivalent of `UnmarshalJSONFrom` — the decoder is constructed
// over the member's raw bytes (see `deserialize_unmarshaler_from` in tsc-json).
impl<'de> Deserialize<'de> for JSONValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        json::deserialize_unmarshaler_from(deserializer)
    }
}

/// `func (v *JSONValue) unmarshalJSONValueFrom[T any](dec *json.Decoder) error`
///
/// PORT: a free function returning the decoded `(Type, Value)` pair so
/// `ExportsOrImports` — whose `Value` children are `ExportsOrImports`, not
/// `JSONValue` — shares the implementation, mirroring Go's `[T]` type param.
pub(crate) fn unmarshal_json_value_from<E, R>(
    dec: &mut json::Decoder<R>,
) -> Result<(JSONValueType, JSONValueData<E>), serde_json::Error>
where
    E: DeserializeOwned,
    R: io::Read,
{
    match dec.peek_kind()? {
        b'n' => {
            // json.Null.Kind()
            dec.read_token()?;
            // v.Value = nil
            Ok((JSONValueType::Null, JSONValueData::Null))
        }
        b'"' => {
            let s: String = json::unmarshal_decode(dec, &[])?;
            Ok((JSONValueType::String, JSONValueData::String(s)))
        }
        b'[' => {
            dec.read_token()?;
            let mut elements = Vec::new();
            while dec.peek_kind()? != json::END_ARRAY.kind() {
                let element: E = json::unmarshal_decode(dec, &[])?;
                elements.push(element);
            }
            dec.read_token()?;
            Ok((JSONValueType::Array, JSONValueData::Array(elements)))
        }
        b'{' => {
            let object: OrderedMap<String, E> = json::unmarshal_decode(dec, &[])?;
            Ok((JSONValueType::Object, JSONValueData::Object(object)))
        }
        b't' | b'f' => {
            // json.True.Kind(), json.False.Kind()
            let b: bool = json::unmarshal_decode(dec, &[])?;
            Ok((JSONValueType::Boolean, JSONValueData::Boolean(b)))
        }
        _ => {
            let n: f64 = json::unmarshal_decode(dec, &[])?;
            Ok((JSONValueType::Number, JSONValueData::Number(n)))
        }
    }
}

/// The `IsFalsy` body, shared with `ExportsOrImports` (Go promotes it from the
/// embedded `JSONValue`; the two payload types differ in element type).
pub(crate) fn value_is_falsy<E>(type_: JSONValueType, value: &JSONValueData<E>) -> bool {
    match type_ {
        JSONValueType::NotPresent | JSONValueType::Null => true,
        JSONValueType::String => {
            // `v.Value == ""` — false (not a panic) if the payload is not a
            // string; Type and Value move together so it always is.
            matches!(value, JSONValueData::String(s) if s.is_empty())
        }
        // PORT: Go `v.Value == 0` compares an `any` holding a float64 against
        // the untyped constant 0 (type int) — different dynamic types, so the
        // comparison is always false.
        JSONValueType::Number => false,
        JSONValueType::Boolean => {
            // `!v.Value.(bool)` — a Go type assertion.
            let JSONValueData::Boolean(b) = value else {
                panic!("expected boolean, got {type_}")
            };
            !*b
        }
        _ => false,
    }
}

/// The `AsString` body, shared with `ExportsOrImports` (Go promotes it).
pub(crate) fn value_as_string<E>(type_: JSONValueType, value: &JSONValueData<E>) -> &str {
    if type_ != JSONValueType::String {
        panic!("expected string, got {type_}");
    }
    match value {
        JSONValueData::String(s) => s,
        // Go: `v.Value.(string)` assertion panic.
        _ => panic!("expected string, got {type_}"),
    }
}
