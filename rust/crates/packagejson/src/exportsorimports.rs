// Ported from tsc/internal/packagejson/exportsorimports.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;

use serde::{Deserialize, Deserializer};
use tsc_collections::OrderedMap;
use tsc_json as json;

use crate::jsonvalue::{
    JSONValueData, JSONValueType, unmarshal_json_value_from, value_as_string, value_is_falsy,
};

/// `type objectKind int8`
///
/// PORT: unexported Go type → private enum.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(i8)]
enum ObjectKind {
    #[default]
    Unknown = 0, // objectKindUnknown
    Subpaths,   // objectKindSubpaths
    Conditions, // objectKindConditions
    Imports,    // objectKindImports
    Invalid,    // objectKindInvalid
}

/// `type ExportsOrImports struct`
///
/// PORT: Go embeds `JSONValue`; its `Type`/`Value` fields are inlined here so
/// `e.Type`/`e.Value` → `e.type_`/`e.value` and the promoted methods
/// `IsPresent`/`IsFalsy`/`AsString` are re-declared below. `value`'s object
/// and array children are `ExportsOrImports` — Go achieves this via the
/// `[T]` parameter of `unmarshalJSONValueFrom`.
#[derive(Clone, Debug, Default)]
pub struct ExportsOrImports {
    /// `Type JSONValueType`
    pub type_: JSONValueType,
    /// `Value any`
    pub value: JSONValueData<ExportsOrImports>,
    object_kind: ObjectKind,
}

// PORT: DeepEqual with `cmpopts.IgnoreUnexported` compares only the fields
// promoted from the embedded JSONValue (Type and Value); `object_kind` is
// unexported and excluded.
impl PartialEq for ExportsOrImports {
    fn eq(&self, other: &Self) -> bool {
        self.type_ == other.type_ && self.value == other.value
    }
}

// `var _ json.UnmarshalerFrom = (*ExportsOrImports)(nil)`
impl json::UnmarshalerFrom for ExportsOrImports {
    /// `func (e *ExportsOrImports) UnmarshalJSONFrom(dec *json.Decoder) error`
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

// PORT: serde bridge — see `JSONValue`'s `Deserialize` impl.
impl<'de> Deserialize<'de> for ExportsOrImports {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        json::deserialize_unmarshaler_from(deserializer)
    }
}

impl ExportsOrImports {
    /// `func (e ExportsOrImports) AsObject() *collections.OrderedMap[string, ExportsOrImports]`
    pub fn as_object(&self) -> &OrderedMap<String, ExportsOrImports> {
        if self.type_ != JSONValueType::Object {
            panic!("expected object");
        }
        match &self.value {
            JSONValueData::Object(object) => object,
            _ => panic!("expected object"),
        }
    }

    /// `func (e ExportsOrImports) AsArray() []ExportsOrImports`
    pub fn as_array(&self) -> &[ExportsOrImports] {
        if self.type_ != JSONValueType::Array {
            panic!("expected array");
        }
        match &self.value {
            JSONValueData::Array(elements) => elements,
            _ => panic!("expected array"),
        }
    }

    /// `func (e ExportsOrImports) IsSubpaths() bool`
    pub fn is_subpaths(&self) -> bool {
        self.init_object_kind() == ObjectKind::Subpaths
    }

    /// `func (e ExportsOrImports) IsImports() bool`
    pub fn is_imports(&self) -> bool {
        self.init_object_kind() == ObjectKind::Imports
    }

    /// `func (e ExportsOrImports) IsConditions() bool`
    pub fn is_conditions(&self) -> bool {
        self.init_object_kind() == ObjectKind::Conditions
    }

    /// `func (e *ExportsOrImports) initObjectKind()`
    ///
    /// PORT: Go's `IsX` methods take value receivers, so `initObjectKind`
    /// writes to a per-call copy — the stored `objectKind` never leaves
    /// `objectKindUnknown` and every call recomputes the classification.
    /// Returning the computed kind preserves that observable behavior and
    /// keeps `ExportsOrImports` `Sync` (shared in the package.json cache).
    fn init_object_kind(&self) -> ObjectKind {
        if self.object_kind == ObjectKind::Unknown && self.type_ == JSONValueType::Object {
            let object = self.as_object();
            if object.size() > 0 {
                let mut seen_dot = false;
                let mut seen_hash = false;
                let mut seen_other = false;
                for k in object.keys() {
                    if !k.is_empty() {
                        seen_dot = seen_dot || k.as_bytes()[0] == b'.';
                        seen_hash = seen_hash || k.as_bytes()[0] == b'#';
                        seen_other =
                            seen_other || (k.as_bytes()[0] != b'.' && k.as_bytes()[0] != b'#');
                        if seen_other && (seen_dot || seen_hash) {
                            return ObjectKind::Invalid;
                        }
                    }
                }
                if seen_dot {
                    return ObjectKind::Subpaths;
                }
                if seen_hash {
                    return ObjectKind::Imports;
                }
            }
            return ObjectKind::Conditions;
        }
        self.object_kind
    }

    // PORT: methods promoted from the embedded `JSONValue` in Go.

    /// `func (v *JSONValue) IsPresent() bool`
    pub fn is_present(&self) -> bool {
        self.type_ != JSONValueType::NotPresent
    }

    /// `func (v *JSONValue) IsFalsy() bool`
    pub fn is_falsy(&self) -> bool {
        value_is_falsy(self.type_, &self.value)
    }

    /// `func (v JSONValue) AsString() string`
    pub fn as_string(&self) -> &str {
        value_as_string(self.type_, &self.value)
    }
}
