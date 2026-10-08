// Ported from tsc/internal/tsoptions (the `any`/`CompilerOptionsValue` carrier) @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The Go code passes raw option/config values around as `any`. The concrete
// population is small and closed: nil, bool, int, float64, string, []any,
// []string, *collections.OrderedMap[string, any], map[string]any (from the
// generic JSON unmarshal path inside RawCompilerOptions), struct{}{} (the
// convertToJson "no expression" sentinel), core.Tristate, the typed i32
// option enums (stored in enum maps; see PORT below), rooted path types,
// *OrderedMap[string, []string], and []core.PluginImport (the last two only
// ever placed into serialization output maps).
//
// PORT: Go distinguishes each int32 enum type (core.ScriptTarget,
// core.ModuleKind, ...) in `any` via its concrete type; tsoptions only ever
// (a) stores enum-map values, (b) converts them through floatOrInt32ToFlag,
// and (c) stringifies them via serializeCompilerOptionEnum — which this port
// implements as a reverse lookup over the option's own enum map (the
// generated Go switch is exactly that map's value→key table). That erases
// the need for per-enum-type variants, so they all collapse to `Int`.

use serde::Serialize;
use serde::ser::SerializeMap as _;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::PluginImport;
use tsc_core::tristate::Tristate;
use tsc_tspath::{RootedDirectoryPath, RootedFilePath, RootedPath, SourceMapLocation};

/// `type CompilerOptionsValue any` — plus the handful of non-compiler-option
/// values that flow through the same `any` channels.
#[derive(Clone, Debug, Default)]
pub enum Value {
    /// Go `nil` interface value.
    #[default]
    Null,
    /// Go `struct{}{}` — returned by convertToJson when there is no root
    /// expression but returnValue was requested. Non-nil, not a map.
    EmptyStruct,
    Bool(bool),
    /// Go `int` and the `~int32` option enum types (see PORT note above).
    Int(i64),
    /// Go `float64` (the only numeric type JSON conversion produces).
    Float(f64),
    Str(String),
    /// Go `[]any`.
    List(Vec<Value>),
    /// Go `[]string` — deliberately distinct from `List`: `value.([]any)`
    /// assertions fail on a `[]string` in Go (e.g. `options.Set(name,
    /// []string{})` for an empty `--list` flag is invisible to
    /// ParseStringArray).
    StringList(Vec<String>),
    /// Go `*collections.OrderedMap[string, any]`.
    Map(OrderedMap<String, Value>),
    /// Go `map[string]any` — produced by `json.UnmarshalDecode(&value)` for
    /// non-"paths" object members of RawCompilerOptions. Fails `*OrderedMap`
    /// assertions in Go (e.g. "plugins" elements decode to this and are
    /// dropped by the `plugin.(map)` check — preserved quirk).
    GoMap(OrderedMap<String, Value>),
    Tristate(Tristate),
    FilePath(RootedFilePath),
    DirPath(RootedDirectoryPath),
    RootedPath(RootedPath),
    SourceMapLocation(SourceMapLocation),
    FilePathList(Vec<RootedFilePath>),
    DirPathList(Vec<RootedDirectoryPath>),
    /// Go `*collections.OrderedMap[string, []string]` (CompilerOptions.Paths).
    /// Inner `Option` mirrors Go's nil-able `[]string`.
    StringListMap(OrderedMap<String, Option<Vec<String>>>),
    /// Go `[]core.PluginImport` (CompilerOptions.Plugins).
    Plugins(Vec<PluginImport>),
}

impl Value {
    /// `&collections.OrderedMap[string, any]{}` — an empty ordered map.
    pub fn empty_map() -> Value {
        Value::Map(OrderedMap::new())
    }

    /// `value == nil` on the Go `any` (or a nil `*OrderedMap` — the port never
    /// stores a nil map pointer, so `Null` covers both).
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    /// `reflect.TypeOf(value).Kind() == reflect.Slice`.
    pub fn is_slice(&self) -> bool {
        matches!(
            self,
            Value::List(_)
                | Value::StringList(_)
                | Value::FilePathList(_)
                | Value::DirPathList(_)
                | Value::Plugins(_)
        )
    }

    /// `value.(string)`.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    /// `value.(bool)`.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// `value.([]any)`.
    pub fn as_list(&self) -> Option<&Vec<Value>> {
        match self {
            Value::List(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_list_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self {
            Value::List(v) => Some(v),
            _ => None,
        }
    }

    /// `value.([]string)`.
    pub fn as_string_list(&self) -> Option<&Vec<String>> {
        match self {
            Value::StringList(v) => Some(v),
            _ => None,
        }
    }

    /// `value.(*collections.OrderedMap[string, any])`.
    pub fn as_map(&self) -> Option<&OrderedMap<String, Value>> {
        match self {
            Value::Map(m) => Some(m),
            _ => None,
        }
    }

    pub fn as_map_mut(&mut self) -> Option<&mut OrderedMap<String, Value>> {
        match self {
            Value::Map(m) => Some(m),
            _ => None,
        }
    }

    /// `value.(map[string]any)` — also matches `GoMap` (a Go `map[string]any`
    /// assertion accepts map types, not `*OrderedMap`).
    pub fn as_go_map(&self) -> Option<&OrderedMap<String, Value>> {
        match self {
            Value::GoMap(m) => Some(m),
            _ => None,
        }
    }

    /// `reflect.TypeOf(value).Kind() == reflect.String`.
    pub fn is_string_kind(&self) -> bool {
        matches!(self, Value::Str(_))
    }

    /// `reflect.TypeOf(value).Kind() == reflect.Bool`.
    pub fn is_bool_kind(&self) -> bool {
        matches!(self, Value::Bool(_))
    }

    /// `reflect.TypeOf(value).Kind() == reflect.Float64`.
    /// PORT: `Int` does NOT match — Go `int` is a distinct Kind.
    pub fn is_float64_kind(&self) -> bool {
        matches!(self, Value::Float(_))
    }

    /// `reflect.TypeOf(value) == orderedMapType` (`*OrderedMap[string,any]`).
    pub fn is_ordered_map(&self) -> bool {
        matches!(self, Value::Map(_))
    }

    /// The `float64` coercion used by `floatOrInt32ToFlag`'s second arm.
    /// Go: `value.(float64)` panics for non-float; callers route Int through
    /// the `value.(T)` arm. Both arms land here.
    pub fn as_i32_flag(&self) -> i32 {
        match self {
            Value::Int(n) => *n as i32,
            Value::Float(f) => *f as i32,
            _ => panic!("interface conversion: Value is not a number"),
        }
    }
}

// Go `==` on `any` compares (dynamic type, value); mismatched types are
// unequal and uncomparable same-type pairs (maps/slices) would panic —
// callers never hit that case, so we return false instead of panicking
// except for the pointer-comparable cases Go would resolve by identity.
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Null, Value::Null) => true,
            // Go: `struct{}{} == struct{}{}` is true.
            (Value::EmptyStruct, Value::EmptyStruct) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Tristate(a), Value::Tristate(b)) => a == b,
            (Value::FilePath(a), Value::FilePath(b)) => a == b,
            (Value::DirPath(a), Value::DirPath(b)) => a == b,
            (Value::RootedPath(a), Value::RootedPath(b)) => a == b,
            (Value::SourceMapLocation(a), Value::SourceMapLocation(b)) => a == b,
            // Go `*OrderedMap == *OrderedMap` is a pointer comparison.
            (Value::Map(a), Value::Map(b)) => std::ptr::eq(a, b),
            _ => false,
        }
    }
}

/// `MarshalJSON` for the `any` population — used when a `Raw`/`TSConfig`
// compilerOptions map or a build-info options map is serialized.
impl Serialize for Value {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Value::Null => serializer.serialize_unit(),
            // Go `json.Marshal(struct{}{})` produces `{}`.
            Value::EmptyStruct => serializer.serialize_map(Some(0)).and_then(|m| m.end()),
            Value::Bool(b) => serializer.serialize_bool(*b),
            Value::Int(n) => serializer.serialize_i64(*n),
            Value::Float(f) => serializer.serialize_f64(*f),
            Value::Str(s) => serializer.serialize_str(s),
            Value::List(v) => v.serialize(serializer),
            Value::StringList(v) => v.serialize(serializer),
            Value::Map(m) | Value::GoMap(m) => m.serialize(serializer),
            Value::Tristate(t) => t.serialize(serializer),
            Value::FilePath(p) => serializer.serialize_str(p.as_string()),
            Value::DirPath(p) => serializer.serialize_str(p.as_string()),
            Value::RootedPath(p) => serializer.serialize_str(p.as_string()),
            Value::SourceMapLocation(p) => serializer.serialize_str(p.as_string()),
            Value::FilePathList(v) => serializer.collect_seq(v.iter().map(|p| p.as_string())),
            Value::DirPathList(v) => serializer.collect_seq(v.iter().map(|p| p.as_string())),
            Value::StringListMap(m) => m.serialize(serializer),
            Value::Plugins(v) => v.serialize(serializer),
        }
    }
}

/// `*collections.OrderedMap[string, any]` as a function parameter — Go passes
/// a nilable pointer.
pub type ValueMap = OrderedMap<String, Value>;

/// Shared ownership for `Value` tables behind `LazyLock`s.

impl From<bool> for Value {
    fn from(v: bool) -> Value {
        Value::Bool(v)
    }
}

impl From<String> for Value {
    fn from(v: String) -> Value {
        Value::Str(v)
    }
}

impl From<&str> for Value {
    fn from(v: &str) -> Value {
        Value::Str(v.to_string())
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Value {
        Value::Int(v)
    }
}

impl From<Vec<Value>> for Value {
    fn from(v: Vec<Value>) -> Value {
        Value::List(v)
    }
}

impl From<Vec<String>> for Value {
    fn from(v: Vec<String>) -> Value {
        Value::StringList(v)
    }
}

impl From<OrderedMap<String, Value>> for Value {
    fn from(v: OrderedMap<String, Value>) -> Value {
        Value::Map(v)
    }
}

/// Go `fmt` `%v` formatting for diagnostic args: only the scalar variants
/// ever appear as diagnostic args (strings, ints, floats, bools, tristates,
/// path strings). Composite variants format like Go's `%v` too where cheap
/// (slices as `[a b c]`); maps fall back to Go's `map[...]` debug shape is
/// avoided by callers.
impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Null => f.write_str("<nil>"),
            Value::EmptyStruct => f.write_str("{}"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(n) => write!(f, "{}", n),
            // PORT: Go %v on float64 uses %g; Rust {} prints the shortest
            // round-trip form, which agrees for the option values used.
            Value::Float(x) => write!(f, "{}", x),
            Value::Str(s) => f.write_str(s),
            Value::Tristate(t) => write!(f, "{}", *t as i32),
            Value::FilePath(p) => f.write_str(p.as_string()),
            Value::DirPath(p) => f.write_str(p.as_string()),
            Value::RootedPath(p) => f.write_str(p.as_string()),
            Value::SourceMapLocation(p) => f.write_str(p.as_string()),
            Value::List(v) => {
                let parts: Vec<String> = v.iter().map(ToString::to_string).collect();
                write!(f, "[{}]", parts.join(" "))
            }
            Value::StringList(v) => write!(f, "[{}]", v.join(" ")),
            Value::FilePathList(v) => {
                let parts: Vec<&str> = v.iter().map(|p| p.as_string()).collect();
                write!(f, "[{}]", parts.join(" "))
            }
            Value::DirPathList(v) => {
                let parts: Vec<&str> = v.iter().map(|p| p.as_string()).collect();
                write!(f, "[{}]", parts.join(" "))
            }
            Value::Map(m) | Value::GoMap(m) => {
                let parts: Vec<String> = m.entries().map(|(k, v)| format!("{}:{}", k, v)).collect();
                write!(f, "map[{}]", parts.join(" "))
            }
            Value::StringListMap(m) => {
                let parts: Vec<String> = m
                    .entries()
                    .map(|(k, v)| format!("{}:[{}]", k, v.clone().unwrap_or_default().join(" ")))
                    .collect();
                write!(f, "map[{}]", parts.join(" "))
            }
            Value::Plugins(_) => f.write_str("[]"),
        }
    }
}

/// `json.Marshal`-equivalent — converts a `Value` to `tsc_json::Value`
/// (`Box<RawValue>`), used where Go stores marshaled JSON bytes
/// (`Mapper.Options`).
pub fn value_to_json(value: &Value) -> tsc_json::Value {
    let text = serde_json::to_string(value).expect("Value serializes to JSON");
    serde_json::value::RawValue::from_string(text).expect("serialized JSON is valid")
}

/// Generic `json.UnmarshalDecode(&value)` — produces the Go `any` shapes the
/// tsconfig decoder produces: `nil`, `bool`, `float64`, `string`, `[]any`,
/// `*OrderedMap[string,any]` (the internal decoder returns ordered maps).
/// Numbers always decode to `Value::Float` (Go's `float64`).
///
/// Deserializing into `OrderedMap` preserves the JSON document order at every
/// level, unlike `serde_json::Value` which uses a sorted `BTreeMap` unless the
/// `preserve_order` feature is enabled. The `map[string]any` quirk for
/// RawCompilerOptions members is applied afterwards via `Value::into_go_map`.
impl<'de> serde::Deserialize<'de> for Value {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct ValueVisitor;

        impl<'de> serde::de::Visitor<'de> for ValueVisitor {
            type Value = Value;

            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("any JSON value")
            }

            fn visit_bool<E>(self, v: bool) -> Result<Value, E> {
                Ok(Value::Bool(v))
            }

            fn visit_i64<E>(self, v: i64) -> Result<Value, E> {
                Ok(Value::Float(v as f64))
            }

            fn visit_u64<E>(self, v: u64) -> Result<Value, E> {
                Ok(Value::Float(v as f64))
            }

            fn visit_f64<E>(self, v: f64) -> Result<Value, E> {
                Ok(Value::Float(v))
            }

            fn visit_str<E>(self, v: &str) -> Result<Value, E> {
                Ok(Value::Str(v.to_string()))
            }

            fn visit_none<E>(self) -> Result<Value, E> {
                Ok(Value::Null)
            }

            fn visit_some<D: serde::Deserializer<'de>>(
                self,
                deserializer: D,
            ) -> Result<Value, D::Error> {
                <Value as serde::Deserialize>::deserialize(deserializer)
            }

            fn visit_unit<E>(self) -> Result<Value, E> {
                Ok(Value::Null)
            }

            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<Value, A::Error> {
                let mut list = Vec::with_capacity(seq.size_hint().unwrap_or(0));
                while let Some(element) = seq.next_element()? {
                    list.push(element);
                }
                Ok(Value::List(list))
            }

            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                mut access: A,
            ) -> Result<Value, A::Error> {
                let mut map = OrderedMap::with_size_hint(access.size_hint().unwrap_or(0));
                while let Some((key, value)) = access.next_entry::<String, Value>()? {
                    map.set(key, value);
                }
                Ok(Value::Map(map))
            }
        }

        deserializer.deserialize_any(ValueVisitor)
    }
}

/// Recursively converts `Value::Map` into `Value::GoMap` — Go `map[string]any`
/// decoded members contain `map[string]any` nested values, whereas the tsconfig
/// decoder's `*OrderedMap` targets produce ordered maps.
pub fn value_into_go_map(value: Value) -> Value {
    match value {
        Value::Map(map) => {
            let mut result = OrderedMap::with_size_hint(map.size());
            for (k, v) in map.entries() {
                result.set(k.clone(), value_into_go_map(v.clone()));
            }
            Value::GoMap(result)
        }
        Value::List(list) => Value::List(list.into_iter().map(value_into_go_map).collect()),
        other => other,
    }
}
