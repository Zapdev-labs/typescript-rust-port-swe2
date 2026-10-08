// Ported from tsc/internal/packagejson/packagejson.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::ops::Deref;

use rustc_hash::FxHashMap;
use serde::de::{DeserializeOwned, Error as _, IgnoredAny, MapAccess, Visitor};
use serde::{Deserialize, Deserializer};
use serde_json::value::RawValue;
use tsc_collections::Set;
use tsc_json as json;

use crate::expected::{Expected, ExpectedJSONType};
use crate::exportsorimports::ExportsOrImports;
use crate::jsonvalue::JSONValue;

// PORT: serde glue, not present in the Go file. Go's
// `json.Unmarshal(data, &parsed, json.AllowDuplicateNames(true))` hands each
// member's raw bytes to the field's `UnmarshalJSON`/`UnmarshalJSONFrom`; the
// serde equivalents below capture `&RawValue` members and forward them
// through the `UnmarshalMember` trait. Reading every member through the
// visitor (and assigning last-wins) is what `AllowDuplicateNames` permits —
// see the note in tsc-json: serde never rejects duplicate member names.
pub(crate) trait UnmarshalMember {
    /// Decode one raw member value (or `null`) into `self`, mirroring the
    /// field types' `UnmarshalJSON`/`UnmarshalJSONFrom` contracts.
    fn unmarshal_member(&mut self, data: &[u8]) -> Result<(), serde_json::Error>;
}

impl<T> UnmarshalMember for Expected<T>
where
    T: DeserializeOwned + Default,
{
    fn unmarshal_member(&mut self, data: &[u8]) -> Result<(), serde_json::Error> {
        self.unmarshal_json(data);
        Ok(())
    }
}

impl UnmarshalMember for JSONValue {
    fn unmarshal_member(&mut self, data: &[u8]) -> Result<(), serde_json::Error> {
        *self = json::unmarshal(data, &[])?;
        Ok(())
    }
}

impl UnmarshalMember for ExportsOrImports {
    fn unmarshal_member(&mut self, data: &[u8]) -> Result<(), serde_json::Error> {
        *self = json::unmarshal(data, &[])?;
        Ok(())
    }
}

/// Implements `Deserialize` for a package.json-shaped struct: `$key` is the
/// `json:"..."` member name and `$field` the (possibly nested) field path it
/// unmarshals into. `null` documents are a no-op, matching Go's
/// `json.Unmarshal(null)` convention (see `OrderedMap`'s `Deserialize`).
macro_rules! impl_package_json_deserialize {
    ($ty:ty { $($key:literal => $($field:ident).+),* $(,)? }) => {
        impl<'de> Deserialize<'de> for $ty {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                struct FieldsVisitor;

                impl<'de> Visitor<'de> for FieldsVisitor {
                    type Value = $ty;

                    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                        f.write_str("a JSON object")
                    }

                    fn visit_map<A: MapAccess<'de>>(
                        self,
                        mut access: A,
                    ) -> Result<Self::Value, A::Error> {
                        let mut out = <$ty>::default();
                        while let Some(key) = access.next_key::<String>()? {
                            match key.as_str() {
                                $($key => {
                                    let raw = access.next_value::<&RawValue>()?;
                                    out.$($field).+
                                        .unmarshal_member(raw.get().as_bytes())
                                        .map_err(A::Error::custom)?;
                                })*
                                _ => {
                                    access.next_value::<IgnoredAny>()?;
                                }
                            }
                        }
                        Ok(out)
                    }

                    fn visit_unit<E>(self) -> Result<Self::Value, E> {
                        Ok(<$ty>::default())
                    }

                    fn visit_none<E>(self) -> Result<Self::Value, E> {
                        Ok(<$ty>::default())
                    }

                    fn visit_some<D: Deserializer<'de>>(
                        self,
                        deserializer: D,
                    ) -> Result<Self::Value, D::Error> {
                        deserializer.deserialize_map(self)
                    }
                }

                deserializer.deserialize_option(FieldsVisitor)
            }
        }
    };
}

/// `type HeaderFields struct`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct HeaderFields {
    /// `Name Expected[string] `json:"name"``
    pub name: Expected<String>,
    /// `Version Expected[string] `json:"version"``
    pub version: Expected<String>,
    /// `Type Expected[string] `json:"type"``
    pub type_: Expected<String>,
}

impl_package_json_deserialize!(HeaderFields {
    "name" => name,
    "version" => version,
    "type" => type_,
});

/// `type PathFields struct`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PathFields {
    /// `TSConfig Expected[string] `json:"tsconfig"``
    pub ts_config: Expected<String>,
    /// `Main Expected[string] `json:"main"``
    pub main: Expected<String>,
    /// `Types Expected[string] `json:"types"``
    pub types: Expected<String>,
    /// `Typings Expected[string] `json:"typings"``
    pub typings: Expected<String>,
    /// `TypesVersions JSONValue `json:"typesVersions"``
    pub types_versions: JSONValue,
    /// `Imports ExportsOrImports `json:"imports"``
    pub imports: ExportsOrImports,
    /// `Exports ExportsOrImports `json:"exports"``
    pub exports: ExportsOrImports,
}

impl_package_json_deserialize!(PathFields {
    "tsconfig" => ts_config,
    "main" => main,
    "types" => types,
    "typings" => typings,
    "typesVersions" => types_versions,
    "imports" => imports,
    "exports" => exports,
});

/// `type DependencyFields struct`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DependencyFields {
    /// `Dependencies Expected[map[string]string] `json:"dependencies"``
    pub dependencies: Expected<FxHashMap<String, String>>,
    /// `DevDependencies Expected[map[string]string] `json:"devDependencies"``
    pub dev_dependencies: Expected<FxHashMap<String, String>>,
    /// `PeerDependencies Expected[map[string]string] `json:"peerDependencies"``
    pub peer_dependencies: Expected<FxHashMap<String, String>>,
    /// `OptionalDependencies Expected[map[string]string] `json:"optionalDependencies"``
    pub optional_dependencies: Expected<FxHashMap<String, String>>,
}

impl_package_json_deserialize!(DependencyFields {
    "dependencies" => dependencies,
    "devDependencies" => dev_dependencies,
    "peerDependencies" => peer_dependencies,
    "optionalDependencies" => optional_dependencies,
});

impl DependencyFields {
    /// `func (df *DependencyFields) HasDependency(name string) bool`
    pub fn has_dependency(&self, name: &str) -> bool {
        if let Some(deps) = self.dependencies.get_value() {
            if deps.contains_key(name) {
                return true;
            }
        }
        if let Some(deps) = self.dev_dependencies.get_value() {
            if deps.contains_key(name) {
                return true;
            }
        }
        if let Some(deps) = self.peer_dependencies.get_value() {
            if deps.contains_key(name) {
                return true;
            }
        }
        if let Some(deps) = self.optional_dependencies.get_value() {
            if deps.contains_key(name) {
                return true;
            }
        }
        false
    }

    /// `func (df *DependencyFields) RangeDependencies(f func(name, version, dependencyField string) bool)`
    ///
    /// PORT: Go passes `string` copies into `f`; `&str` borrows carry the
    /// same data. Map iteration order is unspecified on both sides (Go maps
    /// are randomized).
    pub fn range_dependencies(&self, mut f: impl FnMut(&str, &str, &str) -> bool) {
        if let Some(deps) = self.dependencies.get_value() {
            for (name, version) in deps {
                if !f(name, version, "dependencies") {
                    return;
                }
            }
        }
        if let Some(deps) = self.dev_dependencies.get_value() {
            for (name, version) in deps {
                if !f(name, version, "devDependencies") {
                    return;
                }
            }
        }
        if let Some(deps) = self.peer_dependencies.get_value() {
            for (name, version) in deps {
                if !f(name, version, "peerDependencies") {
                    return;
                }
            }
        }
        if let Some(deps) = self.optional_dependencies.get_value() {
            for (name, version) in deps {
                if !f(name, version, "optionalDependencies") {
                    return;
                }
            }
        }
    }

    /// `func (df *DependencyFields) GetRuntimeDependencyNames() *collections.Set[string]`
    pub fn get_runtime_dependency_names(&self) -> Set<String> {
        let mut count = 0;
        let deps = self.dependencies.get_value();
        count += deps.map_or(0, |d| d.len());
        let peer_deps = self.peer_dependencies.get_value();
        count += peer_deps.map_or(0, |d| d.len());
        let opt_deps = self.optional_dependencies.get_value();
        count += opt_deps.map_or(0, |d| d.len());

        let mut names = Set::with_size_hint(count);
        if let Some(deps) = deps {
            for name in deps.keys() {
                names.add(name.clone());
            }
        }
        if let Some(deps) = peer_deps {
            for name in deps.keys() {
                names.add(name.clone());
            }
        }
        if let Some(deps) = opt_deps {
            for name in deps.keys() {
                names.add(name.clone());
            }
        }
        names
    }
}

/// `type Fields struct`
///
/// PORT: Go embeds `HeaderFields`, `PathFields`, and `DependencyFields`; every
/// member is a promoted field of `Fields`. The header/path members are
/// flattened here, and `dependency_fields` keeps the `DependencyFields` group
/// (its methods promote through `Deref` exactly as Go's embedding does), so
/// `f.Name`/`f.Exports`/`f.Dependencies`/`f.HasDependency` map to `f.name`/
/// `f.exports`/`f.dependencies`/`f.has_dependency` unchanged.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Fields {
    // HeaderFields
    pub name: Expected<String>,
    pub version: Expected<String>,
    pub type_: Expected<String>,
    // PathFields
    pub ts_config: Expected<String>,
    pub main: Expected<String>,
    pub types: Expected<String>,
    pub typings: Expected<String>,
    pub types_versions: JSONValue,
    pub imports: ExportsOrImports,
    pub exports: ExportsOrImports,
    /// `DependencyFields` (embedded)
    pub dependency_fields: DependencyFields,
    /// `ContentMapper Expected[ContentMapperFields] `json:"-"`` — the content
    /// mapper is only present in "typescript"; private field.
    pub content_mapper: Expected<ContentMapperFields>,
}

impl Deref for Fields {
    type Target = DependencyFields;

    fn deref(&self) -> &DependencyFields {
        &self.dependency_fields
    }
}

// Go's `json.Unmarshal` into `Fields` accepts every promoted member;
// `ContentMapper`'s `json:"-"` tag means the `typescript` member is skipped.
impl_package_json_deserialize!(Fields {
    "name" => name,
    "version" => version,
    "type" => type_,
    "tsconfig" => ts_config,
    "main" => main,
    "types" => types,
    "typings" => typings,
    "typesVersions" => types_versions,
    "imports" => imports,
    "exports" => exports,
    "dependencies" => dependency_fields.dependencies,
    "devDependencies" => dependency_fields.dev_dependencies,
    "peerDependencies" => dependency_fields.peer_dependencies,
    "optionalDependencies" => dependency_fields.optional_dependencies,
});

/// `type ContentMapperFields struct`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ContentMapperFields {
    /// `Exec Expected[[]string] `json:"exec"``
    pub exec: Expected<Vec<String>>,
    /// `CompilerOptions Expected[[]string] `json:"compilerOptions"``
    pub compiler_options: Expected<Vec<String>>,
    /// `DynamicConfig Expected[bool] `json:"dynamicConfig"``
    pub dynamic_config: Expected<bool>,
}

impl_package_json_deserialize!(ContentMapperFields {
    "exec" => exec,
    "compilerOptions" => compiler_options,
    "dynamicConfig" => dynamic_config,
});

// reflect.Struct → "unknown"
impl ExpectedJSONType for ContentMapperFields {
    fn expected_json_type() -> &'static str {
        "unknown"
    }
}

/// `type typeScriptFields struct`
///
/// PORT: unexported in Go → `pub(crate)` (visible to the test module for the
/// `ExpectedJSONType` impl if needed).
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct TypeScriptFields {
    /// `ContentMapper Expected[ContentMapperFields] `json:"contentMapper"``
    pub(crate) content_mapper: Expected<ContentMapperFields>,
}

impl_package_json_deserialize!(TypeScriptFields {
    "contentMapper" => content_mapper,
});

// reflect.Struct → "unknown"
impl ExpectedJSONType for TypeScriptFields {
    fn expected_json_type() -> &'static str {
        "unknown"
    }
}

/// PORT: Go's `Parse` unmarshals into an anonymous struct embedding the three
/// field groups plus a `typescript` member; `Parsed` carries the same members
/// (`Fields` already holds the flattened member set).
#[derive(Clone, Debug, Default)]
struct Parsed {
    fields: Fields,
    /// `TypeScript Expected[typeScriptFields] `json:"typescript"``
    type_script: Expected<TypeScriptFields>,
}

impl_package_json_deserialize!(Parsed {
    "name" => fields.name,
    "version" => fields.version,
    "type" => fields.type_,
    "tsconfig" => fields.ts_config,
    "main" => fields.main,
    "types" => fields.types,
    "typings" => fields.typings,
    "typesVersions" => fields.types_versions,
    "imports" => fields.imports,
    "exports" => fields.exports,
    "dependencies" => fields.dependency_fields.dependencies,
    "devDependencies" => fields.dependency_fields.dev_dependencies,
    "peerDependencies" => fields.dependency_fields.peer_dependencies,
    "optionalDependencies" => fields.dependency_fields.optional_dependencies,
    "typescript" => type_script,
});

/// `func Parse(data []byte) (Fields, error)`
pub fn parse(data: &[u8]) -> Result<Fields, serde_json::Error> {
    let parsed: Parsed = json::unmarshal(data, &[json::allow_duplicate_names(true)])?;
    // PORT: `typeScript, _ := parsed.TypeScript.GetValue()` reads `Value`
    // regardless of `Valid`; `value` is the same slot (it holds the default
    // `TypeScriptFields` when invalid).
    let type_script = parsed.type_script.value;
    let mut fields = parsed.fields;
    fields.content_mapper = type_script.content_mapper;
    Ok(fields)
}
