// Ported from tsc/internal/contentmapper/contentmapper.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*Mapper` parameters/fields become `&Mapper` / `Arc<Mapper>`; the Go code
//   relies on pointer identity for equality and project entry lookup, so
//   `Mapper` is always shared through `Arc` in this port.
// - `json.Value` members become `Option<json::Value>` (a `Box<RawValue>`):
//   Go's `Options json.Value` nil-vs-present distinction matters both for
//   `omitempty` serialization and for `Mapper.Equals`.
// - `Mapper.Equals` compares `Arc` pointer identity first (Go's `m == other`)
//   then field-by-field, including Go's nil-vs-empty slice distinctions via
//   `Option<Vec<_>>`.
// - `MarshalDeclaredOptions` replaces reflection with a whole-options
//   `json.Marshal` + member pick: Go marshals each declared struct field by
//   JSON name in declared order, skipping zero fields — the generated serde
//   impl already emits exactly the non-zero members under their `json` names,
//   so selecting the declared names from that output is equivalent.

use std::sync::{Arc, LazyLock};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use tsc_collections::{OrderedMap, Set};
use tsc_core::options_generated::CompilerOptions;
use tsc_json as json;
use tsc_json::Value;
use tsc_tspath::RootedDirectoryPath;

use crate::xxh3::{self, Uint128};

/// `var ErrProjectUnavailable = errors.New("content mapper project is unavailable")`
///
/// PORT: Go's sentinel error becomes a function returning the [`Error`]
/// variant; consumers match `error.is_project_unavailable()` rather than
/// comparing `err == ErrProjectUnavailable`.
pub fn err_project_unavailable() -> crate::Error {
    crate::Error::ProjectUnavailable
}

/// `type Definition struct` — a content mapper as declared in a tsconfig's
/// "contentMappers": the npm package that implements the mapper and the
/// otherwise unsupported file extensions it registers.
///
/// PORT: `Extensions []string` → `Option<Vec<String>>` preserves Go's
/// nil-vs-empty distinction (`null` vs `[]`), which `Mapper.Equals` inspects.
// PORT: no `PartialEq` — `json::Value` (`Box<RawValue>`) has none; Go uses
// `bytes.Equal` on options where equality matters (`Mapper.Equals`).
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct Definition {
    /// `Package string`
    #[serde(rename = "package", default)]
    pub package: String,
    /// `Extensions []string`
    #[serde(rename = "extensions", default)]
    pub extensions: Option<Vec<String>>,
    /// `Options json.Value json:"options,omitempty"`
    #[serde(rename = "options", default, skip_serializing_if = "Option::is_none")]
    pub options: Option<Value>,
}

/// `type Manifest struct` — the content-mapper information read from a
/// package's package.json: its name and version (which form the mapper's
/// identity), the argv used to run it, and the compiler options it declares
/// it depends on.
#[derive(Clone, Default, Debug)]
pub struct Manifest {
    /// `Name string`
    pub name: String,
    /// `Version string`
    pub version: String,
    /// `Exec []string` — `Option` preserves nil-vs-empty for `Equals`.
    pub exec: Option<Vec<String>>,
    /// `CompilerOptions []string` — `Option` preserves nil-vs-empty for `Equals`.
    pub compiler_options: Option<Vec<String>>,
    /// `DynamicConfig bool`
    pub dynamic_config: bool,
}

/// `type Mapper struct` — a resolved content mapper: its tsconfig
/// `Definition` combined with the `Manifest` resolved from the package's
/// package.json, plus the package directory used as the mapper's working
/// directory.
///
/// PORT: Go embeds `Definition`/`Manifest` (promoting their fields); the
/// fields are flattened here. `Mapper`'s JSON form is the embedded
/// `Definition`'s (`package`/`extensions`/`options`), matching Go's
/// `Manifest json:"-"` exclusion.
#[derive(Clone, Default, Debug)]
pub struct Mapper {
    /// `Definition.Package`
    pub package: String,
    /// `Definition.Extensions`
    pub extensions: Option<Vec<String>>,
    /// `Definition.Options`
    pub options: Option<Value>,
    /// `Manifest.Name`
    pub name: String,
    /// `Manifest.Version`
    pub version: String,
    /// `Manifest.Exec`
    pub exec: Option<Vec<String>>,
    /// `Manifest.CompilerOptions`
    pub compiler_options: Option<Vec<String>>,
    /// `Manifest.DynamicConfig`
    pub dynamic_config: bool,
    /// `PackageDirectory` is the real path directory returned by package
    /// resolution for package-based mappers.
    pub package_directory: RootedDirectoryPath,
    /// `ContributionID` is provided by an LSP client extension for inferred
    /// project content mappers.
    pub contribution_id: String,
}

impl Mapper {
    /// Converts to/from the JSON-visible `Definition` half — the `Serialize`
    /// impl marshals only this shape, as Go's `Manifest json:"-"` does.
    pub(crate) fn definition(&self) -> Definition {
        Definition {
            package: self.package.clone(),
            extensions: self.extensions.clone(),
            options: self.options.clone(),
        }
    }

    /// `func (m *Mapper) DiagnosticName() string` — returns the best
    /// available user-facing name, including when manifest resolution failed.
    pub fn diagnostic_name(&self) -> String {
        if !self.name.is_empty() {
            return self.name.clone();
        }
        if !self.package.is_empty() {
            return self.package.clone();
        }
        self.contribution_id.clone()
    }

    /// `func (m *Mapper) Identity() string` — the mapper's "name@version"
    /// identity, or just the name when it declares no version, or an empty
    /// string when the mapper has not been resolved to a name.
    pub fn identity(&self) -> String {
        if !self.contribution_id.is_empty() {
            return format!("{} ({})", self.contribution_id, self.manifest_identity());
        }
        self.manifest_identity()
    }

    /// `func (m *Mapper) manifestIdentity() string`
    fn manifest_identity(&self) -> String {
        if self.name.is_empty() {
            return String::new();
        }
        if self.version.is_empty() {
            return self.name.clone();
        }
        format!("{}@{}", self.name, self.version)
    }

    /// `func (m *Mapper) Equals(other *Mapper) bool` — compares the complete
    /// mapper configuration, not just its advertised identity. Call with
    /// `&Arc<Mapper>` so `m == other` (pointer identity) is preserved.
    pub fn equals(&self, other: &Arc<Mapper>) -> bool {
        // Go `m == other` compares *Mapper pointers.
        let self_ptr = self as *const Mapper;
        if std::ptr::eq(self_ptr, Arc::as_ptr(other)) {
            return true;
        }
        let empty_options: &[u8] = b"";
        self.package == other.package
            && self.extensions.is_some() == other.extensions.is_some()
            && self.extensions == other.extensions
            && self.options.is_some() == other.options.is_some()
            && self
                .options
                .as_ref()
                .map_or(empty_options, |v| v.get().as_bytes())
                == other
                    .options
                    .as_ref()
                    .map_or(empty_options, |v| v.get().as_bytes())
            && self.name == other.name
            && self.version == other.version
            && self.exec.is_some() == other.exec.is_some()
            && self.exec == other.exec
            && self.compiler_options.is_some() == other.compiler_options.is_some()
            && self.compiler_options == other.compiler_options
            && self.dynamic_config == other.dynamic_config
            && self.package_directory == other.package_directory
            && self.contribution_id == other.contribution_id
    }

    /// `func (m *Mapper) TransformIdentity(options *core.CompilerOptions) xxh3.Uint128`
    ///
    /// A fingerprint of everything besides a file's content that determines
    /// the output of transforming it with this mapper under the given
    /// options. It is a pure function of the mapper and options — the
    /// declared options come from the manifest, so it never starts the
    /// mapper process.
    ///
    /// PORT: `*core.CompilerOptions` → `Option<&CompilerOptions>` (`None` is
    /// Go's nil). As in Go, the marshal errors are ignored (`declared, _ :=`;
    /// `optionsJSON, _ :=` — the generated serde impl cannot fail here).
    pub fn transform_identity(&self, options: Option<&CompilerOptions>) -> Uint128 {
        let declared = self
            .marshal_declared_options(options)
            .unwrap_or_else(|_| OrderedMap::new());
        let options_json = json::marshal(&declared, &[]).unwrap_or_default();
        let mut buf = Vec::with_capacity(
            self.identity().len()
                + 2
                + self.options.as_ref().map_or(0, |v| v.get().len())
                + options_json.len(),
        );
        buf.extend(self.identity().as_bytes());
        buf.push(0);
        if let Some(options) = &self.options {
            buf.extend(options.get().as_bytes());
        }
        buf.push(0);
        buf.extend(&options_json);
        xxh3::hash_128(&buf)
    }

    /// `func (m *Mapper) MarshalDeclaredOptions(options *core.CompilerOptions) (*collections.OrderedMap[string, json.Value], error)`
    ///
    /// Marshals just the compiler options this mapper declared it depends
    /// on, in the declared order, skipping any that are unset. Marshaling
    /// only the declared fields avoids serializing the whole CompilerOptions
    /// when a mapper depends on few options (or none).
    ///
    /// PORT: Go uses reflection to marshal each declared field; here the
    /// whole options object is marshaled once (the generated serde impl
    /// already omits zero-value fields, mirroring `field.IsZero()`) and the
    /// declared members are picked out in declaration order.
    pub fn marshal_declared_options(
        &self,
        options: Option<&CompilerOptions>,
    ) -> Result<OrderedMap<String, Value>, serde_json::Error> {
        let mut out: OrderedMap<String, Value> =
            OrderedMap::with_size_hint(self.compiler_options.as_deref().map_or(0, |v| v.len()));
        let names = self.compiler_options.as_deref().unwrap_or(&[]);
        if options.is_none() || names.is_empty() {
            return Ok(out);
        }
        let serialized: serde_json::Value =
            serde_json::from_slice(&json::marshal(options.unwrap(), &[])?)?;
        let Some(members) = serialized.as_object() else {
            return Ok(out);
        };
        for name in names {
            let Some(member) = members.get(name) else {
                // `!ok` — the JSON name does not correspond to a compiler
                // option field, or the option is unset (Go's `field.IsZero()`
                // mirrors serde's `skip_serializing_if` on the same field).
                continue;
            };
            let raw = serde_json::value::RawValue::from_string(serde_json::to_string(member)?)?;
            out.set(name.to_string(), raw);
        }
        Ok(out)
    }
}

impl Serialize for Mapper {
    /// Go's `Mapper` marshals as its embedded `Definition` — `Manifest` and
    /// the resolved-path fields are `json:"-"`.
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.definition().serialize(s)
    }
}

impl<'de> Deserialize<'de> for Mapper {
    /// Inverse of `Serialize`: parses the `Definition` members; the manifest
    /// fields keep their zero values.
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let definition = Definition::deserialize(d)?;
        Ok(Mapper {
            package: definition.package,
            extensions: definition.extensions,
            options: definition.options,
            ..Mapper::default()
        })
    }
}

/// `var supportedVirtualExtensions`
static SUPPORTED_VIRTUAL_EXTENSIONS: LazyLock<Set<&'static str>> = LazyLock::new(|| {
    let mut s = Set::default();
    for ext in [
        ".js", ".jsx", ".mjs", ".cjs", ".ts", ".tsx", ".mts", ".cts", ".json",
    ] {
        s.add(ext);
    }
    s
});

/// `func IsSupportedVirtualExtension(extension string) bool`
pub fn is_supported_virtual_extension(extension: &str) -> bool {
    SUPPORTED_VIRTUAL_EXTENSIONS.has(extension)
}
