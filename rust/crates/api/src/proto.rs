// Ported from tsc/internal/api/proto.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Native-API wire protocol types: method names, request params, response
// bodies, and the `unmarshalers` dispatch consumed by session.go.
//
// PORT notes:
// - Serde mapping: `json:"camelCase"` → `#[serde(rename_all = "camelCase")]`
//   (or explicit `rename`). `*T omitempty`/`omitzero` → `Option<T>` +
//   `skip_serializing_if`; value `omitempty`/`omitzero` → `Option<T>` where
//   the session assigns, else `T` + `default`/`skip_serializing_if`.
//   `nonnil:"true"` → a value type (or `Option` + `ser_nonnil`) so the field
//   always serializes a non-null JSON value, plus `#[serde(default)]` for
//   missing input — mirroring jsonv2's non-nil marshal behavior.
// - `#[serde(default)]` at the container level mirrors Go's json unmarshal,
//   which never fails on missing fields (absent → zero value).
// - Foreign types without serde impls (`tspath::*`, `project::Id`,
//   `project::SyntheticProjectId`, int-flag/enum types) are bridged via the
//   local `StrWrapped`/`IntTagged` traits + `*_with` helpers — orphan rules
//   prevent impls on the other crates. Go marshals them as plain
//   strings/numbers.
// - `Go int` → `i64`, `int32` → `i32`, `uint32`/`uint64` → `u32`/`u64`.
//   Go's `TypeID uint32` is `pub struct TypeId(pub u64)` — the session's
//   registries key on the u64 wire value; uint32→u64 is wire-identical.
// - `json:"-"` (server-populated fields like `CompilerOptions`) →
//   `#[serde(skip)]`.
// - `SymbolId`/`TypeId`/`SignatureId`/`NodeHandle` are API wire ids, not the
//   checker/ast arena ids — see `symbol_handle`/`type_handle`/
//   `signature_handle` for the mapping.
// - `unmarshalers map[Method]func` → the `unmarshal_payload` match (the keys
//   are the same wire literals; METHOD_* constants name them). Go's generic
//   `unmarshallerFor[T]` returning `any` → `Box<dyn Any>` for session-side
//   downcasting; `noParams` → `Box::new(())` (Go's nil `any`).
// - `ErrInvalidRequest`/`ErrClientError` → `ERR_INVALID_REQUEST`/
//   `ERR_CLIENT_ERROR` message consts; sessions return `Result<_, String>`
//   and protocol_msgpack.rs already wraps the same text in `ipc::Error`.

#![allow(dead_code)]

use std::any::Any;
use std::borrow::Cow;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_hash::FxHashMap;
use serde::de::{self, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use tsc_ast::ast::SourceFileLike as AstSourceFileLike;
use tsc_ast::diagnostic::{
    DiagnosticRef, lock_diagnostic, new_compiler_diagnostic, new_diagnostic_from_text,
};
use tsc_ast::{Node, SymbolId as AstSymbolId};
use tsc_checker::checker_core::is_tuple_type;
use tsc_checker::exports::is_tuple_type_target;
use tsc_checker::types::{
    ElementFlags, ObjectFlags, Signature, Type as CheckerType, TypeArena, TypeFlags,
    TypeId as CheckerTypeId,
};
use tsc_collections::OrderedMap;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::core::{UTF16Offset, utf16_len};
use tsc_core::options_generated::{BuildOptions, CompilerOptions, TypeAcquisition};
use tsc_core::projectreference::ProjectReference;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::TextRange;
use tsc_diagnostics::Category;
use tsc_diagnosticwriter::{ASTDiagnostic, Diagnostic as _, FileLike, wrap_ast_diagnostic};
use tsc_evaluator::Value as EvaluatorValue;
use tsc_execute::tsc::{ExitStatus, Statistics};
use tsc_json as json;
use tsc_locale::locale::DEFAULT as DEFAULT_LOCALE;
use tsc_lsconv::converters::file_name_to_document_uri;
use tsc_lsproto::DocumentUri;
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_module::types::PackageId as ModulePackageId;
use tsc_packagejson::{JSONValue, JSONValueData, JSONValueType};
use tsc_project::project::{Id as ProjectId, Kind as ProjectKind, Project, SyntheticProjectId};
use tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position;
use tsc_spanmap::SpanMap;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::rawcompileroptions::RawCompilerOptions;
use tsc_tsoptions::value::Value as TsValue;
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, to_rooted_file_path,
};

use crate::requestfilesystem::RequestFileSystemParams;

// ---------------------------------------------------------------------------
// Error sentinels (`ErrInvalidRequest`, `ErrClientError`)
// ---------------------------------------------------------------------------

/// `errors.New("api: invalid request")` — message text only; sessions return
/// `Result<_, String>` so the sentinel is the literal message.
pub const ERR_INVALID_REQUEST: &str = "api: invalid request";
/// `errors.New("api: client error")`.
pub const ERR_CLIENT_ERROR: &str = "api: client error";

// ---------------------------------------------------------------------------
// Serde bridges for foreign types (orphan rule)
// ---------------------------------------------------------------------------

/// Bridge for Go `type X string`-ish foreign wrappers — they marshal as a
/// plain JSON string in Go.
trait StrWrapped: Sized {
    fn wrapped_str(&self) -> &str;
    fn wrap_string(s: String) -> Self;
}

impl StrWrapped for RootedFilePath {
    fn wrapped_str(&self) -> &str {
        self.as_string()
    }
    fn wrap_string(s: String) -> Self {
        RootedFilePath::from(s)
    }
}
impl StrWrapped for RootedDirectoryPath {
    fn wrapped_str(&self) -> &str {
        self.as_string()
    }
    fn wrap_string(s: String) -> Self {
        RootedDirectoryPath::from(s)
    }
}
impl StrWrapped for PathKey {
    fn wrapped_str(&self) -> &str {
        self.as_string()
    }
    fn wrap_string(s: String) -> Self {
        PathKey::from(s)
    }
}
impl StrWrapped for ProjectId {
    fn wrapped_str(&self) -> &str {
        self.as_str()
    }
    fn wrap_string(s: String) -> Self {
        ProjectId::from(s)
    }
}
impl StrWrapped for SyntheticProjectId {
    fn wrapped_str(&self) -> &str {
        &self.0
    }
    fn wrap_string(s: String) -> Self {
        SyntheticProjectId(s)
    }
}

fn ser_str<T: StrWrapped, S: Serializer>(v: &T, s: S) -> Result<S::Ok, S::Error> {
    s.serialize_str(v.wrapped_str())
}
fn de_str<'de, T: StrWrapped, D: Deserializer<'de>>(d: D) -> Result<T, D::Error> {
    Ok(T::wrap_string(String::deserialize(d)?))
}
fn ser_str_opt<T: StrWrapped, S: Serializer>(v: &Option<T>, s: S) -> Result<S::Ok, S::Error> {
    match v {
        Some(v) => s.serialize_str(v.wrapped_str()),
        None => s.serialize_none(),
    }
}
fn de_str_opt<'de, T: StrWrapped, D: Deserializer<'de>>(d: D) -> Result<Option<T>, D::Error> {
    Ok(Option::<String>::deserialize(d)?.map(T::wrap_string))
}
fn ser_str_vec<T: StrWrapped, S: Serializer>(v: &[T], s: S) -> Result<S::Ok, S::Error> {
    s.collect_seq(v.iter().map(|x| x.wrapped_str()))
}
fn de_str_vec<'de, T: StrWrapped, D: Deserializer<'de>>(d: D) -> Result<Vec<T>, D::Error> {
    Ok(Vec::<String>::deserialize(d)?
        .into_iter()
        .map(T::wrap_string)
        .collect())
}
fn ser_str_opt_vec<T: StrWrapped, S: Serializer>(
    v: &Option<Vec<T>>,
    s: S,
) -> Result<S::Ok, S::Error> {
    match v {
        Some(v) => s.collect_seq(v.iter().map(|x| x.wrapped_str())),
        None => s.serialize_none(),
    }
}
fn de_str_opt_vec<'de, T: StrWrapped, D: Deserializer<'de>>(
    d: D,
) -> Result<Option<Vec<T>>, D::Error> {
    Ok(Option::<Vec<String>>::deserialize(d)?
        .map(|v| v.into_iter().map(T::wrap_string).collect()))
}
fn str_wrapped_is_empty<T: StrWrapped>(v: &T) -> bool {
    v.wrapped_str().is_empty()
}

/// `map[project.ID]V` — Go map keys are the ID string (JSON object keys).
fn ser_id_map<V: Serialize, S: Serializer>(
    m: &FxHashMap<ProjectId, V>,
    s: S,
) -> Result<S::Ok, S::Error> {
    s.collect_map(m.iter().map(|(k, v)| (k.as_str(), v)))
}
fn de_id_map<'de, V: Deserialize<'de>, D: Deserializer<'de>>(
    d: D,
) -> Result<FxHashMap<ProjectId, V>, D::Error> {
    let raw = FxHashMap::<String, V>::deserialize(d)?;
    Ok(raw.into_iter().map(|(k, v)| (ProjectId::from(k), v)).collect())
}

/// Bridge for Go `type X int`-ish foreign enums/flag-newtypes — they marshal
/// as a JSON number in Go.
trait IntTagged: Sized {
    fn as_i64(&self) -> i64;
    fn from_i64(v: i64) -> Option<Self>;
}

impl IntTagged for ScriptKind {
    fn as_i64(&self) -> i64 {
        *self as i64
    }
    fn from_i64(v: i64) -> Option<Self> {
        Some(match v {
            0 => ScriptKind::Unknown,
            1 => ScriptKind::Js,
            2 => ScriptKind::Jsx,
            3 => ScriptKind::Ts,
            4 => ScriptKind::Tsx,
            6 => ScriptKind::Json,
            _ => return None,
        })
    }
}
impl IntTagged for Category {
    fn as_i64(&self) -> i64 {
        *self as i64
    }
    fn from_i64(v: i64) -> Option<Self> {
        Some(match v {
            0 => Category::Warning,
            1 => Category::Error,
            2 => Category::Suggestion,
            3 => Category::Message,
            _ => return None,
        })
    }
}
impl IntTagged for ExitStatus {
    fn as_i64(&self) -> i64 {
        *self as i64
    }
    fn from_i64(v: i64) -> Option<Self> {
        Some(match v {
            0 => ExitStatus::Success,
            1 => ExitStatus::DiagnosticsPresentOutputsSkipped,
            2 => ExitStatus::DiagnosticsPresentOutputsGenerated,
            3 => ExitStatus::InvalidProjectOutputsSkipped,
            4 => ExitStatus::ProjectReferenceCycleOutputsSkipped,
            5 => ExitStatus::NotImplemented,
            _ => return None,
        })
    }
}
impl IntTagged for CaseSensitivity {
    fn as_i64(&self) -> i64 {
        match self {
            CaseSensitivity::CaseInsensitive => 0,
            CaseSensitivity::CaseSensitive => 1,
        }
    }
    fn from_i64(v: i64) -> Option<Self> {
        Some(match v {
            0 => CaseSensitivity::CaseInsensitive,
            1 => CaseSensitivity::CaseSensitive,
            _ => return None,
        })
    }
}
impl IntTagged for ElementFlags {
    fn as_i64(&self) -> i64 {
        self.0 as i64
    }
    fn from_i64(v: i64) -> Option<Self> {
        u32::try_from(v).ok().map(ElementFlags)
    }
}

fn ser_int<T: IntTagged, S: Serializer>(v: &T, s: S) -> Result<S::Ok, S::Error> {
    s.serialize_i64(v.as_i64())
}
fn de_int<'de, T: IntTagged, D: Deserializer<'de>>(d: D) -> Result<T, D::Error> {
    let v = i64::deserialize(d)?;
    T::from_i64(v).ok_or_else(|| {
        de::Error::custom(format!("unknown {} value {v}", std::any::type_name::<T>()))
    })
}
fn ser_int_opt<T: IntTagged, S: Serializer>(v: &Option<T>, s: S) -> Result<S::Ok, S::Error> {
    match v {
        Some(v) => s.serialize_i64(v.as_i64()),
        None => s.serialize_none(),
    }
}
fn de_int_opt<'de, T: IntTagged, D: Deserializer<'de>>(d: D) -> Result<Option<T>, D::Error> {
    match Option::<i64>::deserialize(d)? {
        Some(v) => Ok(Some(T::from_i64(v).ok_or_else(|| {
            de::Error::custom(format!("unknown {} value {v}", std::any::type_name::<T>()))
        })?)),
        None => Ok(None),
    }
}
fn ser_int_vec<T: IntTagged, S: Serializer>(v: &[T], s: S) -> Result<S::Ok, S::Error> {
    s.collect_seq(v.iter().map(|x| x.as_i64()))
}
fn de_int_vec<'de, T: IntTagged, D: Deserializer<'de>>(d: D) -> Result<Vec<T>, D::Error> {
    Vec::<i64>::deserialize(d)?
        .into_iter()
        .map(|v| {
            T::from_i64(v).ok_or_else(|| {
                de::Error::custom(format!("unknown {} value {v}", std::any::type_name::<T>()))
            })
        })
        .collect()
}

/// `*T nonnil:"true"` — a nil Go pointer marshals as the JSON zero value of
/// the underlying type; `Option` serializes `T::default()` when `None`.
fn ser_nonnil<T, S>(v: &Option<T>, s: S) -> Result<S::Ok, S::Error>
where
    T: Default + Serialize,
    S: Serializer,
{
    match v {
        Some(v) => v.serialize(s),
        None => T::default().serialize(s),
    }
}

/// `tsc.Statistics` — Go jsonv2 exports the three exported fields with their
/// Go names (`Projects`, `ProjectsBuilt`, `TimestampUpdates`); private fields
/// are not serializable in Go either (the Rust port's private fields mirror
/// those unexported fields, so only the same three round-trip).
fn ser_statistics<S: Serializer>(v: &Statistics, s: S) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;
    let mut st = s.serialize_struct("Statistics", 3)?;
    st.serialize_field("Projects", &v.projects)?;
    st.serialize_field("ProjectsBuilt", &v.projects_built)?;
    st.serialize_field("TimestampUpdates", &v.timestamp_updates)?;
    st.end()
}
fn de_statistics<'de, D: Deserializer<'de>>(d: D) -> Result<Statistics, D::Error> {
    #[derive(Default, Deserialize)]
    #[serde(default)]
    struct StatisticsFields {
        #[serde(rename = "Projects")]
        projects: i32,
        #[serde(rename = "ProjectsBuilt")]
        projects_built: i32,
        #[serde(rename = "TimestampUpdates")]
        timestamp_updates: i32,
    }
    let f = StatisticsFields::deserialize(d)?;
    let mut stats = Statistics::default();
    stats.projects = f.projects;
    stats.projects_built = f.projects_built;
    stats.timestamp_updates = f.timestamp_updates;
    Ok(stats)
}

fn exit_status_default() -> ExitStatus {
    // Go's `tsc.ExitStatus` zero value.
    ExitStatus::Success
}
fn category_default() -> Category {
    // Go's `diagnostics.Category` zero value.
    Category::Warning
}

fn is_zero_u32(v: &u32) -> bool {
    *v == 0
}
fn is_zero_i32(v: &i32) -> bool {
    *v == 0
}
fn is_zero_i64(v: &i64) -> bool {
    *v == 0
}
fn is_zero_u64(v: &u64) -> bool {
    *v == 0
}
fn is_false(v: &bool) -> bool {
    !*v
}
fn document_uri_is_empty(v: &DocumentUri) -> bool {
    v.0.is_empty()
}
fn node_handle_is_empty(v: &NodeHandle) -> bool {
    v.0.is_empty()
}
fn changed_projects_is_empty(m: &FxHashMap<ProjectId, ProjectFileChanges>) -> bool {
    m.is_empty()
}
fn script_kind_is_unknown(v: &ScriptKind) -> bool {
    *v == ScriptKind::Unknown
}

/// Defines a Go `type X string` newtype (`Method`, `NodeHandle`,
/// `ModuleResolutionFallback`, `ImportAdderActionKind`) over
/// `Cow<'static, str>` — const-constructible for method constants,
/// `Cow::Owned` on deserialize and for session-built handles.
macro_rules! api_string_newtype {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $name(pub Cow<'static, str>);

        impl $name {
            /// Constant constructor used by the `*_KIND_*`/`METHOD_*` consts.
            pub const fn new(s: &'static str) -> Self {
                $name(Cow::Borrowed(s))
            }
            pub fn as_str(&self) -> &str {
                &self.0
            }
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.0)
            }
        }

        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_str(&self.0)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                Ok($name(Cow::Owned(String::deserialize(d)?)))
            }
        }
    };
}

api_string_newtype! {
    /// `type Method string` — the wire method name.
    Method
}
api_string_newtype! {
    /// `type NodeHandle string` — opaque server-side node handle.
    NodeHandle
}
api_string_newtype! {
    /// `type ModuleResolutionFallback string`.
    ModuleResolutionFallback
}
api_string_newtype! {
    /// `type ImportAdderActionKind string`.
    ImportAdderActionKind
}

// ---------------------------------------------------------------------------
// ID types (`type ( SnapshotID uint64 ... )`)
// ---------------------------------------------------------------------------

/// Bridge trait for the u64 wire-id newtypes (Go `type X uint64`) — the
/// `omitzero` skip check looks through `Option` like Go's zero value.
trait WireId: Sized {
    fn raw(&self) -> u64;
}
fn wire_id_is_zero<T: WireId>(v: &T) -> bool {
    v.raw() == 0
}
/// `Option<Id>` that treats `Some(0)` like Go's `omitzero` on the id value —
/// the session uses `Some(TypeId(0))`/`Some(SignatureId(0))` as sentinels for
/// the absent-id case Go writes as the zero value.
fn opt_wire_id_is_zero<T: WireId>(v: &Option<T>) -> bool {
    v.as_ref().map_or(true, |t| t.raw() == 0)
}

macro_rules! api_id_newtype {
    ($(#[$meta:meta])* $name:ident, $gotype:literal) => {
        $(#[$meta])*
        /// Go `$gotype` — serializes as a JSON number.
        #[derive(
            Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash,
            Serialize, Deserialize,
        )]
        #[serde(transparent)]
        pub struct $name(pub u64);

        impl $name {
            /// `id == 0` — Go's nil handle check.
            pub const fn is_zero(&self) -> bool {
                self.0 == 0
            }
        }

        impl WireId for $name {
            fn raw(&self) -> u64 {
                self.0
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }

        impl PartialEq<u64> for $name {
            fn eq(&self, other: &u64) -> bool {
                self.0 == *other
            }
        }

        impl From<u64> for $name {
            fn from(v: u64) -> Self {
                Self(v)
            }
        }
    };
}

api_id_newtype! {
    /// `type SnapshotID uint64`.
    SnapshotId, "SnapshotID uint64"
}
api_id_newtype! {
    /// `type ModuleResolverID uint64`.
    ModuleResolverId, "ModuleResolverID uint64"
}
api_id_newtype! {
    /// `type SourceFileLeaseID uint64`.
    SourceFileLeaseId, "SourceFileLeaseID uint64"
}
api_id_newtype! {
    /// `type BuildOrchestratorID uint64`.
    BuildOrchestratorId, "BuildOrchestratorID uint64"
}
api_id_newtype! {
    /// `type SymbolID uint64` — API wire id, not `ast::SymbolId`.
    SymbolId, "SymbolID uint64"
}
api_id_newtype! {
    /// `type TypeID uint32` — API wire id, not `checker::TypeId`.
    /// PORT: inner is `u64` (session registries index the u64 wire value).
    TypeId, "TypeID uint32"
}
api_id_newtype! {
    /// `type SignatureID uint64` — API wire id, not `checker::SignatureId`.
    SignatureId, "SignatureID uint64"
}

static NEXT_BUILD_ORCHESTRATOR_ID: AtomicU64 = AtomicU64::new(0);

/// `func NewBuildOrchestratorID() BuildOrchestratorID` — `Add(1)` returns the
/// new value; `fetch_add(1)+1` is equivalent.
pub fn new_build_orchestrator_id() -> BuildOrchestratorId {
    BuildOrchestratorId(NEXT_BUILD_ORCHESTRATOR_ID.fetch_add(1, Ordering::Relaxed) + 1)
}

/// `func SymbolHandle(symbol *ast.Symbol) SymbolID`.
///
/// PORT: Go reads a lazily-assigned atomic counter off `*ast.Symbol`; the
/// session's canonical version (`session.rs::symbol_handle`) uses the symbol's
/// stable arena pointer — this arena-slot variant exists for proto parity.
pub fn symbol_handle(symbol: AstSymbolId) -> SymbolId {
    SymbolId(symbol.0 as u64)
}

/// `func TypeHandle(t *checker.Type) TypeID` — `t.Id()`.
pub fn type_handle(t: &CheckerType) -> TypeId {
    TypeId(t.id().0 as u64)
}

/// `func SignatureHandle(sig *checker.Signature) SignatureID` — `sig.Id()`.
pub fn signature_handle(sig: &Signature) -> SignatureId {
    SignatureId(sig.id().0 as u64)
}

// ---------------------------------------------------------------------------
// Method constants (Go `const ( MethodXxx Method = "..." )` block)
// ---------------------------------------------------------------------------

pub const METHOD_RELEASE: Method = Method::new("release");
pub const METHOD_RELEASE_SOURCE_FILE: Method = Method::new("releaseSourceFile");
pub const METHOD_RETAIN_SOURCE_FILE: Method = Method::new("retainSourceFile");
pub const METHOD_GET_CACHED_SOURCE_FILE: Method = Method::new("getCachedSourceFile");
pub const METHOD_GET_SYMBOL_OF_DECLARATION: Method = Method::new("getSymbolOfDeclaration");

pub const METHOD_BATCH_REQUESTS: Method = Method::new("batchRequests");
pub const METHOD_INITIALIZE: Method = Method::new("initialize");
pub const METHOD_CREATE_SNAPSHOT: Method = Method::new("createSnapshot");
pub const METHOD_UPDATE_SNAPSHOT: Method = Method::new("updateSnapshot");
pub const METHOD_GET_CURRENT_LANGUAGE_SERVER_SNAPSHOT: Method =
    Method::new("getCurrentLanguageServerSnapshot");
pub const METHOD_CREATE_BUILD_ORCHESTRATOR: Method = Method::new("createBuildOrchestrator");
pub const METHOD_DISPOSE_BUILD_ORCHESTRATOR: Method = Method::new("disposeBuildOrchestrator");
pub const METHOD_BUILD: Method = Method::new("build");
pub const METHOD_BUILD_REFERENCES: Method = Method::new("buildReferences");
pub const METHOD_CLEAN_BUILD: Method = Method::new("cleanBuild");
pub const METHOD_CLEAN_REFERENCES: Method = Method::new("cleanReferences");
pub const METHOD_CREATE_MODULE_RESOLVER: Method = Method::new("createModuleResolver");
pub const METHOD_RELEASE_MODULE_RESOLVER: Method = Method::new("releaseModuleResolver");
pub const METHOD_RESOLVE_MODULE_NAME: Method = Method::new("resolveModuleName");
pub const METHOD_PARSE_COMMAND_LINE: Method = Method::new("parseCommandLine");
pub const METHOD_READ_CONFIG_FILE: Method = Method::new("readConfigFile");
pub const METHOD_PARSE_JSON_CONFIG_FILE: Method = Method::new("parseJsonConfigFileContent");
pub const METHOD_PARSE_CONFIG_FILE: Method = Method::new("parseConfigFile");
pub const METHOD_CREATE_SOURCE_FILE: Method = Method::new("createSourceFile");
pub const METHOD_CREATE_SOURCE_FILE_FROM_FILE: Method = Method::new("createSourceFileFromFile");
pub const METHOD_TRANSPILE_MODULE: Method = Method::new("transpileModule");
pub const METHOD_TRANSPILE_MODULE_FROM_FILE: Method = Method::new("transpileModuleFromFile");
pub const METHOD_TRANSPILE_DECLARATION: Method = Method::new("transpileDeclaration");
pub const METHOD_TRANSPILE_DECLARATION_FROM_FILE: Method =
    Method::new("transpileDeclarationFromFile");
pub const METHOD_GET_DEFAULT_PROJECT_FOR_FILE: Method = Method::new("getDefaultProjectForFile");
pub const METHOD_GET_SYMBOL_AT_POSITION: Method = Method::new("getSymbolAtPosition");
pub const METHOD_GET_SYMBOLS_AT_POSITIONS: Method = Method::new("getSymbolsAtPositions");
pub const METHOD_GET_SYMBOL_AT_LOCATION: Method = Method::new("getSymbolAtLocation");
pub const METHOD_GET_SYMBOLS_AT_LOCATIONS: Method = Method::new("getSymbolsAtLocations");
pub const METHOD_GET_SYMBOL_OF_SOURCE_FILE: Method = Method::new("getSymbolOfSourceFile");
pub const METHOD_GET_SYMBOLS_OF_SOURCE_FILES: Method = Method::new("getSymbolsOfSourceFiles");
pub const METHOD_GET_TYPE_OF_SYMBOL: Method = Method::new("getTypeOfSymbol");
pub const METHOD_GET_TYPES_OF_SYMBOLS: Method = Method::new("getTypesOfSymbols");
pub const METHOD_GET_DECLARED_TYPE_OF_SYMBOL: Method = Method::new("getDeclaredTypeOfSymbol");
pub const METHOD_GET_NON_MISSING_TYPE_OF_SYMBOL: Method =
    Method::new("getNonMissingTypeOfSymbol");
pub const METHOD_GET_SOURCE_FILE: Method = Method::new("getSourceFile");
pub const METHOD_GET_SOURCE_FILE_NAMES: Method = Method::new("getSourceFileNames");
pub const METHOD_GET_SOURCE_FILE_METADATA: Method = Method::new("getSourceFileMetadata");
pub const METHOD_GET_MODE_FOR_USAGE_LOCATION: Method = Method::new("getModeForUsageLocation");
pub const METHOD_GET_MODE_FOR_RESOLUTION_AT_INDEX: Method =
    Method::new("getModeForResolutionAtIndex");
pub const METHOD_GET_RESOLVED_MODULE: Method = Method::new("getResolvedModule");
pub const METHOD_GET_RESOLVED_MODULE_FROM_MODULE_SPECIFIER: Method =
    Method::new("getResolvedModuleFromModuleSpecifier");
pub const METHOD_GET_RESOLVED_TYPE_REFERENCE_DIRECTIVE: Method =
    Method::new("getResolvedTypeReferenceDirective");
pub const METHOD_GET_RESOLVED_TYPE_REFERENCE_DIRECTIVE_FROM_REFERENCE: Method =
    Method::new("getResolvedTypeReferenceDirectiveFromTypeReferenceDirective");
pub const METHOD_GET_CONFIG_FILE_NAMES: Method = Method::new("getConfigFileNames");
pub const METHOD_GET_CONFIG_SOURCE_FILE: Method = Method::new("getConfigSourceFile");
pub const METHOD_RESOLVE_NAME: Method = Method::new("resolveName");
pub const METHOD_GET_SYMBOLS_IN_SCOPE: Method = Method::new("getSymbolsInScope");
pub const METHOD_GET_SIGNATURES_OF_TYPE: Method = Method::new("getSignaturesOfType");
pub const METHOD_GET_RESOLVED_SIGNATURE: Method = Method::new("getResolvedSignature");
pub const METHOD_GET_TYPE_AT_LOCATION: Method = Method::new("getTypeAtLocation");
pub const METHOD_GET_TYPE_AT_LOCATIONS: Method = Method::new("getTypeAtLocations");
pub const METHOD_GET_TYPE_AT_POSITION: Method = Method::new("getTypeAtPosition");
pub const METHOD_GET_TYPES_AT_POSITIONS: Method = Method::new("getTypesAtPositions");

// Symbol sub-property methods
pub const METHOD_GET_PARENT_OF_SYMBOL: Method = Method::new("getParentOfSymbol");
pub const METHOD_GET_MEMBERS_OF_SYMBOL: Method = Method::new("getMembersOfSymbol");
pub const METHOD_GET_EXPORTS_OF_SYMBOL: Method = Method::new("getExportsOfSymbol");
pub const METHOD_GET_EXPORT_SYMBOL_OF_SYMBOL: Method = Method::new("getExportSymbolOfSymbol");

// Type sub-property methods
pub const METHOD_GET_SYMBOL_OF_TYPE: Method = Method::new("getSymbolOfType");
pub const METHOD_GET_TARGET_OF_TYPE: Method = Method::new("getTargetOfType");
pub const METHOD_GET_FRESH_TYPE_OF_TYPE: Method = Method::new("getFreshTypeOfType");
pub const METHOD_GET_REGULAR_TYPE_OF_TYPE: Method = Method::new("getRegularTypeOfType");
pub const METHOD_GET_TYPES_OF_TYPE: Method = Method::new("getTypesOfType");
pub const METHOD_GET_TYPE_PARAMETERS_OF_TYPE: Method = Method::new("getTypeParametersOfType");
pub const METHOD_GET_OUTER_TYPE_PARAMETERS_OF_TYPE: Method =
    Method::new("getOuterTypeParametersOfType");
pub const METHOD_GET_LOCAL_TYPE_PARAMETERS_OF_TYPE: Method =
    Method::new("getLocalTypeParametersOfType");
pub const METHOD_GET_THIS_TYPE_OF_TYPE: Method = Method::new("getThisTypeOfType");
pub const METHOD_GET_ALIAS_TYPE_ARGUMENTS_OF_TYPE: Method =
    Method::new("getAliasTypeArgumentsOfType");
pub const METHOD_GET_ALIAS_SYMBOL_OF_TYPE: Method = Method::new("getAliasSymbolOfType");
pub const METHOD_GET_OBJECT_TYPE_OF_TYPE: Method = Method::new("getObjectTypeOfType");
pub const METHOD_GET_INDEX_TYPE_OF_TYPE: Method = Method::new("getIndexTypeOfType");
pub const METHOD_GET_CHECK_TYPE_OF_TYPE: Method = Method::new("getCheckTypeOfType");
pub const METHOD_GET_EXTENDS_TYPE_OF_TYPE: Method = Method::new("getExtendsTypeOfType");
pub const METHOD_GET_BASE_TYPE_OF_TYPE: Method = Method::new("getBaseTypeOfType");
pub const METHOD_GET_CONSTRAINT_OF_TYPE: Method = Method::new("getConstraintOfType");
pub const METHOD_GET_TYPE_PARAMETER_OF_MAPPED_TYPE: Method =
    Method::new("getTypeParameterOfMappedType");
pub const METHOD_GET_CONSTRAINT_TYPE_OF_MAPPED_TYPE: Method =
    Method::new("getConstraintTypeOfMappedType");
pub const METHOD_GET_NAME_TYPE_OF_MAPPED_TYPE: Method = Method::new("getNameTypeOfMappedType");
pub const METHOD_GET_TEMPLATE_TYPE_OF_MAPPED_TYPE: Method =
    Method::new("getTemplateTypeOfMappedType");

// Signature sub-property methods
pub const METHOD_GET_TYPE_PARAMETERS_OF_SIGNATURE: Method =
    Method::new("getTypeParametersOfSignature");
pub const METHOD_GET_PARAMETERS_OF_SIGNATURE: Method = Method::new("getParametersOfSignature");
pub const METHOD_GET_THIS_PARAMETER_OF_SIGNATURE: Method =
    Method::new("getThisParameterOfSignature");
pub const METHOD_GET_TARGET_OF_SIGNATURE: Method = Method::new("getTargetOfSignature");

// Checker methods
pub const METHOD_GET_CONTEXTUAL_TYPE: Method = Method::new("getContextualType");
pub const METHOD_GET_CONTEXTUAL_TYPE_FOR_ARGUMENT: Method =
    Method::new("getContextualTypeForArgument");
pub const METHOD_GET_AWAITED_TYPE: Method = Method::new("getAwaitedType");
pub const METHOD_GET_BASE_TYPE_OF_LITERAL_TYPE: Method =
    Method::new("getBaseTypeOfLiteralType");
pub const METHOD_GET_NON_NULLABLE_TYPE: Method = Method::new("getNonNullableType");
pub const METHOD_GET_TYPE_FROM_TYPE_NODE: Method = Method::new("getTypeFromTypeNode");
pub const METHOD_GET_WIDENED_TYPE: Method = Method::new("getWidenedType");
pub const METHOD_GET_PARAMETER_TYPE: Method = Method::new("getParameterType");
pub const METHOD_GET_TYPE_PARAMETER_AT_POSITION: Method =
    Method::new("getTypeParameterAtPosition");
pub const METHOD_IS_ARRAY_LIKE_TYPE: Method = Method::new("isArrayLikeType");
pub const METHOD_IS_TYPE_ASSIGNABLE_TO: Method = Method::new("isTypeAssignableTo");
pub const METHOD_GET_SHORTHAND_ASSIGNMENT_VALUE_SYMBOL: Method =
    Method::new("getShorthandAssignmentValueSymbol");
pub const METHOD_GET_TYPE_OF_SYMBOL_AT_LOCATION: Method =
    Method::new("getTypeOfSymbolAtLocation");
pub const METHOD_TYPE_TO_TYPE_NODE: Method = Method::new("typeToTypeNode");
pub const METHOD_SIGNATURE_TO_SIGNATURE_DECLARATION: Method =
    Method::new("signatureToSignatureDeclaration");
pub const METHOD_TYPE_TO_STRING: Method = Method::new("typeToString");
pub const METHOD_IS_CONTEXT_SENSITIVE: Method = Method::new("isContextSensitive");
pub const METHOD_GET_RETURN_TYPE_OF_SIGNATURE: Method =
    Method::new("getReturnTypeOfSignature");
pub const METHOD_GET_REST_TYPE_OF_SIGNATURE: Method = Method::new("getRestTypeOfSignature");
pub const METHOD_GET_TYPE_PREDICATE_OF_SIGNATURE: Method =
    Method::new("getTypePredicateOfSignature");
pub const METHOD_GET_BASE_TYPES: Method = Method::new("getBaseTypes");
pub const METHOD_GET_PROPERTIES_OF_TYPE: Method = Method::new("getPropertiesOfType");
pub const METHOD_GET_APPARENT_PROPERTIES_OF_TYPE: Method =
    Method::new("getApparentPropertiesOfType");
pub const METHOD_GET_APPARENT_TYPE: Method = Method::new("getApparentType");
pub const METHOD_GET_REDUCED_TYPE: Method = Method::new("getReducedType");
pub const METHOD_GET_PROPERTY_OF_TYPE: Method = Method::new("getPropertyOfType");
pub const METHOD_GET_TYPE_OF_PROPERTY_OF_TYPE: Method =
    Method::new("getTypeOfPropertyOfType");
pub const METHOD_GET_INDEX_INFO_OF_TYPE: Method = Method::new("getIndexInfoOfType");
pub const METHOD_GET_INDEX_INFOS_OF_TYPE: Method = Method::new("getIndexInfosOfType");
pub const METHOD_GET_CONSTRAINT_OF_TYPE_PARAMETER: Method =
    Method::new("getConstraintOfTypeParameter");
pub const METHOD_GET_DEFAULT_FROM_TYPE_PARAMETER: Method =
    Method::new("getDefaultFromTypeParameter");
pub const METHOD_GET_BASE_CONSTRAINT_OF_TYPE: Method = Method::new("getBaseConstraintOfType");
pub const METHOD_GET_TYPE_ARGUMENTS: Method = Method::new("getTypeArguments");
pub const METHOD_GET_IMPORT_ADDER_EDITS: Method = Method::new("getImportAdderEdits");
pub const METHOD_GET_TRUE_TYPE_OF_CONDITIONAL_TYPE: Method =
    Method::new("getTrueTypeOfConditionalType");
pub const METHOD_GET_FALSE_TYPE_OF_CONDITIONAL_TYPE: Method =
    Method::new("getFalseTypeOfConditionalType");
pub const METHOD_GET_CONSTANT_VALUE: Method = Method::new("getConstantValue");
pub const METHOD_GET_SIGNATURE_FROM_DECLARATION: Method =
    Method::new("getSignatureFromDeclaration");
pub const METHOD_GET_EXPORT_SPECIFIER_LOCAL_TARGET: Method =
    Method::new("getExportSpecifierLocalTargetSymbol");
pub const METHOD_GET_ALIASED_SYMBOL: Method = Method::new("getAliasedSymbol");
pub const METHOD_GET_IMMEDIATE_ALIASED_SYMBOL: Method = Method::new("getImmediateAliasedSymbol");
pub const METHOD_GET_TARGET_SYMBOL: Method = Method::new("getTargetSymbol");
pub const METHOD_GET_MERGED_SYMBOL: Method = Method::new("getMergedSymbol");
pub const METHOD_GET_SYMBOL_OF_NODE: Method = Method::new("getSymbolOfNode");
pub const METHOD_GET_SYMBOL_OF_DECLARATION_FOR_CHECKER: Method =
    Method::new("getSymbolOfDeclarationForChecker");
pub const METHOD_GET_PARENT_OF_SYMBOL_FOR_CHECKER: Method =
    Method::new("getParentOfSymbolForChecker");
pub const METHOD_GET_EXPORT_SYMBOL_OF_SYMBOL_FOR_CHECKER: Method =
    Method::new("getExportSymbolOfSymbolForChecker");
pub const METHOD_GET_FULLY_QUALIFIED_NAME: Method = Method::new("getFullyQualifiedName");
pub const METHOD_GET_EXPORTS_OF_MODULE: Method = Method::new("getExportsOfModule");
pub const METHOD_GET_MEMBER_IN_MODULE_EXPORTS: Method = Method::new("getMemberInModuleExports");
pub const METHOD_GET_JS_DOC_TAGS: Method = Method::new("getJsDocTags");
pub const METHOD_GET_DOCUMENTATION_COMMENT: Method = Method::new("getDocumentationComment");
pub const METHOD_IS_ARRAY_TYPE: Method = Method::new("isArrayType");
pub const METHOD_IS_READONLY_SYMBOL: Method = Method::new("isReadonlySymbol");

// Reference methods
pub const METHOD_GET_REFERENCES_TO_SYMBOL_IN_FILE: Method =
    Method::new("getReferencesToSymbolInFile");
pub const METHOD_GET_REFERENCED_SYMBOLS_FOR_NODE: Method =
    Method::new("getReferencedSymbolsForNode");
pub const METHOD_GET_SIGNATURE_USAGES: Method = Method::new("getSignatureUsages");

// Language service methods
pub const METHOD_GET_COMPLETIONS_AT_POSITION: Method = Method::new("getCompletionsAtPosition");

// Diagnostic methods
pub const METHOD_GET_SYNTACTIC_DIAGNOSTICS: Method = Method::new("getSyntacticDiagnostics");
pub const METHOD_GET_BIND_DIAGNOSTICS: Method = Method::new("getBindDiagnostics");
pub const METHOD_GET_SEMANTIC_DIAGNOSTICS: Method = Method::new("getSemanticDiagnostics");
pub const METHOD_GET_SUGGESTION_DIAGNOSTICS: Method = Method::new("getSuggestionDiagnostics");
pub const METHOD_GET_DECLARATION_DIAGNOSTICS: Method = Method::new("getDeclarationDiagnostics");
pub const METHOD_GET_PROGRAM_DIAGNOSTICS: Method = Method::new("getProgramDiagnostics");
pub const METHOD_GET_GLOBAL_DIAGNOSTICS: Method = Method::new("getGlobalDiagnostics");
pub const METHOD_GET_CONFIG_FILE_PARSING_DIAGNOSTICS: Method =
    Method::new("getConfigFileParsingDiagnostics");

// Printer methods
pub const METHOD_PRINT_NODE: Method = Method::new("printNode");
pub const METHOD_FORMAT_NODE_FOR_INSERTION: Method = Method::new("formatNodeForInsertion");
pub const METHOD_EMIT: Method = Method::new("emit");
pub const METHOD_EMIT_TO_STRING: Method = Method::new("emitToString");
pub const METHOD_GET_JAVA_SCRIPT_EMIT: Method = Method::new("getJavaScriptEmit");
pub const METHOD_GET_DECLARATION_EMIT: Method = Method::new("getDeclarationEmit");

// Intrinsic type getters
pub const METHOD_GET_ANY_TYPE: Method = Method::new("getAnyType");
pub const METHOD_GET_STRING_TYPE: Method = Method::new("getStringType");
pub const METHOD_GET_NUMBER_TYPE: Method = Method::new("getNumberType");
pub const METHOD_GET_BOOLEAN_TYPE: Method = Method::new("getBooleanType");
pub const METHOD_GET_VOID_TYPE: Method = Method::new("getVoidType");
pub const METHOD_GET_UNDEFINED_TYPE: Method = Method::new("getUndefinedType");
pub const METHOD_GET_NULL_TYPE: Method = Method::new("getNullType");
pub const METHOD_GET_NEVER_TYPE: Method = Method::new("getNeverType");
pub const METHOD_GET_UNKNOWN_TYPE: Method = Method::new("getUnknownType");
pub const METHOD_GET_BIG_INT_TYPE: Method = Method::new("getBigIntType");
pub const METHOD_GET_ES_SYMBOL_TYPE: Method = Method::new("getESSymbolType");
pub const METHOD_GET_NON_PRIMITIVE_TYPE: Method = Method::new("getNonPrimitiveType");

// Well-known per-checker symbols
pub const METHOD_GET_WELL_KNOWN_SYMBOLS: Method = Method::new("getWellKnownSymbols");

// Well-known per-checker signatures
pub const METHOD_GET_WELL_KNOWN_SIGNATURES: Method = Method::new("getWellKnownSignatures");

// Profiling methods
pub const METHOD_START_CPU_PROFILE: Method = Method::new("startCPUProfile");
pub const METHOD_STOP_CPU_PROFILE: Method = Method::new("stopCPUProfile");
pub const METHOD_SAVE_HEAP_PROFILE: Method = Method::new("saveHeapProfile");

// ---------------------------------------------------------------------------
// InitializeResponse
// ---------------------------------------------------------------------------

/// `type InitializeResponse struct` — returned by the initialize method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct InitializeResponse {
    /// `CaseSensitivity` determines how the host file system compares paths.
    /// Go's `uint8` enum serializes as a number.
    #[serde(serialize_with = "ser_int", deserialize_with = "de_int")]
    pub case_sensitivity: CaseSensitivity,
    /// `CurrentDirectory` is the server's current working directory.
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub current_directory: RootedDirectoryPath,
}

// ---------------------------------------------------------------------------
// DocumentIdentifier — string | { uri: string } on the wire
// ---------------------------------------------------------------------------

/// `type DocumentIdentifier struct` — identifies a document by either a file
/// name (plain string) or a URI object. On the wire it is
/// `string | { uri: string }`.
///
/// Go's custom `UnmarshalJSONFrom` accepts a bare string (-> `FileName`) or an
/// object `{"uri": "..."}`; `Serialize` is the default struct shape
/// (`{"fileName":...,"uri":...}` with both omitempty).
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DocumentIdentifier {
    #[serde(skip_serializing_if = "String::is_empty")]
    pub file_name: String,
    #[serde(skip_serializing_if = "document_uri_is_empty")]
    pub uri: DocumentUri,
}

/// `func (d *DocumentIdentifier) UnmarshalJSONFrom(dec *json.Decoder) error`.
///
/// PORT: serde `deserialize_any` visitor mirrors the Go token-level decoder —
/// Go's `dec.ReadToken`/`PeekKind`/`SkipValue` become `visit_str`/`visit_map`/
/// `IgnoredAny`. Error text is preserved verbatim; the Go `key.Kind() != '"'`
/// check is unreachable over serde (object keys are always strings) and is
/// omitted. The `%v` `json.Kind` names are reproduced for the type-error
/// messages (`"number"`, `"true"`, `"false"`, `"null"`, `"array begin"`).
impl<'de> Deserialize<'de> for DocumentIdentifier {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct DocumentIdentifierVisitor;

        fn expected_string_or_object<E: de::Error>(kind: &str) -> E {
            E::custom(format!(
                "DocumentIdentifier: expected string or object, got {kind}"
            ))
        }

        impl<'de> Visitor<'de> for DocumentIdentifierVisitor {
            type Value = DocumentIdentifier;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("string or object")
            }

            fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
                if v.is_empty() {
                    return Err(E::custom("DocumentIdentifier: file name must not be empty"));
                }
                Ok(DocumentIdentifier {
                    file_name: v.to_string(),
                    uri: DocumentUri::default(),
                })
            }

            fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
                self.visit_str(&v)
            }

            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                let mut uri: Option<DocumentUri> = None;
                while let Some(key) = map.next_key::<String>()? {
                    if key == "uri" {
                        if uri.is_some() {
                            return Err(de::Error::custom(format!(
                                "DocumentIdentifier: duplicate field {key:?}"
                            )));
                        }
                        let value = map.next_value::<serde_json::Value>()?;
                        match value.as_str() {
                            Some(s) if !s.is_empty() => {
                                uri = Some(DocumentUri(s.to_string()));
                            }
                            _ => {
                                return Err(de::Error::custom(
                                    "DocumentIdentifier: uri must be a non-empty string",
                                ));
                            }
                        }
                    } else {
                        // `dec.SkipValue()`
                        map.next_value::<IgnoredAny>()?;
                    }
                }
                match uri {
                    Some(uri) => Ok(DocumentIdentifier {
                        file_name: String::new(),
                        uri,
                    }),
                    None => Err(de::Error::custom(
                        "DocumentIdentifier: object must contain uri",
                    )),
                }
            }

            fn visit_seq<A: SeqAccess<'de>>(self, _seq: A) -> Result<Self::Value, A::Error> {
                Err(expected_string_or_object("array begin"))
            }

            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Self::Value, E> {
                Err(expected_string_or_object(if v { "true" } else { "false" }))
            }

            fn visit_i64<E: de::Error>(self, _v: i64) -> Result<Self::Value, E> {
                Err(expected_string_or_object("number"))
            }

            fn visit_u64<E: de::Error>(self, _v: u64) -> Result<Self::Value, E> {
                Err(expected_string_or_object("number"))
            }

            fn visit_f64<E: de::Error>(self, _v: f64) -> Result<Self::Value, E> {
                Err(expected_string_or_object("number"))
            }

            fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
                Err(expected_string_or_object("null"))
            }

            fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
                Err(expected_string_or_object("null"))
            }
        }

        deserializer.deserialize_any(DocumentIdentifierVisitor)
    }
}

impl DocumentIdentifier {
    /// `func (d DocumentIdentifier) ToFileName(cwd) tspath.RootedFilePath`.
    pub fn to_file_name(&self, cwd: &RootedDirectoryPath) -> RootedFilePath {
        if !self.uri.0.is_empty() {
            return self.uri.file_name();
        }
        to_rooted_file_path(&self.file_name, cwd)
    }

    /// `func (d DocumentIdentifier) ToURI(cwd) lsproto.DocumentUri` — an
    /// explicitly provided URI is returned as-is; a file name is first
    /// normalized to an absolute path against cwd before being converted.
    pub fn to_uri(&self, cwd: &RootedDirectoryPath) -> DocumentUri {
        if !self.uri.0.is_empty() {
            return self.uri.clone();
        }
        file_name_to_document_uri(&self.to_file_name(cwd))
    }
}

/// `func (d DocumentIdentifier) String() string`.
impl fmt::Display for DocumentIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.uri.0.is_empty() {
            f.write_str(&self.uri.0)
        } else {
            f.write_str(&self.file_name)
        }
    }
}

// ---------------------------------------------------------------------------
// FileNotifications / SnapshotRequestChangesParams / EnsurePrograms
// ---------------------------------------------------------------------------

/// `type FileNotifications struct` — describes changes to files that have
/// occurred on the host file system, used to notify the session to reload
/// cached files and reevaluate tsconfig.json `include` globs. Either
/// InvalidateAll is true (discard all caches) or Changed/Created/Deleted list
/// individual documents.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct FileNotifications {
    #[serde(skip_serializing_if = "is_false")]
    pub invalidate_all: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub changed: Vec<DocumentIdentifier>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub created: Vec<DocumentIdentifier>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub deleted: Vec<DocumentIdentifier>,
}

/// `type SnapshotRequestChangesParams struct` — describes project, file, and
/// program changes to apply while creating or updating a snapshot.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SnapshotRequestChangesParams {
    /// `OpenProjects` lists tsconfig.json files to open/load in the new snapshot.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub open_projects: Vec<DocumentIdentifier>,
    /// `CloseProjects` lists tsconfig.json files to release in the new
    /// snapshot. A project is only unloaded once every API client that opened
    /// it closes it.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub close_projects: Vec<DocumentIdentifier>,
    /// `OpenFiles` lists files to open in the new snapshot, mirroring LSP's
    /// textDocument/didOpen.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub open_files: Vec<DocumentIdentifier>,
    /// `CloseFiles` lists files to release in the new snapshot. A file is only
    /// fully closed once every API client that opened it closes it.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub close_files: Vec<DocumentIdentifier>,
    /// `CreatePrograms` describes synthetic programs to create in the snapshot.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub create_programs: Vec<CreateSnapshotProgramParams>,
    /// `ReconfigurePrograms` replaces the configuration of existing synthetic
    /// programs.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub reconfigure_programs: Vec<ReconfigureSnapshotProgramParams>,
    /// `RemovePrograms` lists synthetic project handles to remove from the
    /// snapshot.
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        serialize_with = "ser_str_vec",
        deserialize_with = "de_str_vec"
    )]
    pub remove_programs: Vec<SyntheticProjectId>,
    /// `EnsurePrograms` identifies projects whose programs should be updated
    /// if dirty, or all contained projects when true.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ensure_programs: Option<EnsurePrograms>,
}

/// `type EnsurePrograms struct { All bool; Projects []project.ID }`.
///
/// PORT: the Go struct has a custom `UnmarshalJSONFrom` (`true` → All; array →
/// Projects). Its marshal is the default struct shape — Go's untagged
/// exported fields serialize under their Go names (`All`/`Projects`).
#[derive(Clone, Debug, Default, Serialize)]
pub struct EnsurePrograms {
    #[serde(rename = "All")]
    pub all: bool,
    #[serde(rename = "Projects", serialize_with = "ser_str_vec")]
    pub projects: Vec<ProjectId>,
}

/// `func (e *EnsurePrograms) UnmarshalJSONFrom(dec *json.Decoder) error` —
/// `true` → All; array of project IDs → Projects; anything else fails with
/// the Go message.
impl<'de> Deserialize<'de> for EnsurePrograms {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        const MSG: &str = "ensurePrograms must be true or an array of project IDs";

        struct EnsureProgramsVisitor;
        impl<'de> Visitor<'de> for EnsureProgramsVisitor {
            type Value = EnsurePrograms;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("true or an array of project IDs")
            }

            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Self::Value, E> {
                if v {
                    Ok(EnsurePrograms {
                        all: true,
                        projects: Vec::new(),
                    })
                } else {
                    Err(E::custom(MSG))
                }
            }

            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                let mut projects = Vec::new();
                while let Some(id) = seq.next_element::<String>()? {
                    projects.push(ProjectId::from(id));
                }
                Ok(EnsurePrograms {
                    all: false,
                    projects,
                })
            }

            fn visit_str<E: de::Error>(self, _v: &str) -> Result<Self::Value, E> {
                Err(E::custom(MSG))
            }

            fn visit_i64<E: de::Error>(self, _v: i64) -> Result<Self::Value, E> {
                Err(E::custom(MSG))
            }

            fn visit_u64<E: de::Error>(self, _v: u64) -> Result<Self::Value, E> {
                Err(E::custom(MSG))
            }

            fn visit_f64<E: de::Error>(self, _v: f64) -> Result<Self::Value, E> {
                Err(E::custom(MSG))
            }

            fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
                Err(E::custom(MSG))
            }

            fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
                Err(E::custom(MSG))
            }

            fn visit_map<A: MapAccess<'de>>(self, _map: A) -> Result<Self::Value, A::Error> {
                Err(<A::Error as de::Error>::custom(MSG))
            }
        }

        deserializer.deserialize_any(EnsureProgramsVisitor)
    }
}

/// `type CreateSnapshotParams struct` — parameters for creating a new
/// independent snapshot. Go embeds `SnapshotRequestChangesParams` (flattened
/// on the wire).
///
/// PORT: `FileSystem *requestfilesystem.RequestFileSystem` — the Go field
/// type is the deserializable params struct; the port names it
/// `RequestFileSystemParams` (`requestfilesystem.go` splits params from the
/// built filesystem). `RequestFileSystemParams` has no `Serialize` impl, so
/// this struct is request-side only (`Deserialize`).
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateSnapshotParams {
    /// Embedded `SnapshotRequestChangesParams` — flattened like Go's
    /// anonymous field.
    #[serde(flatten)]
    pub snapshot_request_changes: SnapshotRequestChangesParams,
    /// `UserPreferences` configures language service behavior in the new snapshot.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub user_preferences: Option<UserPreferences>,
    /// `PrepareAutoImports` identifies the file whose auto-import indexes
    /// should be ready in the new snapshot.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prepare_auto_imports: Option<DocumentIdentifier>,
    /// `FileNotifications` describes host file system changes to invalidate
    /// while creating the snapshot.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file_notifications: Option<FileNotifications>,
    /// `FileSystem` supplies file contents and directory listings for the new
    /// snapshot. A full filesystem is canonical and total. A filesystem layer
    /// is checked before falling back to the base snapshot or host filesystem.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file_system: Option<RequestFileSystemParams>,
}

/// `type CreateSnapshotProgramParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateSnapshotProgramParams {
    pub root_files: Vec<DocumentIdentifier>,
    /// `CompilerOptions` is populated by the session after parsing
    /// `CompilerOptionsInput` — `json:"-"` on the wire.
    #[serde(skip)]
    pub compiler_options: CompilerOptions,
    /// `CompilerOptionsInput` — `nonnil:"true"` (always an object on the wire).
    #[serde(rename = "compilerOptions")]
    pub compiler_options_input: RawCompilerOptions,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub options: Option<CreateProgramOptions>,
}

/// `type ReconfigureSnapshotProgramParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReconfigureSnapshotProgramParams {
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub id: SyntheticProjectId,
    pub root_files: Vec<DocumentIdentifier>,
    /// `CompilerOptions` — `json:"-"`.
    #[serde(skip)]
    pub compiler_options: CompilerOptions,
    /// `CompilerOptionsInput` — `nonnil:"true"`.
    #[serde(rename = "compilerOptions")]
    pub compiler_options_input: RawCompilerOptions,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub options: Option<CreateProgramOptions>,
}

/// `type UpdateSnapshotParams struct`. Request-side only (contains
/// `CreateSnapshotParams` → `RequestFileSystemParams`).
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct UpdateSnapshotParams {
    pub snapshot: SnapshotId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub changes: Option<CreateSnapshotParams>,
}

/// `type GetCurrentLanguageServerSnapshotParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetCurrentLanguageServerSnapshotParams {
    #[serde(skip_serializing_if = "wire_id_is_zero")]
    pub base_snapshot: SnapshotId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub changes: Option<LanguageServerSnapshotChanges>,
}

/// `type LanguageServerSnapshotChanges struct` — describes API-driven changes
/// to adopt into the language server's canonical state. Go embeds
/// `SnapshotRequestChangesParams` (flattened).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct LanguageServerSnapshotChanges {
    #[serde(flatten)]
    pub snapshot_request_changes: SnapshotRequestChangesParams,
}

/// `type CreateProgramOptions struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateProgramOptions {
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub project_references: Vec<ProjectReference>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub config_file_parsing_diagnostics: Vec<DiagnosticResponse>,
    #[serde(skip_serializing_if = "wire_id_is_zero")]
    pub module_resolver: ModuleResolverId,
}

/// `ModuleResolutionFallbackResolve`.
pub const MODULE_RESOLUTION_FALLBACK_RESOLVE: ModuleResolutionFallback =
    ModuleResolutionFallback::new("resolve");
/// `ModuleResolutionFallbackUnresolved`.
pub const MODULE_RESOLUTION_FALLBACK_UNRESOLVED: ModuleResolutionFallback =
    ModuleResolutionFallback::new("unresolved");

/// `type ModuleResolutionSpec struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ModuleResolutionSpec {
    pub fallback: ModuleResolutionFallback,
    /// `Entries` — `nonnil:"true"`.
    pub entries: Vec<ModuleResolutionEntry>,
}

/// `type ModuleResolutionEntry struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ModuleResolutionEntry {
    pub module_name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub containing_directory: Option<DocumentIdentifier>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resolution_mode: Option<ResolutionMode>,
    /// `Result *StaticModuleResolution` — `nonnil:"true"`; `Option` so a
    /// missing/null result reaches the same "has no result" error Go's
    /// nil check produces.
    pub result: Option<StaticModuleResolution>,
}

/// `type StaticModuleResolution struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct StaticModuleResolution {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resolved_file_name: Option<DocumentIdentifier>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub original_path: Option<DocumentIdentifier>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub package_id: Option<PackageId>,
}

/// `type CreateModuleResolverParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateModuleResolverParams {
    pub compiler_options: CompilerOptions,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub module_resolutions: Option<ModuleResolutionSpec>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub resolve_module_name_callback: String,
}

/// `type ReleaseModuleResolverParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReleaseModuleResolverParams {
    pub resolver: ModuleResolverId,
}

/// `type ResolveModuleNameParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ResolveModuleNameParams {
    #[serde(skip_serializing_if = "wire_id_is_zero")]
    pub snapshot: SnapshotId,
    #[serde(skip_serializing_if = "is_zero_u64")]
    pub in_progress_snapshot: u64,
    pub resolver: ModuleResolverId,
    pub module_name: String,
    pub containing_directory: DocumentIdentifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resolution_mode: Option<ResolutionMode>,
}

/// `type ResolveModuleNameCallbackParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ResolveModuleNameCallbackParams {
    pub module_name: String,
    pub containing_directory: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resolution_mode: Option<ResolutionMode>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub snapshot: Option<SnapshotId>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub in_progress_snapshot: Option<u64>,
}

/// `type ResolveModuleNameResult struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ResolveModuleNameResult {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resolved_module: Option<ResolvedModule>,
    /// `Trace` is provided when compilerOptions.traceResolution is true.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub trace: Vec<String>,
}

/// `type ProjectFileChanges struct` — describes what source files changed
/// within a single project.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ProjectFileChanges {
    /// `ChangedFiles` lists source file paths whose content differs.
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        serialize_with = "ser_str_vec",
        deserialize_with = "de_str_vec"
    )]
    pub changed_files: Vec<PathKey>,
    /// `DeletedFiles` lists source file paths removed from the project's program.
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        serialize_with = "ser_str_vec",
        deserialize_with = "de_str_vec"
    )]
    pub deleted_files: Vec<PathKey>,
}

/// `type SnapshotChanges struct` — describes what changed between a response
/// base and a new snapshot. Changes are reported per-project so clients can
/// track cache refs at the (snapshot, project) level.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SnapshotChanges {
    /// `ChangedProjects` maps project handles to the file changes within that
    /// project. Projects not listed here (and not in RemovedProjects) are
    /// unchanged.
    #[serde(
        skip_serializing_if = "changed_projects_is_empty",
        serialize_with = "ser_id_map",
        deserialize_with = "de_id_map"
    )]
    pub changed_projects: FxHashMap<ProjectId, ProjectFileChanges>,
    /// `RemovedProjects` lists project handles that were present in the
    /// previous snapshot but absent from the new one.
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        serialize_with = "ser_str_vec",
        deserialize_with = "de_str_vec"
    )]
    pub removed_projects: Vec<ProjectId>,
}

/// `type CreateSnapshotResponse struct` — returned by createSnapshot.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateSnapshotResponse {
    /// `Snapshot` is the handle for the newly created snapshot.
    pub snapshot: SnapshotId,
    /// `Projects` contains all projects when no response base was supplied, or
    /// only projects added or replaced relative to that base.
    /// `nonnil:"true"`.
    pub projects: Vec<ProjectResponse>,
    /// `Changes` describes source file differences from the response base.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub changes: Option<SnapshotChanges>,
    /// `Operation` describes results correlated with the request that
    /// produced the snapshot. `nonnil:"true"` (nil → zero struct `{}`).
    #[serde(serialize_with = "ser_nonnil")]
    pub operation: Option<SnapshotOperationResponse>,
}

/// `type SnapshotOperationResponse struct` — both fields use
/// `omitzero` on the Go pointer (nil → key absent).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SnapshotOperationResponse {
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "ser_str_opt_vec",
        deserialize_with = "de_str_opt_vec"
    )]
    pub created_programs: Option<Vec<SyntheticProjectId>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub opened_files: Option<Vec<OpenedFileOperationResult>>,
}

/// `type OpenedFileOperationResult struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct OpenedFileOperationResult {
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
}

// ---------------------------------------------------------------------------
// Config-file parse / command-line params
// ---------------------------------------------------------------------------

/// `type ParseConfigFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ParseConfigFileParams {
    pub file: DocumentIdentifier,
}

/// `type ParseCommandLineParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ParseCommandLineParams {
    pub command_line: Vec<String>,
}

/// `type ReadConfigFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReadConfigFileParams {
    pub file: DocumentIdentifier,
}

/// `type ParseJsonConfigFileContentParams struct`. Request-side only
/// (`packagejson.JSONValue` has no `Serialize` impl in the port, matching
/// Go's `UnmarshalJSONFrom`-only JSONValue).
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ParseJsonConfigFileContentParams {
    #[serde(rename = "json")]
    pub json: JSONValue,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub config_directory: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub config_file_name: Option<DocumentIdentifier>,
}

/// `func jsonValueToAny(value packagejson.JSONValue) any`.
///
/// PORT: Go's `any` carrier (nil/string/float64/bool/[]any/*OrderedMap) is
/// `tsc_tsoptions::value::Value` — the port's closed `any` enum with the same
/// shapes (`Value::Map` is `*OrderedMap[string, any]`). Go's `default` panic
/// arm is unreachable (Rust matches the closed `JSONValueType` enum).
pub fn json_value_to_any(value: &JSONValue) -> TsValue {
    match value.type_ {
        JSONValueType::NotPresent | JSONValueType::Null => TsValue::Null,
        JSONValueType::String => match &value.value {
            JSONValueData::String(s) => TsValue::Str(s.clone()),
            _ => TsValue::Null,
        },
        JSONValueType::Number => match &value.value {
            JSONValueData::Number(n) => TsValue::Float(*n),
            _ => TsValue::Null,
        },
        JSONValueType::Boolean => match &value.value {
            JSONValueData::Boolean(b) => TsValue::Bool(*b),
            _ => TsValue::Null,
        },
        JSONValueType::Array => {
            let array = value.as_array();
            TsValue::List(array.iter().map(json_value_to_any).collect())
        }
        JSONValueType::Object => {
            let object = value.as_object();
            let mut result = OrderedMap::with_size_hint(object.size());
            for (key, child) in object.entries() {
                result.set(key.clone(), json_value_to_any(child));
            }
            TsValue::Map(result)
        }
    }
}

// ---------------------------------------------------------------------------
// Transpile / source-file params
// ---------------------------------------------------------------------------

/// `type TranspileOptions struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TranspileOptions {
    /// `CompilerOptions` — `json:"-"` (populated by the session after parsing
    /// `CompilerOptionsInput`).
    #[serde(skip)]
    pub compiler_options: Option<CompilerOptions>,
    #[serde(rename = "compilerOptions", skip_serializing_if = "Option::is_none")]
    pub compiler_options_input: Option<RawCompilerOptions>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub file_name: String,
    #[serde(skip_serializing_if = "is_false")]
    pub report_diagnostics: bool,
}

/// `type CreateSourceFileOptions struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateSourceFileOptions {
    /// `core.ScriptKind` serializes as its int value in Go.
    #[serde(
        skip_serializing_if = "script_kind_is_unknown",
        serialize_with = "ser_int",
        deserialize_with = "de_int"
    )]
    pub script_kind: ScriptKind,
}

/// `type CreateSourceFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateSourceFileParams {
    pub file_name: String,
    pub source_text: String,
    pub options: CreateSourceFileOptions,
}

/// `type CreateSourceFileFromFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateSourceFileFromFileParams {
    pub file_name: String,
    pub options: CreateSourceFileOptions,
}

/// `type TranspileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TranspileParams {
    pub input: String,
    pub options: TranspileOptions,
}

/// `type TranspileFromFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TranspileFromFileParams {
    pub file_name: String,
    pub options: TranspileOptions,
}

/// `type TranspileOutputResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TranspileOutputResponse {
    pub output_text: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<DiagnosticResponse>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub source_map_text: String,
}

// ---------------------------------------------------------------------------
// Batch requests
// ---------------------------------------------------------------------------

/// `type BatchRequestsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BatchRequestsParams {
    pub requests: Vec<BatchRequest>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub continuation_token: String,
    #[serde(skip_serializing_if = "is_zero_i64")]
    pub max_response_bytes_per_page: i64,
}

/// `type BatchRequest struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BatchRequest {
    pub method: Method,
    /// `json.Value` — pre-encoded raw JSON params.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<json::Value>,
}

/// `type BatchRequestsResponse struct` — `encodedResponses` carries
/// pre-encoded payloads that bypass re-marshal.
///
/// PORT: `MarshalJSONTo` is the custom `Serialize` below (a `{"responses":[]}`
/// object whose responses are either the pre-encoded `encoded_responses` raw
/// payloads or the serialized `responses` list, plus `continuationToken` when
/// non-empty). Go's unexported `encodedResponses` gets `#[serde(skip)]` on
/// the derived `Deserialize`.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BatchRequestsResponse {
    /// `Responses` — `nonnil:"true"`.
    pub responses: Vec<BatchResponse>,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub continuation_token: String,
    /// `encodedResponses` — unexported in Go; pre-encoded `json.Value`s.
    #[serde(skip)]
    pub encoded_responses: Option<Vec<json::Value>>,
}

/// `func (r *BatchRequestsResponse) MarshalJSONTo(enc *json.Encoder) error`.
impl Serialize for BatchRequestsResponse {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        let mut map = serializer.serialize_map(None)?;
        match &self.encoded_responses {
            // `r.encodedResponses != nil` — write each pre-encoded payload.
            Some(encoded) => map.serialize_entry("responses", encoded)?,
            None => map.serialize_entry("responses", &self.responses)?,
        }
        if !self.continuation_token.is_empty() {
            map.serialize_entry("continuationToken", &self.continuation_token)?;
        }
        map.end()
    }
}

/// `type BatchResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BatchResponse {
    pub method: Method,
    /// `Result any` — arbitrary per-method result payload; `null` when unset
    /// (Go `any` nil marshals as `null`, matching `serde_json::Value::Null`).
    pub result: serde_json::Value,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub error: String,
}

// ---------------------------------------------------------------------------
// Release / source-file lease params
// ---------------------------------------------------------------------------

/// `type ReleaseParams struct` — parameters for the release method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReleaseParams {
    pub snapshot: SnapshotId,
}

/// `type ReleaseSourceFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReleaseSourceFileParams {
    pub lease: SourceFileLeaseId,
}

/// `type SourceFileDescriptor struct`.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SourceFileDescriptor {
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub file_name: RootedFilePath,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub path: PathKey,
    pub content_hash: String,
    pub parse_options_key: String,
    /// `core.ScriptKind` serializes as its int value in Go.
    #[serde(serialize_with = "ser_int", deserialize_with = "de_int")]
    pub script_kind: ScriptKind,
    pub node_id: String,
}

/// `type RetainSourceFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct RetainSourceFileParams {
    pub file: SourceFileDescriptor,
}

/// `type RetainSourceFileResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct RetainSourceFileResponse {
    pub lease: SourceFileLeaseId,
}

/// `type GetCachedSourceFileParams struct` — addresses an ordinary cached
/// source file by its complete identity, independent of any snapshot or lease.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetCachedSourceFileParams {
    pub file: SourceFileDescriptor,
}

/// `type GetSymbolOfDeclarationParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolOfDeclarationParams {
    pub file: SourceFileDescriptor,
    /// `Index uint32`.
    pub index: u32,
}

/// `type ProfileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ProfileParams {
    pub dir: String,
}

/// `type ProfileResult struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ProfileResult {
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub file: RootedFilePath,
}

// ---------------------------------------------------------------------------
// Build orchestrator params/responses
// ---------------------------------------------------------------------------

/// `type CreateBuildOrchestratorParams struct` — Go embeds `*core.BuildOptions`
/// and `*core.CompilerOptions` with explicit tags, so they are named fields
/// (`buildOptions`/`compilerOptions`), not flattened.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateBuildOrchestratorParams {
    pub root_names: Vec<String>,
    #[serde(
        skip_serializing_if = "str_wrapped_is_empty",
        serialize_with = "ser_str",
        deserialize_with = "de_str"
    )]
    pub cwd: RootedDirectoryPath,
    /// `*core.BuildOptions` — only a subset of these options are exposed in the API.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build_options: Option<BuildOptions>,
    /// `*core.CompilerOptions`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiler_options: Option<CompilerOptions>,
}

/// `type CreateBuildOrchestratorResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CreateBuildOrchestratorResponse {
    #[serde(rename = "buildOrchestratorID")]
    pub build_orchestrator_id: BuildOrchestratorId,
}

/// `type DisposeBuildOrchestratorParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct DisposeBuildOrchestratorParams {
    #[serde(rename = "buildOrchestratorID")]
    pub build_orchestrator_id: BuildOrchestratorId,
}

/// `type BuildParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BuildParams {
    #[serde(rename = "buildOrchestratorID")]
    pub build_orchestrator_id: BuildOrchestratorId,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub project: String,
}

/// `type BuildResponse struct`.
///
/// PORT: `Statistics` has no `Clone`/`Debug` impls in `tsc-execute`
/// (mirroring Go, where only the exported fields matter), so this struct
/// derives only serde traits.
#[derive(Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct BuildResponse {
    /// `tsc.ExitStatus` serializes as its int value in Go.
    #[serde(
        default = "exit_status_default",
        serialize_with = "ser_int",
        deserialize_with = "de_int"
    )]
    pub status: ExitStatus,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<DiagnosticResponse>,
    /// `tsc.Statistics` serializes only its exported fields (Go names).
    #[serde(
        serialize_with = "ser_statistics",
        deserialize_with = "de_statistics"
    )]
    pub statistics: Statistics,
}

/// `type CleanBuildParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CleanBuildParams {
    #[serde(rename = "buildOrchestratorID")]
    pub build_orchestrator_id: BuildOrchestratorId,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub project: String,
}

/// `type CleanBuildResponse struct` — see `BuildResponse` for the
/// `Statistics`-driven derive restrictions.
#[derive(Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CleanBuildResponse {
    #[serde(
        default = "exit_status_default",
        serialize_with = "ser_int",
        deserialize_with = "de_int"
    )]
    pub status: ExitStatus,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<DiagnosticResponse>,
    #[serde(
        serialize_with = "ser_statistics",
        deserialize_with = "de_statistics"
    )]
    pub statistics: Statistics,
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        serialize_with = "ser_str_vec",
        deserialize_with = "de_str_vec"
    )]
    pub files_deleted: Vec<RootedFilePath>,
}

/// `type BuildOrchestrator struct` — the three Go `func` fields become boxed
/// `Fn` trait objects. Not serializable in Go or Rust.
pub struct BuildOrchestrator {
    /// `Build func(project string) tsc.ExitStatus`.
    pub build: Box<dyn Fn(&str) -> ExitStatus + Send>,
    /// `BuildReferences func(project string) tsc.ExitStatus`.
    pub build_references: Box<dyn Fn(&str) -> ExitStatus + Send>,
    /// `CleanReferences func(project string) tsc.ExitStatus`.
    pub clean_references: Box<dyn Fn(&str) -> ExitStatus + Send>,
}

// ---------------------------------------------------------------------------
// ConfigFileResponse / ReadConfigFileResponse / ProjectResponse
// ---------------------------------------------------------------------------

/// `type ConfigFileResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ConfigFileResponse {
    /// `FileNames` — `nonnil:"true"`.
    #[serde(serialize_with = "ser_str_vec", deserialize_with = "de_str_vec")]
    pub file_names: Vec<RootedFilePath>,
    /// `Options` — `nonnil:"true"` (nil → `{}`).
    #[serde(serialize_with = "ser_nonnil")]
    pub options: Option<CompilerOptions>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build_options: Option<BuildOptions>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub project_references: Vec<ProjectReference>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_acquisition: Option<TypeAcquisition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compile_on_save: Option<bool>,
    /// `Raw any` — the parsed config's raw value; the port's `any` carrier is
    /// `tsc_tsoptions::value::Value`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw: Option<TsValue>,
    /// `Errors` — `nonnil:"true"`.
    pub errors: Vec<DiagnosticResponse>,
}

/// `type ReadConfigFileResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReadConfigFileResponse {
    /// `Config any` — arbitrary config payload.
    pub config: serde_json::Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<DiagnosticResponse>,
}

/// `type GetDefaultProjectForFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetDefaultProjectForFileParams {
    pub snapshot: SnapshotId,
    pub file: DocumentIdentifier,
}

/// `type ProjectResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ProjectResponse {
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub id: ProjectId,
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "ser_str_opt",
        deserialize_with = "de_str_opt"
    )]
    pub config_file_name: Option<RootedFilePath>,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub current_directory: RootedDirectoryPath,
    pub dirty: bool,
    /// `ParsedCommandLine` — `nonnil:"true"` (nil → zero-value object).
    #[serde(serialize_with = "ser_nonnil")]
    pub parsed_command_line: Option<ConfigFileResponse>,
    /// Deprecated: Use parsedCommandLine.fileNames. `nonnil:"true"`.
    #[serde(serialize_with = "ser_str_vec", deserialize_with = "de_str_vec")]
    pub root_files: Vec<RootedFilePath>,
    /// Deprecated: Use parsedCommandLine.options. `nonnil:"true"`.
    #[serde(serialize_with = "ser_nonnil")]
    pub compiler_options: Option<CompilerOptions>,
}

/// `func NewConfigFileResponse(parsedCommandLine *tsoptions.ParsedCommandLine) *ConfigFileResponse`.
///
/// PORT: `nodes` supplies the AST arena that `ASTDiagnostic` resolves
/// diagnostic files through (Go diagnostics carry live `*ast.SourceFile`
/// pointers; here the arena is explicit). `None` mirrors Go's nil → nil.
/// Go does not populate `BuildOptions` here — it stays `None`.
pub fn new_config_file_response(
    parsed_command_line: Option<&ParsedCommandLine>,
    nodes: &[Node],
) -> Option<ConfigFileResponse> {
    let parsed_command_line = parsed_command_line?;
    let mut compile_on_save = parsed_command_line.compile_on_save;
    if compile_on_save.is_none() {
        // `rawConfig.GetOrZero("compileOnSave").(bool)` — Go's `any`
        // assertion on the OrderedMap value.
        if let Some(TsValue::Map(raw_config)) = &parsed_command_line.raw {
            if let Some(TsValue::Bool(value)) = raw_config.get("compileOnSave") {
                compile_on_save = Some(*value);
            }
        }
    }
    let compiler_options = parsed_command_line.compiler_options().cloned();
    // Go's `errors == nil` → `[]` is an empty Vec here (serializes `[]`
    // either way).
    let errors = {
        let diags = parsed_command_line.errors.lock().unwrap();
        new_diagnostic_responses(&diags, nodes)
    };
    Some(ConfigFileResponse {
        file_names: parsed_command_line.file_names().to_vec(),
        options: compiler_options,
        project_references: parsed_command_line.project_references().to_vec(),
        type_acquisition: parsed_command_line.type_acquisition().cloned(),
        compile_on_save,
        raw: parsed_command_line.raw.clone(),
        errors,
        ..Default::default()
    })
}

/// `func NewProjectResponse(p *project.Project) *ProjectResponse`.
///
/// PORT: panics on `p.command_line == nil` like Go (`NewProjectResponse
/// called with unloaded project`); `nodes` feeds the diagnostic conversion —
/// see `new_config_file_response`.
pub fn new_project_response(p: &Project, nodes: &[Node]) -> ProjectResponse {
    let Some(command_line) = p.command_line.as_ref() else {
        panic!("NewProjectResponse called with unloaded project");
    };
    let config_file_name =
        (p.kind == ProjectKind::Configured).then(|| p.config_file_name().clone());
    ProjectResponse {
        id: p.id().clone(),
        config_file_name,
        current_directory: p.current_directory(),
        dirty: p.is_dirty(),
        parsed_command_line: new_config_file_response(Some(command_line.as_ref()), nodes),
        root_files: command_line.file_names().to_vec(),
        compiler_options: command_line.compiler_options().cloned(),
    }
}

// ---------------------------------------------------------------------------
// Symbol-position / symbol-location params and responses
// ---------------------------------------------------------------------------

/// `type GetSymbolAtPositionParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolAtPositionParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub position: u32,
}

/// `type GetSymbolsAtPositionsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolsAtPositionsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub positions: Vec<u32>,
}

/// `type GetSymbolOfSourceFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolOfSourceFileParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
}

/// `type GetSymbolsOfSourceFilesParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolsOfSourceFilesParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub files: Vec<DocumentIdentifier>,
}

/// `type GetSymbolAtLocationParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolAtLocationParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
}

/// `type GetSymbolsAtLocationsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolsAtLocationsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub locations: Vec<NodeHandle>,
}

/// `type SymbolResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SymbolResponse {
    pub reference: SymbolReference,
    pub name: String,
    pub flags: u32,
    pub check_flags: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub declarations: Option<Vec<NodeHandle>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value_declaration: Option<NodeHandle>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<CompactSymbolReference>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub export_symbol: Option<CompactSymbolReference>,
}

/// `type SymbolOwnerKind uint32` — serializes as its uint32 value; the enum
/// shape gives the session `SymbolOwnerKind::File`/`::Snapshot` variants
/// (and `SYMBOL_OWNER_KIND_*` const patterns).
///
/// PORT: Go's `uint32` accepts any value on unmarshal; the Rust enum is
/// closed and rejects out-of-range values.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum SymbolOwnerKind {
    /// `SymbolOwnerKindFile`.
    #[default]
    File = 0,
    /// `SymbolOwnerKindSnapshot`.
    Snapshot = 1,
}

/// `SymbolOwnerKindFile`.
pub const SYMBOL_OWNER_KIND_FILE: SymbolOwnerKind = SymbolOwnerKind::File;
/// `SymbolOwnerKindSnapshot`.
pub const SYMBOL_OWNER_KIND_SNAPSHOT: SymbolOwnerKind = SymbolOwnerKind::Snapshot;

impl Serialize for SymbolOwnerKind {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_u32(*self as u32)
    }
}
impl<'de> Deserialize<'de> for SymbolOwnerKind {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        match u64::deserialize(d)? {
            0 => Ok(SymbolOwnerKind::File),
            1 => Ok(SymbolOwnerKind::Snapshot),
            v => Err(de::Error::custom(format!("unknown SymbolOwnerKind {v}"))),
        }
    }
}

/// `type SymbolOwner struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SymbolOwner {
    pub kind: SymbolOwnerKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<SourceFileDescriptor>,
    /// `json:"snapshot,omitzero"` — omitted when zero.
    #[serde(skip_serializing_if = "wire_id_is_zero")]
    pub snapshot: SnapshotId,
    /// `json:"project,omitempty"` — empty ID omitted.
    #[serde(
        skip_serializing_if = "str_wrapped_is_empty",
        serialize_with = "ser_str",
        deserialize_with = "de_str"
    )]
    pub project: ProjectId,
}

/// `type SymbolReference struct` — identifies a symbol and its
/// server-resolvable owner. Go embeds `SymbolOwner` (flattened on the wire).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SymbolReference {
    /// Embedded `SymbolOwner` — flattened like Go's anonymous field.
    #[serde(flatten)]
    pub owner: SymbolOwner,
    /// `Id SymbolID` — Go's field name `Id` → `id` on the wire.
    pub id: SymbolId,
}

/// `type CompactSymbolReference struct` — embedded in other responses.
/// Identifies a cached symbol without repeating its owning file's full
/// descriptor: `File` is the owning source file's node ID, or empty for a
/// symbol owned by the response's snapshot.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CompactSymbolReference {
    pub id: SymbolId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
}

/// `type GetTypeOfSymbolParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypeOfSymbolParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub symbol: SymbolReference,
}

/// `type GetTypesOfSymbolsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypesOfSymbolsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub symbols: Vec<SymbolReference>,
}

// ---------------------------------------------------------------------------
// TypeResponse + newTypeResponse
// ---------------------------------------------------------------------------

/// `type TypeResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TypeResponse {
    pub id: TypeId,
    pub flags: u32,
    #[serde(skip_serializing_if = "is_zero_u32")]
    pub object_flags: u32,
    #[serde(skip_serializing_if = "is_false")]
    pub is_tuple_type: bool,

    /// `Value` is literal type data. BigInt literals are encoded as signed
    /// decimal strings because JSON cannot represent bigint; absent values
    /// are null.
    pub value: serde_json::Value,

    /// ObjectType / TypeReference / StringMappingType / IndexType target.
    /// `omitzero` — `Some(TypeId(0))` serializes as absent.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub target: Option<TypeId>,

    /// InterfaceType type parameters.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub type_parameters: Vec<TypeId>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub outer_type_parameters: Vec<TypeId>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub local_type_parameters: Vec<TypeId>,

    /// TupleType data.
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        serialize_with = "ser_int_vec",
        deserialize_with = "de_int_vec"
    )]
    pub element_flags: Vec<ElementFlags>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fixed_length: Option<i64>,
    #[serde(rename = "readonly", skip_serializing_if = "Option::is_none")]
    pub tuple_readonly: Option<bool>,
    /// Go `[]NodeHandle` elements; the session emits `null` for label-less
    /// elements (Go's empty `NodeHandle("")` would also render as `""` — the
    /// `null` is the session's own port note).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub labeled_element_declarations: Option<Vec<Option<NodeHandle>>>,

    /// IndexedAccessType data — `omitzero`.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub object_type: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub index_type: Option<TypeId>,

    /// ConditionalType data — `omitzero`.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub check_type: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub extends_type: Option<TypeId>,

    /// SubstitutionType data — `omitzero`.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub base_type: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub subst_constraint: Option<TypeId>,

    /// MappedType data — `omitzero`.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub type_parameter: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub constraint_type: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub name_type: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub template_type: Option<TypeId>,

    /// TemplateLiteralType text segments.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub texts: Vec<String>,

    /// FreshableType data (LiteralType and computed enum types) — `omitzero`.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub fresh_type: Option<TypeId>,
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub regular_type: Option<TypeId>,

    /// TypeParameter data.
    #[serde(skip_serializing_if = "is_false")]
    pub is_this_type: bool,

    /// InterfaceType data — `omitzero`.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub this_type: Option<TypeId>,

    /// IntrinsicType data.
    #[serde(skip_serializing_if = "String::is_empty")]
    pub intrinsic_name: String,

    /// TypeAlias data.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub alias_type_arguments: Vec<TypeId>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub alias_symbol: Option<CompactSymbolReference>,

    /// Symbol associated with structured types.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<CompactSymbolReference>,
}

/// `func newTypeResponse(t *checker.Type, id TypeID) *TypeResponse`.
///
/// PORT: `*checker.Type` → `(types, t)` arena + `TypeId`; the arena is also
/// needed for `is_tuple_type`/`is_tuple_type_target` (free functions taking
/// `(&TypeArena, TypeId)` here). The Go `switch` on `t.Flags()` is exclusive
/// top-down — preserved as an if/else-if chain in the same order.
pub fn new_type_response(types: &TypeArena, t: CheckerTypeId, id: TypeId) -> TypeResponse {
    let t_ref = types.get_ref(t);
    let mut resp = TypeResponse {
        id,
        flags: t_ref.flags().0,
        ..Default::default()
    };

    if let Some(alias) = t_ref.alias() {
        resp.alias_type_arguments = type_handles(alias.type_arguments());
    }

    let flags = t_ref.flags();
    if flags.intersects(TypeFlags::FRESHABLE) {
        let lit = t_ref.as_literal_type();
        if flags.intersects(TypeFlags::LITERAL) {
            resp.value = literal_value_to_json(lit.value());
        }
        if let Some(fresh) = lit.fresh_type() {
            resp.fresh_type = Some(TypeId(fresh.0 as u64));
        }
        if let Some(regular) = lit.regular_type() {
            resp.regular_type = Some(TypeId(regular.0 as u64));
        }
    } else if flags.intersects(TypeFlags::OBJECT) {
        resp.object_flags = t_ref.object_flags().0;
        resp.is_tuple_type = is_tuple_type(types, t);
        let object_flags = t_ref.object_flags();
        if object_flags.intersects(ObjectFlags::REFERENCE) {
            if is_tuple_type_target(types, t) {
                let tuple = t_ref.as_tuple_type();
                resp.element_flags = tuple.element_flags();
                resp.fixed_length = Some(tuple.fixed_length() as i64);
                resp.tuple_readonly = Some(tuple.is_readonly());
            }
            // `ref := t.AsTypeReference(); ref.Target()` — `Type::target()`
            // dispatches on the object type's structured target.
            if let Some(target) = t_ref.target() {
                resp.target = Some(TypeId(target.0 as u64));
            }
        }
        if object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE) {
            if let Some(iface) = t_ref.as_interface_type() {
                resp.type_parameters = type_handles(iface.type_parameters());
                resp.outer_type_parameters = type_handles(iface.outer_type_parameters());
                resp.local_type_parameters = type_handles(iface.local_type_parameters());
                if let Some(this_type) = iface.this_type() {
                    resp.this_type = Some(TypeId(this_type.0 as u64));
                }
            }
        }
    } else if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
        // types omitted; fetched via separate request
    } else if flags.intersects(TypeFlags::INDEX) {
        if let Some(target) = t_ref.as_index_type().target() {
            resp.target = Some(TypeId(target.0 as u64));
        }
    } else if flags.intersects(TypeFlags::INDEXED_ACCESS) {
        let data = t_ref.as_indexed_access_type();
        resp.object_type = data.object_type().map(|v| TypeId(v.0 as u64));
        resp.index_type = data.index_type().map(|v| TypeId(v.0 as u64));
    } else if flags.intersects(TypeFlags::CONDITIONAL) {
        let data = t_ref.as_conditional_type();
        resp.check_type = data.check_type().map(|v| TypeId(v.0 as u64));
        resp.extends_type = data.extends_type().map(|v| TypeId(v.0 as u64));
    } else if flags.intersects(TypeFlags::SUBSTITUTION) {
        let data = t_ref.as_substitution_type();
        resp.base_type = data.base_type().map(|v| TypeId(v.0 as u64));
        resp.subst_constraint = data.subst_constraint().map(|v| TypeId(v.0 as u64));
    } else if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
        let tl = t_ref.as_template_literal_type();
        resp.texts = tl.texts().to_vec();
        // types omitted; fetched via separate request
    } else if flags.intersects(TypeFlags::STRING_MAPPING) {
        if let Some(target) = t_ref.as_string_mapping_type().target() {
            resp.target = Some(TypeId(target.0 as u64));
        }
    } else if flags.intersects(TypeFlags::TYPE_PARAMETER) {
        resp.is_this_type = t_ref.as_type_parameter().is_this_type();
    } else if flags.intersects(TypeFlags::INTRINSIC) {
        resp.intrinsic_name = t_ref.as_intrinsic_type().intrinsic_name().to_string();
    }

    resp
}

/// `func typeHandles(types []*checker.Type) []TypeID`.
///
/// PORT: takes `&[TypeId]` (the arena ids the checker sub-objects return);
/// an empty slice produces an empty Vec, which `skip_serializing_if` omits
/// like Go's nil slice.
fn type_handles(types: &[CheckerTypeId]) -> Vec<TypeId> {
    types.iter().map(|t| TypeId(t.0 as u64)).collect()
}

/// `func literalValueToJSON(value any) any`.
///
/// PORT: Go's `any` (string/jsnum.Number/bool/jsnum.PseudoBigInt/nil) is the
/// port's `tsc_evaluator::Value` enum; `nil` is `Option::None`. Returns
/// `serde_json::Value` for the `any` response field.
pub fn literal_value_to_json(value: Option<&EvaluatorValue>) -> serde_json::Value {
    match value {
        Some(EvaluatorValue::String(s)) => serde_json::Value::String(s.clone()),
        Some(EvaluatorValue::Number(n)) => {
            if n.is_inf() {
                return serde_json::Value::String(
                    if n.0 > 0.0 { "+Infinity" } else { "-Infinity" }.to_string(),
                );
            }
            if n.is_nan() {
                return serde_json::Value::String("NaN".to_string());
            }
            serde_json::Value::from(n.0)
        }
        Some(EvaluatorValue::Bool(b)) => serde_json::Value::Bool(*b),
        Some(EvaluatorValue::PseudoBigInt(v)) => {
            // Encode bigint literals as a signed decimal string; the API
            // client decodes this back into a real bigint. JSON has no bigint.
            serde_json::Value::String(v.string())
        }
        None => serde_json::Value::Null,
    }
}

/// `type ConstantValueResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ConstantValueResponse {
    pub is_number: bool,
    /// `Value any` — `null` when unset.
    pub value: serde_json::Value,
}

/// `type SignatureResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SignatureResponse {
    pub id: SignatureId,
    pub flags: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub declaration: Option<NodeHandle>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_parameters: Option<Vec<TypeId>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parameters: Option<Vec<CompactSymbolReference>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub this_parameter: Option<CompactSymbolReference>,
    /// `omitzero` — `Some(SignatureId(0))` serializes as absent.
    #[serde(skip_serializing_if = "opt_wire_id_is_zero")]
    pub target: Option<SignatureId>,
}

// ---------------------------------------------------------------------------
// Source-file / resolution params and responses
// ---------------------------------------------------------------------------

/// `type GetSourceFileParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSourceFileParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
}

/// `type GetSourceFileNamesParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSourceFileNamesParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
}

/// `type GetModeForUsageLocationParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetModeForUsageLocationParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub usage: NodeHandle,
}

/// `type GetModeForResolutionAtIndexParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetModeForResolutionAtIndexParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    /// `Index int`.
    pub index: i64,
}

/// `type GetResolvedModuleParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetResolvedModuleParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub module_name: String,
    /// `core.ResolutionMode` — a `ModuleKind` serializing as its int value.
    pub mode: ResolutionMode,
}

/// `type GetResolvedModuleFromModuleSpecifierParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetResolvedModuleFromModuleSpecifierParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub module_specifier: NodeHandle,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_file: Option<DocumentIdentifier>,
}

/// `type GetResolvedTypeReferenceDirectiveParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetResolvedTypeReferenceDirectiveParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub type_directive_name: String,
    /// `core.ResolutionMode`.
    pub mode: ResolutionMode,
}

/// `type GetResolvedTypeReferenceDirectiveFromReferenceParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetResolvedTypeReferenceDirectiveFromReferenceParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub source_file: DocumentIdentifier,
    pub type_directive_name: String,
    /// `core.ResolutionMode`.
    pub resolution_mode: ResolutionMode,
}

/// `type PackageId struct` — API response package id (distinct from
/// `module.PackageId`; see `new_package_id`).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct PackageId {
    pub name: String,
    pub sub_module_name: String,
    pub version: String,
    pub peer_dependencies: String,
}

/// `func NewPackageId(packageID module.PackageId) *PackageId`.
pub fn new_package_id(package_id: &ModulePackageId) -> Option<PackageId> {
    if package_id.name.is_empty() {
        return None;
    }
    Some(PackageId {
        name: package_id.name.clone(),
        sub_module_name: package_id.sub_module_name.clone(),
        version: package_id.version.clone(),
        peer_dependencies: package_id.peer_dependencies.clone(),
    })
}

/// `type ResolvedModule struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ResolvedModule {
    pub resolved_file_name: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub original_path: String,
    pub extension: String,
    #[serde(skip_serializing_if = "is_false")]
    pub resolved_using_ts_extension: bool,
    #[serde(skip_serializing_if = "is_false")]
    pub resolved_using_extra_extensions: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub package_id: Option<PackageId>,
    #[serde(skip_serializing_if = "is_false")]
    pub is_external_library_import: bool,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub alternate_result: String,
}

/// `type ResolvedTypeReferenceDirective struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ResolvedTypeReferenceDirective {
    pub primary: bool,
    pub resolved_file_name: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub original_path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub package_id: Option<PackageId>,
    #[serde(skip_serializing_if = "is_false")]
    pub is_external_library_import: bool,
}

/// `type SourceFileMetadata struct` — program-stored metadata about a single
/// source file.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SourceFileMetadata {
    pub is_default_library: bool,
    pub is_from_external_library: bool,
    pub package_json_type: String,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub package_json_directory: RootedDirectoryPath,
    /// `core.ResolutionMode`.
    pub implied_node_format: ResolutionMode,
}

// ---------------------------------------------------------------------------
// Scope / property / checker param structs
// ---------------------------------------------------------------------------

/// `type ResolveNameParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ResolveNameParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub name: String,
    /// Optional: node handle for location context.
    #[serde(skip_serializing_if = "node_handle_is_empty")]
    pub location: NodeHandle,
    /// Optional: file for location context (alternative to Location).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<DocumentIdentifier>,
    /// Optional: position in file for location context (with File).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub position: Option<u32>,
    /// `Meaning` — SymbolFlags for what kind of symbol to find.
    pub meaning: u32,
    /// Whether to exclude global symbols.
    #[serde(skip_serializing_if = "is_false")]
    pub exclude_globals: bool,
}

/// `type GetSymbolsInScopeParams struct` — parameters for getSymbolsInScope,
/// which returns all symbols visible at a given location.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolsInScopeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    /// Optional: node handle for location context.
    #[serde(skip_serializing_if = "node_handle_is_empty")]
    pub location: NodeHandle,
    /// Optional: file for location context (alternative to Location).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<DocumentIdentifier>,
    /// Optional: position in file for location context (with File).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub position: Option<u32>,
    /// `Meaning` — SymbolFlags for what kind of symbols to find.
    pub meaning: u32,
}

/// `type GetTypePropertyParams struct` — used for all type sub-property
/// endpoints.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypePropertyParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    /// `json:"objectId"`.
    #[serde(rename = "objectId")]
    pub r#type: TypeId,
}

/// `type GetSymbolPropertyParams struct` — used for all symbol sub-property
/// endpoints.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSymbolPropertyParams {
    pub symbol: SymbolReference,
}

/// `type GetSignaturePropertyParams struct` — used for all signature
/// sub-property endpoints.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSignaturePropertyParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    /// `json:"objectId"`.
    #[serde(rename = "objectId")]
    pub signature: SignatureId,
}

/// `type GetContextualTypeParams struct` — returns the contextual type for a node.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetContextualTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
}

/// `type GetContextualTypeForArgumentParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetContextualTypeForArgumentParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
    /// `Index int32`.
    pub index: i32,
}

/// `type GetTypeOfSymbolAtLocationParams struct` — returns the narrowed type
/// of a symbol at a specific location.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypeOfSymbolAtLocationParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub symbol: SymbolReference,
    pub location: NodeHandle,
}

/// `type GetReferencesToSymbolInFileParams struct` — parameters for the
/// getReferencesToSymbolInFile method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetReferencesToSymbolInFileParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub symbol: SymbolReference,
}

/// `type GetReferencedSymbolsForNodeParams struct` — parameters for the
/// getReferencedSymbolsForNode method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetReferencedSymbolsForNodeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub node: NodeHandle,
    /// `Position int`.
    pub position: i64,
}

/// `type ReferencedSymbolEntry struct` — a symbol definition and its references.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ReferencedSymbolEntry {
    pub definition: NodeHandle,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<SymbolResponse>,
    /// `References` — `nonnil:"true"`.
    pub references: Vec<NodeHandle>,
}

/// `type GetSignatureUsagesParams struct` — parameters for the
/// getSignatureUsages method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSignatureUsagesParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub signature_decl: NodeHandle,
}

/// `type SignatureUsageResponse struct` — a single usage of a signature as a
/// name-call pair.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SignatureUsageResponse {
    pub name: NodeHandle,
    #[serde(skip_serializing_if = "node_handle_is_empty")]
    pub call: NodeHandle,
}

/// `type GetCompletionsAtPositionParams struct` — parameters for the
/// getCompletionsAtPosition method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetCompletionsAtPositionParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub position: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trigger_character: Option<String>,
    #[serde(skip_serializing_if = "is_false")]
    pub include_symbol: bool,
}

/// `type CompletionEntryLabelDetailsResponse struct` — additional label
/// display text for a completion entry.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CompletionEntryLabelDetailsResponse {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
}

/// `type CompletionEntryResponse struct` — a single completion item.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CompletionEntryResponse {
    pub name: String,
    #[serde(skip_serializing_if = "is_zero_u32")]
    pub kind: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sort_text: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub insert_text: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub filter_text: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label_details: Option<CompletionEntryLabelDetailsResponse>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<SymbolResponse>,
}

/// `type CompletionInfoResponse struct` — wraps a list of completion entries.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CompletionInfoResponse {
    pub is_incomplete: bool,
    /// `Entries` — `nonnil:"true"`.
    pub entries: Vec<CompletionEntryResponse>,
}

/// `type GetIntrinsicTypeParams struct` — used for intrinsic type getters
/// (anyType, stringType, etc.).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetIntrinsicTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
}

/// `type WellKnownSymbolsResponse struct` — carries the handle ids of the
/// per-checker singleton symbols (unknown, undefined, arguments) so the
/// client can identify them by id without a round-trip on every check.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct WellKnownSymbolsResponse {
    pub unknown: SymbolId,
    pub undefined: SymbolId,
    pub arguments: SymbolId,
}

/// `type WellKnownSignaturesResponse struct` — carries the handle id of the
/// per-checker singleton unknown signature (the signature the checker yields
/// when a call cannot be resolved) so the client can identify it by id
/// without a round-trip on every check.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct WellKnownSignaturesResponse {
    pub unknown: SignatureId,
}

/// `type GetBaseTypeOfLiteralTypeParams struct` — returns the base type of a
/// literal type.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetBaseTypeOfLiteralTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
}

/// `type GetNonNullableTypeParams struct` — parameters for the
/// getNonNullableType method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetNonNullableTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
}

/// `type GetTypeFromTypeNodeParams struct` — parameters for the
/// getTypeFromTypeNode method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypeFromTypeNodeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
}

/// `type GetWidenedTypeParams struct` — parameters for the getWidenedType method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetWidenedTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
}

/// `type GetParameterTypeParams struct` — parameters for the
/// getParameterType method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetParameterTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub signature: SignatureId,
    /// `Index int32`.
    pub index: i32,
}

/// `type IsArrayLikeTypeParams struct` — checks whether a type is array-like.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct IsArrayLikeTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
}

/// `type IsTypeAssignableToParams struct` — checks assignability between two types.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct IsTypeAssignableToParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub source: TypeId,
    pub target: TypeId,
}

/// `type GetSignaturesOfTypeParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetSignaturesOfTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
    /// `Kind int32`.
    pub kind: i32,
}

/// `type GetResolvedSignatureParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetResolvedSignatureParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
}

/// `type GetTypeAtLocationParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypeAtLocationParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
}

/// `type GetTypeAtLocationsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypeAtLocationsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub locations: Vec<NodeHandle>,
}

/// `type GetTypeAtPositionParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypeAtPositionParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub position: u32,
}

/// `type GetTypesAtPositionsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetTypesAtPositionsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub positions: Vec<u32>,
}

// ---------------------------------------------------------------------------
// Import adder / printer params
// ---------------------------------------------------------------------------

/// `ImportAdderActionKindImportSymbol`.
pub const IMPORT_ADDER_ACTION_KIND_IMPORT_SYMBOL: ImportAdderActionKind =
    ImportAdderActionKind::new("importSymbol");

/// `type ImportAdderAction struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct ImportAdderAction {
    pub kind: ImportAdderActionKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<SymbolReference>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_valid_type_only_use_site: Option<bool>,
}

/// `type GetImportAdderEditsParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetImportAdderEditsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub file: DocumentIdentifier,
    pub actions: Vec<ImportAdderAction>,
}

/// `type TextEdit struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TextEdit {
    /// `Pos int`.
    pub pos: i64,
    /// `End int`.
    pub end: i64,
    pub new_text: String,
}

/// `type TypeToTypeNodeParams struct` — parameters for the typeToTypeNode method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TypeToTypeNodeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
    #[serde(skip_serializing_if = "node_handle_is_empty")]
    pub location: NodeHandle,
    /// `Flags int32`.
    #[serde(skip_serializing_if = "is_zero_i32")]
    pub flags: i32,
}

/// `type SignatureToSignatureDeclarationParams struct` — parameters for the
/// signatureToSignatureDeclaration method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SignatureToSignatureDeclarationParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub signature: SignatureId,
    /// `Kind int32`.
    pub kind: i32,
    #[serde(skip_serializing_if = "node_handle_is_empty")]
    pub location: NodeHandle,
    /// `Flags int32`.
    #[serde(skip_serializing_if = "is_zero_i32")]
    pub flags: i32,
}

/// `type PrintNodeParams struct` — parameters for the printNode method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct PrintNodeParams {
    /// `Data` — base64-encoded binary AST data.
    pub data: String,
    #[serde(skip_serializing_if = "is_false")]
    pub preserve_source_newlines: bool,
    #[serde(skip_serializing_if = "is_false")]
    pub never_ascii_escape: bool,
    #[serde(skip_serializing_if = "is_false")]
    pub terminate_unterminated_literals: bool,
}

/// `type EmitParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct EmitParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub emit_only: Option<u32>,
}

/// `type SelectedFilesEmitParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SelectedFilesEmitParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub files: Vec<DocumentIdentifier>,
}

/// `type EmitResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct EmitResponse {
    pub emit_skipped: bool,
    /// `Diagnostics` — `nonnil:"true"`.
    pub diagnostics: Vec<DiagnosticResponse>,
    /// `EmittedFiles` — `nonnil:"true"`.
    #[serde(serialize_with = "ser_str_vec", deserialize_with = "de_str_vec")]
    pub emitted_files: Vec<RootedFilePath>,
    /// `EmittedFilesContents` contains contents parallel to EmittedFiles when
    /// the source snapshot uses a full filesystem. It is empty for
    /// write-through emits. `nonnil:"true"`.
    pub emitted_files_contents: Vec<String>,
}

/// `type EmitOutputFile struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct EmitOutputFile {
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub file_name: RootedFilePath,
    pub text: String,
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "ser_str_opt",
        deserialize_with = "de_str_opt"
    )]
    pub source_file_name: Option<RootedFilePath>,
}

/// `type EmitOutputResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct EmitOutputResponse {
    pub emit_skipped: bool,
    /// `Diagnostics` — `nonnil:"true"`.
    pub diagnostics: Vec<DiagnosticResponse>,
    /// `OutputFiles` — `nonnil:"true"`.
    pub output_files: Vec<EmitOutputFile>,
}

/// `type FormatNodeForInsertionParams struct` — parameters for the
/// formatNodeForInsertion method.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct FormatNodeForInsertionParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    /// Target file where the node will be inserted.
    pub file: DocumentIdentifier,
    /// UTF-16 code-unit offset of the insertion position in the target file.
    pub position: u32,
    /// `Data` — base64-encoded binary AST data for the synthesized node.
    pub data: String,
}

// ---------------------------------------------------------------------------
// Checker param structs
// ---------------------------------------------------------------------------

/// `type CheckerTypeParams struct` — parameters for checker methods that
/// operate on a type.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CheckerTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
}

/// `type GetPropertyOfTypeParams struct` — parameters for getPropertyOfType
/// (a named property of a type).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetPropertyOfTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
    pub name: String,
}

/// `type GetIndexInfoOfTypeParams struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetIndexInfoOfTypeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub r#type: TypeId,
    /// `Kind int32`.
    pub kind: i32,
}

/// `type GetMemberInModuleExportsParams struct` — parameters for
/// getMemberInModuleExports.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetMemberInModuleExportsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub symbol: SymbolReference,
    pub name: String,
}

/// `type CheckerNodeParams struct` — parameters for checker methods that
/// operate on a node location.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CheckerNodeParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub location: NodeHandle,
}

/// `type CheckerSymbolParams struct` — parameters for checker methods that
/// operate on a symbol.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CheckerSymbolParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub symbol: SymbolReference,
}

/// `type JSDocTagInfo struct` — a single JSDoc tag, mirroring Strada's
/// JSDocTagInfo but with the tag text rendered as a plain string rather than
/// SymbolDisplayPart[].
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct JsDocTagInfo {
    pub name: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub text: String,
}

/// `type CheckerSignatureParams struct` — parameters for checker methods that
/// operate on a signature.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct CheckerSignatureParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    pub signature: SignatureId,
}

/// `type TypePredicateResponse struct` — the response for
/// getTypePredicateOfSignature.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct TypePredicateResponse {
    /// `Kind int32`.
    pub kind: i32,
    /// `ParameterIndex int32`.
    pub parameter_index: i32,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub parameter_name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub r#type: Option<TypeResponse>,
}

/// `type IndexInfoResponse struct` — a single index signature.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct IndexInfoResponse {
    pub key_type: TypeResponse,
    pub value_type: TypeResponse,
    #[serde(skip_serializing_if = "is_false")]
    pub is_readonly: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub declaration: Option<NodeHandle>,
}

/// `type SourceFileResponse struct` — contains the binary-encoded AST data
/// for a source file. `Data` is base64-encoded binary data in the encoder's
/// format.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct SourceFileResponse {
    pub data: String,
}

// ---------------------------------------------------------------------------
// Diagnostic params/responses
// ---------------------------------------------------------------------------

/// `type GetDiagnosticsParams struct` — parameters for per-file diagnostic methods.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetDiagnosticsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub files: Vec<DocumentIdentifier>,
}

/// `type GetProjectDiagnosticsParams struct` — parameters for project-wide
/// diagnostic methods.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GetProjectDiagnosticsParams {
    pub snapshot: SnapshotId,
    #[serde(serialize_with = "ser_str", deserialize_with = "de_str")]
    pub project: ProjectId,
}

/// `type DiagnosticResponse struct` — the API response for a single diagnostic.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct DiagnosticResponse {
    /// The file name of the file this diagnostic belongs to, if any.
    #[serde(
        skip_serializing_if = "str_wrapped_is_empty",
        serialize_with = "ser_str",
        deserialize_with = "de_str"
    )]
    pub file_name: RootedFilePath,
    /// `Pos` is the start position of the diagnostic in the source file.
    pub pos: i64,
    /// `End` is the end position of the diagnostic in the source file.
    pub end: i64,
    /// `StartPosition` is the zero-based line and UTF-16 character position of Pos.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start_position: Option<DiagnosticPositionResponse>,
    /// `EndPosition` is the zero-based line and UTF-16 character position of End.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_position: Option<DiagnosticPositionResponse>,
    /// `SourceLines` contains the source lines needed to render this
    /// diagnostic with context.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub source_lines: Vec<DiagnosticSourceLineResponse>,
    /// `Code` is the diagnostic error code.
    pub code: i32,
    /// `Category` is the diagnostic category (error, warning, suggestion,
    /// message). Go `int32` serializes as a number.
    #[serde(
        default = "category_default",
        serialize_with = "ser_int",
        deserialize_with = "de_int"
    )]
    pub category: Category,
    /// `Source` is a custom diagnostic-code prefix. An empty value uses the
    /// default "TS".
    #[serde(skip_serializing_if = "String::is_empty")]
    pub source: String,
    /// `Text` is the localized diagnostic message text.
    pub text: String,
    /// `ReportsUnnecessary` indicates this diagnostic highlights unnecessary
    /// code. `omitzero`.
    #[serde(skip_serializing_if = "is_false")]
    pub reports_unnecessary: bool,
    /// `ReportsDeprecated` indicates this diagnostic highlights deprecated
    /// code. `omitzero`.
    #[serde(skip_serializing_if = "is_false")]
    pub reports_deprecated: bool,
    /// `MessageChain` contains chained diagnostic messages, if any.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub message_chain: Vec<DiagnosticResponse>,
    /// `RelatedInformation` contains related diagnostic information, if any.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub related_information: Vec<DiagnosticResponse>,
}

/// `type DiagnosticPositionResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct DiagnosticPositionResponse {
    /// `Line int`.
    pub line: i64,
    /// `Character core.UTF16Offset` (`i32`).
    pub character: UTF16Offset,
}

/// `type DiagnosticSourceLineResponse struct`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct DiagnosticSourceLineResponse {
    /// `Line int`.
    pub line: i64,
    pub text: String,
}

/// `func diagnosticSourceLines(file diagnosticwriter.FileLike, firstLine, lastLine int) []*DiagnosticSourceLineResponse`.
///
/// PORT: `FileLike` is a struct with a lifetime; `Text()`/`ECMALineMap()`
/// come through its `ast::SourceFileLike` impl (borrowed views of the live
/// source file, or owned snapshots — same read surface).
fn diagnostic_source_lines(
    file: &FileLike<'_>,
    first_line: i32,
    last_line: i32,
) -> Vec<DiagnosticSourceLineResponse> {
    let line_map = AstSourceFileLike::ecma_line_map(file);
    if line_map.is_empty() {
        return Vec::new();
    }

    let mut lines: Vec<i32> = Vec::with_capacity((last_line - first_line + 1).min(4) as usize);
    if last_line - first_line >= 4 {
        lines.extend([first_line, first_line + 1, last_line - 1, last_line]);
    } else {
        lines.extend(first_line..=last_line);
    }

    let text = AstSourceFileLike::text(file);
    let mut result = Vec::with_capacity(lines.len());
    for line in lines {
        let start = line_map[line as usize] as usize;
        let mut end = text.len();
        if (line as usize) + 1 < line_map.len() {
            end = line_map[(line as usize) + 1] as usize;
        }
        result.push(DiagnosticSourceLineResponse {
            line: line as i64,
            text: text[start..end].to_string(),
        });
    }
    result
}

/// `func NewDiagnosticResponse(d *ast.Diagnostic) *DiagnosticResponse`.
///
/// PORT: `nodes` is the AST arena the diagnostic's `DiagnosticFile.node`
/// handle resolves through — `wrap_ast_diagnostic(d, nodes)` mirrors
/// `diagnosticwriter.WrapASTDiagnostic(d)`.
pub fn new_diagnostic_response(d: DiagnosticRef, nodes: &[Node]) -> DiagnosticResponse {
    ast_diagnostic_response(&wrap_ast_diagnostic(d, nodes))
}

/// `func newDiagnosticResponse(d *diagnosticwriter.ASTDiagnostic) *DiagnosticResponse`.
///
/// PORT notes:
/// - `d.Pos()`/`d.End()`/`d.Source()`/`d.Localize` are the `Diagnostic`
///   trait methods — resolve()-adjusted, like Go's `*ASTDiagnostic` calls.
/// - `d.Diagnostic.ReportsUnnecessary/ReportsDeprecated` read the embedded
///   `*ast.Diagnostic` → `lock_diagnostic(&d.diagnostic)`.
/// - Go's `file.(*ast.SourceFile)` branch uses `PositionMap.UTF8ToUTF16` —
///   a cache with identical semantics to `UTF16Len(text[:pos])`. The port's
///   `FileLike` doesn't expose its provenance, so `utf16_len` on the
///   boundary-safe byte prefix is used for both branches (see
///   `utf16_len_of_prefix` for mid-char positions).
/// - `d.MessageChain()`/`d.RelatedInformation()` return `Box<dyn Diagnostic>`
///   which cannot downcast to `ASTDiagnostic` (the trait has no `as_any`).
///   The chain is rebuilt at `DiagnosticRef` level — identical output,
///   including the content-mapper "synthesized virtual code" note (see
///   `diagnostic_chain_refs`).
fn ast_diagnostic_response(d: &ASTDiagnostic<'_>) -> DiagnosticResponse {
    let file = d.file();
    let mut pos = d.pos();
    let mut end = d.end();
    if let Some(f) = &file {
        let len = AstSourceFileLike::text(f).len() as i32;
        pos = pos.clamp(0, len);
        end = end.clamp(pos, len);
    }

    let mut resp = {
        let locked = lock_diagnostic(&d.diagnostic);
        DiagnosticResponse {
            pos: pos as i64,
            end: end as i64,
            code: d.code(),
            category: d.category(),
            source: d.source(),
            text: d.localize(&DEFAULT_LOCALE),
            reports_unnecessary: locked.reports_unnecessary(),
            reports_deprecated: locked.reports_deprecated(),
            ..Default::default()
        }
    };

    if let Some(file) = &file {
        resp.file_name = file.file_name().clone();
        let text = AstSourceFileLike::text(file);
        resp.pos = utf16_len_of_prefix(text, pos as usize) as i64;
        resp.end = utf16_len_of_prefix(text, end as usize) as i64;
        let (start_line, start_character) =
            get_ecma_line_and_utf16_character_of_position(file, pos);
        let (end_line, end_character) =
            get_ecma_line_and_utf16_character_of_position(file, end);
        resp.start_position = Some(DiagnosticPositionResponse {
            line: start_line as i64,
            character: start_character,
        });
        resp.end_position = Some(DiagnosticPositionResponse {
            line: end_line as i64,
            character: end_character,
        });
        resp.source_lines = diagnostic_source_lines(file, start_line, end_line);
    }

    for c in diagnostic_chain_refs(d) {
        resp.message_chain.push(ast_diagnostic_response(&ASTDiagnostic {
            diagnostic: c,
            nodes: d.nodes,
        }));
    }

    let related = {
        let locked = lock_diagnostic(&d.diagnostic);
        locked.related_information().to_vec()
    };
    for r in related {
        resp.related_information.push(ast_diagnostic_response(&ASTDiagnostic {
            diagnostic: r,
            nodes: d.nodes,
        }));
    }

    resp
}

/// `core.UTF16Len(text[:pos])` on a possibly mid-char byte offset — decodes
/// the prefix the way Go's rune iterator does: bytes of a truncated
/// multi-byte sequence are invalid UTF-8, so each counts as one RuneError
/// code unit.
fn utf16_len_of_prefix(text: &str, byte_pos: usize) -> UTF16Offset {
    let mut boundary = byte_pos.min(text.len());
    while !text.is_char_boundary(boundary) {
        boundary -= 1;
    }
    utf16_len(&text[..boundary]) + (byte_pos.min(text.len()) - boundary) as UTF16Offset
}

/// `ASTDiagnostic::message_chain` rebuilt at `DiagnosticRef` level —
/// `lock.message_chain()` plus, for synthesized ranges, the content-mapper
/// note (mirrors the trait impl's `resolve().synthesized` + note append).
fn diagnostic_chain_refs(d: &ASTDiagnostic<'_>) -> Vec<DiagnosticRef> {
    let mut chain = {
        let locked = lock_diagnostic(&d.diagnostic);
        locked.message_chain().to_vec()
    };
    if diagnostic_is_synthesized(d) {
        if let Some(mapper) = diagnostic_content_mapper(d) {
            chain.push(new_compiler_diagnostic(
                &tsc_diagnostics::This_location_is_in_virtual_code_produced_by_the_content_mapper_0_and_has_no_corresponding_location_in_the_original_file,
                &[mapper],
            ));
        }
    }
    chain
}

/// `ASTDiagnostic::resolve().synthesized` — the diagnostic's range falls in
/// synthesized virtual code with no original counterpart (`FidelityNone`
/// from `virtual_to_original_span`, or — for external-source diagnostics —
/// Go's early return before the synthesized flag is set).
fn diagnostic_is_synthesized(d: &ASTDiagnostic<'_>) -> bool {
    let locked = lock_diagnostic(&d.diagnostic);
    let Some(file) = locked.file() else {
        return false;
    };
    // `resolve()` returns early (not synthesized) for external-source
    // diagnostics and when there is no file.
    if !locked.source().is_empty() {
        return false;
    }
    let live_span_map = file
        .node
        .and_then(|node| d.nodes[node].as_source_file().span_map());
    let span_map = live_span_map.as_deref().or(file.span_map.as_deref());
    let (_, fidelity) = SpanMap::virtual_to_original_span(span_map, locked.loc());
    fidelity == tsc_spanmap::Fidelity::None
}

/// `ASTDiagnostic::content_mapper` — the live node's mapper identity, or
/// empty when the diagnostic file has no arena node.
fn diagnostic_content_mapper(d: &ASTDiagnostic<'_>) -> Option<String> {
    let locked = lock_diagnostic(&d.diagnostic);
    let file = locked.file()?;
    file.node.map(|node| {
        d.nodes[node]
            .as_source_file()
            .content_mapper()
            .to_string()
    })
}

impl DiagnosticResponse {
    /// `func (d *DiagnosticResponse) ToDiagnostic() *ast.Diagnostic`.
    pub fn to_diagnostic(&self) -> DiagnosticRef {
        new_diagnostic_from_text(
            None,
            TextRange::new(self.pos as i32, self.end as i32),
            self.code,
            self.category,
            self.text.clone(),
            self.message_chain
                .iter()
                .map(|d| d.to_diagnostic())
                .collect(),
            self.related_information
                .iter()
                .map(|d| d.to_diagnostic())
                .collect(),
            self.reports_unnecessary,
            self.reports_deprecated,
        )
    }
}

/// `func NewDiagnosticResponses(diags []*ast.Diagnostic) []*DiagnosticResponse`.
///
/// PORT: `nodes` is the AST arena (see `new_diagnostic_response`); Go's nil
/// for empty is an empty Vec (serialized `[]` either way).
pub fn new_diagnostic_responses(
    diags: &[DiagnosticRef],
    nodes: &[Node],
) -> Vec<DiagnosticResponse> {
    diags.iter()
        .map(|d| new_diagnostic_response(d.clone(), nodes))
        .collect()
}

// ---------------------------------------------------------------------------
// unmarshalers dispatch (`unmarshalPayload`/`unmarshallerFor`/`noParams`)
// ---------------------------------------------------------------------------

/// `func unmarshalPayload(method string, payload json.Value) (any, error)` +
/// `var unmarshalers map[Method]func([]byte) (any, error)` +
/// `func unmarshallerFor[T any]` + `func noParams`.
///
/// PORT: the `map[Method]` becomes a match on the wire literals; each arm
/// deserializes the params struct into `Box<dyn Any>` (the session downcasts
/// to the concrete type, like Go's `any`). `noParams` → `Box::new(())` for
/// Go's `nil` `any` (the session ignores params for those methods). Go's
/// `%T` in the parse error becomes `*api.<TypeName>`.
pub fn unmarshal_payload(method: &str, payload: &[u8]) -> Result<Box<dyn Any>, String> {
    fn parse<T: for<'de> Deserialize<'de> + 'static>(
        data: &[u8],
    ) -> Result<Box<dyn Any>, String> {
        serde_json::from_slice::<T>(data)
            .map(|v| Box::new(v) as Box<dyn Any>)
            .map_err(|e| {
                let name = std::any::type_name::<T>().rsplit("::").next().unwrap_or("?");
                format!("failed to unmarshal *api.{name}: {e}")
            })
    }

    match method {
        "batchRequests" => parse::<BatchRequestsParams>(payload),
        "release" => parse::<ReleaseParams>(payload),
        "releaseSourceFile" => parse::<ReleaseSourceFileParams>(payload),
        "retainSourceFile" => parse::<RetainSourceFileParams>(payload),
        "getCachedSourceFile" => parse::<GetCachedSourceFileParams>(payload),
        "getSymbolOfDeclaration" => parse::<GetSymbolOfDeclarationParams>(payload),
        "initialize" => Ok(Box::new(())),
        "createSnapshot" => parse::<CreateSnapshotParams>(payload),
        "updateSnapshot" => parse::<UpdateSnapshotParams>(payload),
        "getCurrentLanguageServerSnapshot" => {
            parse::<GetCurrentLanguageServerSnapshotParams>(payload)
        }
        "createBuildOrchestrator" => parse::<CreateBuildOrchestratorParams>(payload),
        "disposeBuildOrchestrator" => parse::<DisposeBuildOrchestratorParams>(payload),
        "build" | "buildReferences" => parse::<BuildParams>(payload),
        "cleanBuild" | "cleanReferences" => parse::<CleanBuildParams>(payload),
        "createModuleResolver" => parse::<CreateModuleResolverParams>(payload),
        "releaseModuleResolver" => parse::<ReleaseModuleResolverParams>(payload),
        "resolveModuleName" => parse::<ResolveModuleNameParams>(payload),
        "parseCommandLine" => parse::<ParseCommandLineParams>(payload),
        "readConfigFile" => parse::<ReadConfigFileParams>(payload),
        "parseJsonConfigFileContent" => parse::<ParseJsonConfigFileContentParams>(payload),
        "parseConfigFile" => parse::<ParseConfigFileParams>(payload),
        "createSourceFile" => parse::<CreateSourceFileParams>(payload),
        "createSourceFileFromFile" => parse::<CreateSourceFileFromFileParams>(payload),
        "transpileModule" | "transpileDeclaration" => parse::<TranspileParams>(payload),
        "transpileModuleFromFile" | "transpileDeclarationFromFile" => {
            parse::<TranspileFromFileParams>(payload)
        }
        "getDefaultProjectForFile" => parse::<GetDefaultProjectForFileParams>(payload),
        "getSourceFile" | "getSourceFileMetadata" | "getConfigSourceFile" => {
            parse::<GetSourceFileParams>(payload)
        }
        "getSourceFileNames" => parse::<GetSourceFileNamesParams>(payload),
        "getModeForUsageLocation" => parse::<GetModeForUsageLocationParams>(payload),
        "getModeForResolutionAtIndex" => parse::<GetModeForResolutionAtIndexParams>(payload),
        "getResolvedModule" => parse::<GetResolvedModuleParams>(payload),
        "getResolvedModuleFromModuleSpecifier" => {
            parse::<GetResolvedModuleFromModuleSpecifierParams>(payload)
        }
        "getResolvedTypeReferenceDirective" => {
            parse::<GetResolvedTypeReferenceDirectiveParams>(payload)
        }
        "getResolvedTypeReferenceDirectiveFromTypeReferenceDirective" => {
            parse::<GetResolvedTypeReferenceDirectiveFromReferenceParams>(payload)
        }
        "getConfigFileNames" | "getProgramDiagnostics" | "getGlobalDiagnostics"
        | "getConfigFileParsingDiagnostics" => parse::<GetProjectDiagnosticsParams>(payload),
        "getSymbolAtPosition" => parse::<GetSymbolAtPositionParams>(payload),
        "getSymbolsAtPositions" => parse::<GetSymbolsAtPositionsParams>(payload),
        "getSymbolAtLocation" => parse::<GetSymbolAtLocationParams>(payload),
        "getSymbolsAtLocations" => parse::<GetSymbolsAtLocationsParams>(payload),
        "getSymbolOfSourceFile" => parse::<GetSymbolOfSourceFileParams>(payload),
        "getSymbolsOfSourceFiles" => parse::<GetSymbolsOfSourceFilesParams>(payload),
        "getTypeOfSymbol" | "getDeclaredTypeOfSymbol" | "getNonMissingTypeOfSymbol" => {
            parse::<GetTypeOfSymbolParams>(payload)
        }
        "getTypesOfSymbols" => parse::<GetTypesOfSymbolsParams>(payload),
        "resolveName" => parse::<ResolveNameParams>(payload),
        "getSymbolsInScope" => parse::<GetSymbolsInScopeParams>(payload),
        "getSignaturesOfType" => parse::<GetSignaturesOfTypeParams>(payload),
        "getResolvedSignature" => parse::<GetResolvedSignatureParams>(payload),
        "getTypeAtLocation" | "getShorthandAssignmentValueSymbol" => {
            parse::<GetTypeAtLocationParams>(payload)
        }
        "getTypeAtLocations" => parse::<GetTypeAtLocationsParams>(payload),
        "getTypeAtPosition" => parse::<GetTypeAtPositionParams>(payload),
        "getTypesAtPositions" => parse::<GetTypesAtPositionsParams>(payload),

        // Symbol sub-property methods
        "getParentOfSymbol" | "getMembersOfSymbol" | "getExportsOfSymbol"
        | "getExportSymbolOfSymbol" => parse::<GetSymbolPropertyParams>(payload),

        // Type sub-property methods
        "getSymbolOfType" | "getTargetOfType" | "getFreshTypeOfType"
        | "getRegularTypeOfType" | "getTypesOfType" | "getTypeParametersOfType"
        | "getOuterTypeParametersOfType" | "getLocalTypeParametersOfType"
        | "getThisTypeOfType" | "getAliasTypeArgumentsOfType" | "getAliasSymbolOfType"
        | "getObjectTypeOfType" | "getIndexTypeOfType" | "getCheckTypeOfType"
        | "getExtendsTypeOfType" | "getBaseTypeOfType" | "getConstraintOfType"
        | "getTypeParameterOfMappedType" | "getConstraintTypeOfMappedType"
        | "getNameTypeOfMappedType" | "getTemplateTypeOfMappedType"
        | "getTrueTypeOfConditionalType" | "getFalseTypeOfConditionalType"
        | "getNonNullableType" | "getApparentPropertiesOfType" | "getApparentType"
        | "getReducedType" | "getConstraintOfTypeParameter" => {
            parse::<GetTypePropertyParams>(payload)
        }

        // Signature sub-property methods
        "getTypeParametersOfSignature" | "getParametersOfSignature"
        | "getThisParameterOfSignature" | "getTargetOfSignature"
        | "getReturnTypeOfSignature" => parse::<GetSignaturePropertyParams>(payload),

        // Checker methods
        "getContextualType" | "isContextSensitive" => {
            parse::<GetContextualTypeParams>(payload)
        }
        "getContextualTypeForArgument" => {
            parse::<GetContextualTypeForArgumentParams>(payload)
        }
        "getAwaitedType" | "getBaseTypes" | "getPropertiesOfType"
        | "getIndexInfosOfType" | "getTypeArguments" | "getBaseConstraintOfType"
        | "getDefaultFromTypeParameter" | "isArrayType" => {
            parse::<CheckerTypeParams>(payload)
        }
        "getBaseTypeOfLiteralType" => parse::<GetBaseTypeOfLiteralTypeParams>(payload),
        "getTypeFromTypeNode" => parse::<GetTypeFromTypeNodeParams>(payload),
        "getWidenedType" => parse::<GetWidenedTypeParams>(payload),
        "getParameterType" | "getTypeParameterAtPosition" => {
            parse::<GetParameterTypeParams>(payload)
        }
        "isArrayLikeType" => parse::<IsArrayLikeTypeParams>(payload),
        "isTypeAssignableTo" => parse::<IsTypeAssignableToParams>(payload),
        "getTypeOfSymbolAtLocation" => parse::<GetTypeOfSymbolAtLocationParams>(payload),
        "typeToTypeNode" | "typeToString" => parse::<TypeToTypeNodeParams>(payload),
        "signatureToSignatureDeclaration" => {
            parse::<SignatureToSignatureDeclarationParams>(payload)
        }
        "getRestTypeOfSignature" | "getTypePredicateOfSignature" => {
            parse::<CheckerSignatureParams>(payload)
        }
        "getPropertyOfType" | "getTypeOfPropertyOfType" => {
            parse::<GetPropertyOfTypeParams>(payload)
        }
        "getIndexInfoOfType" => parse::<GetIndexInfoOfTypeParams>(payload),
        "getImportAdderEdits" => parse::<GetImportAdderEditsParams>(payload),
        "getConstantValue" | "getSignatureFromDeclaration"
        | "getExportSpecifierLocalTargetSymbol" | "getSymbolOfNode"
        | "getSymbolOfDeclarationForChecker" => parse::<CheckerNodeParams>(payload),
        "getAliasedSymbol" | "getImmediateAliasedSymbol" | "getTargetSymbol"
        | "getMergedSymbol" | "getParentOfSymbolForChecker"
        | "getExportSymbolOfSymbolForChecker" | "getFullyQualifiedName"
        | "getExportsOfModule" | "getJsDocTags" | "getDocumentationComment"
        | "isReadonlySymbol" => parse::<CheckerSymbolParams>(payload),
        "getMemberInModuleExports" => parse::<GetMemberInModuleExportsParams>(payload),
        "getReferencesToSymbolInFile" => parse::<GetReferencesToSymbolInFileParams>(payload),
        "getReferencedSymbolsForNode" => parse::<GetReferencedSymbolsForNodeParams>(payload),
        "getSignatureUsages" => parse::<GetSignatureUsagesParams>(payload),
        "getCompletionsAtPosition" => parse::<GetCompletionsAtPositionParams>(payload),
        "printNode" => parse::<PrintNodeParams>(payload),
        "formatNodeForInsertion" => parse::<FormatNodeForInsertionParams>(payload),
        "emit" | "emitToString" => parse::<EmitParams>(payload),
        "getJavaScriptEmit" | "getDeclarationEmit" => {
            parse::<SelectedFilesEmitParams>(payload)
        }
        "getAnyType" | "getStringType" | "getNumberType" | "getBooleanType"
        | "getVoidType" | "getUndefinedType" | "getNullType" | "getNeverType"
        | "getUnknownType" | "getBigIntType" | "getESSymbolType" | "getNonPrimitiveType"
        | "getWellKnownSymbols" | "getWellKnownSignatures" => {
            parse::<GetIntrinsicTypeParams>(payload)
        }
        "getSyntacticDiagnostics" | "getBindDiagnostics" | "getSemanticDiagnostics"
        | "getSuggestionDiagnostics" | "getDeclarationDiagnostics" => {
            parse::<GetDiagnosticsParams>(payload)
        }
        "startCPUProfile" | "saveHeapProfile" => parse::<ProfileParams>(payload),
        "stopCPUProfile" => Ok(Box::new(())),
        _ => Err(format!("unknown API method {method:?}")),
    }
}
