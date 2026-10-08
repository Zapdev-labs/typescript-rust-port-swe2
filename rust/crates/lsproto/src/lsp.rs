// Ported from tsc/internal/lsp/lsproto/lsp.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;
use std::fmt;

use serde::de::DeserializeOwned;
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use tsc_bundled as bundled;
use tsc_json as json;
use tsc_tspath as tspath;

use crate::jsonrpc::RequestMessage;
use crate::lsp_generated::{CodeActionKind, ErrorCode, MarkupKind, ResolvedClientCapabilities};

/// `type DocumentUri string` — a URI identifying a document. Kept verbatim
/// from the LSP wire format; [`DocumentUri::path`] performs the encoding-aware
/// conversion to a [`tspath::RootedPath`].
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DocumentUri(pub String);

impl DocumentUri {
    /// `func (uri DocumentUri) Path() tspath.RootedPath`
    ///
    /// `file://` URIs are URL-parsed; other schemes keep their percent
    /// encoding and are folded into an encoded "dynamic URI" file name so
    /// they round-trip back through [`dynamic_file_name_to_document_uri`].
    pub fn path(&self) -> tspath::RootedPath {
        let uri = self.0.as_str();
        if bundled::is_bundled(uri) {
            return tspath::rooted_path_from_absolute(uri);
        }
        if uri.starts_with("file://") {
            let Some((host, path)) = parse_file_uri(uri) else {
                panic!("invalid file URI: {uri}");
            };
            if !host.is_empty() {
                return tspath::rooted_path_from_absolute(&format!("//{host}{path}"));
            }
            return tspath::rooted_path_from_absolute(&fix_windows_uri_path(&path));
        }

        // Leave all other URIs escaped so we can round-trip them.

        let Some((scheme, mut path)) = uri.split_once(':') else {
            panic!("invalid URI: {uri}");
        };
        let mut suffix = "";
        if let Some(suffix_start) = path.find(['?', '#']) {
            suffix = &path[suffix_start..];
            path = &path[..suffix_start];
        }

        let mut authority = "ts-nul-authority".to_string();
        let mut has_authority = false;
        let mut has_path = true;
        if let Some(rest) = path.strip_prefix("//") {
            has_authority = true;
            match rest.split_once('/') {
                Some((a, p)) => {
                    authority = a.to_string();
                    path = p;
                }
                None => {
                    authority = rest.to_string();
                    path = "";
                    has_path = false;
                }
            }
        }
        let encoded_authority = if has_authority {
            if authority == "ts-nul-authority" {
                tspath::force_encode_dynamic_uri_path_segment(&authority, false)
            } else {
                tspath::encode_dynamic_uri_path(&authority).into_owned()
            }
        } else {
            authority
        };
        let encoded_path = if has_path {
            tspath::encode_dynamic_uri_path_with_suffix(path, suffix)
        } else {
            tspath::encode_dynamic_uri_no_path(suffix)
        };

        tspath::rooted_path_from_normalized(&format!(
            "{}{}/{}/{}",
            tspath::DYNAMIC_URI_FILE_NAME_PREFIX,
            scheme,
            encoded_authority,
            encoded_path,
        ))
    }

    /// `func (uri DocumentUri) FileName() tspath.RootedFilePath`
    pub fn file_name(&self) -> tspath::RootedFilePath {
        tspath::rooted_file_path_from_path(self.path())
    }

    /// `func (uri DocumentUri) PathKey(caseSensitivity tspath.CaseSensitivity) tspath.PathKey`
    pub fn path_key(&self, case_sensitivity: tspath::CaseSensitivity) -> tspath::PathKey {
        case_sensitivity.path_key(&self.path())
    }

    /// `func (uri DocumentUri) String()` — the underlying URI text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Minimal port of `net/url.Parse` restricted to `file://` URIs: splits the
/// authority (up to the first `/` of the path) and percent-decodes both parts.
/// The query/fragment is stripped from the path, matching `URL.Path`.
///
/// PORT: Go's `url.Parse` additionally rejects control characters and accepts
/// invalid-UTF8 byte paths; Rust strings cannot hold the latter, and control
/// characters are simply passed through here.
fn parse_file_uri(uri: &str) -> Option<(String, String)> {
    let rest = uri.strip_prefix("file://")?;
    let (authority, path_and_rest) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, ""),
    };
    let host = percent_decode(authority)?;
    let path = match path_and_rest.find(['?', '#']) {
        Some(i) => &path_and_rest[..i],
        None => path_and_rest,
    };
    Some((host, percent_decode(path)?))
}

/// `url.PathUnescape` for the small `file://` subset used above.
fn percent_decode(s: &str) -> Option<String> {
    if !s.contains('%') {
        return Some(s.to_string());
    }
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            if i + 2 >= bytes.len() {
                return None;
            }
            let hi = (bytes[i + 1] as char).to_digit(16)?;
            let lo = (bytes[i + 2] as char).to_digit(16)?;
            out.push((hi * 16 + lo) as u8);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).ok()
}

/// `func fixWindowsURIPath(path string) string` — `/c:/...` -> `c:/...`.
fn fix_windows_uri_path(path: &str) -> String {
    if let Some(rest) = path.strip_prefix('/') {
        let bytes = rest.as_bytes();
        if bytes.len() >= 2 && tspath::is_volume_character(bytes[0]) && bytes[1] == b':' {
            return rest.to_string();
        }
    }
    path.to_string()
}

/// `func DynamicFileNameToDocumentUri(fileName tspath.RootedPath) DocumentUri`
pub fn dynamic_file_name_to_document_uri(file_name: &tspath::RootedPath) -> DocumentUri {
    match dynamic_file_name_to_document_uri_inner(file_name, false) {
        Some(uri) => uri,
        None => panic!("invalid file name: {}", file_name.as_string()),
    }
}

/// `func TryDynamicFileNameToDocumentUri(fileName tspath.RootedPath) (DocumentUri, bool)`
pub fn try_dynamic_file_name_to_document_uri(
    file_name: &tspath::RootedPath,
) -> Option<DocumentUri> {
    dynamic_file_name_to_document_uri_inner(file_name, true)
}

fn dynamic_file_name_to_document_uri_inner(
    file_name: &tspath::RootedPath,
    strict: bool,
) -> Option<DocumentUri> {
    let path = file_name.as_string();
    let encoded = tspath::is_encoded_dynamic_file_name(path);
    let start = if encoded {
        tspath::DYNAMIC_URI_FILE_NAME_PREFIX.len()
    } else {
        2
    };
    let (scheme, rest) = path[start..].split_once('/')?;
    if strict && scheme.is_empty() {
        return None;
    }
    let (authority, uri_path) = rest.split_once('/')?;
    let has_authority = authority != "ts-nul-authority";
    let authority = if encoded {
        if strict {
            tspath::try_decode_dynamic_uri_path_segment(authority)?
        } else {
            tspath::decode_dynamic_uri_path_segment(authority)
        }
    } else {
        authority.to_string()
    };
    if encoded && has_authority {
        if let Some(suffix) = tspath::decode_dynamic_uri_no_path(uri_path) {
            return Some(DocumentUri(format!("{scheme}://{authority}{suffix}")));
        }
    }
    let uri_path = if encoded {
        if strict {
            tspath::try_decode_dynamic_uri_path(uri_path)?
        } else {
            tspath::decode_dynamic_uri_path(uri_path).into_owned()
        }
    } else {
        uri_path.to_string()
    };
    if !has_authority {
        return Some(DocumentUri(format!("{scheme}:{uri_path}")));
    }
    Some(DocumentUri(format!("{scheme}://{authority}/{uri_path}")))
}

/// `type HasTextDocumentURI interface`
pub trait HasTextDocumentUri {
    fn text_document_uri(&self) -> DocumentUri;
}

/// `type HasTextDocumentPosition interface`
pub trait HasTextDocumentPosition: HasTextDocumentUri {
    fn text_document_position(&self) -> Position;
}

/// `type HasLocations interface`
pub trait HasLocations {
    fn get_locations(&self) -> Option<&Vec<Location>>;
}

/// `type HasLocation interface`
pub trait HasLocation {
    fn get_location(&self) -> Location;
}

/// `type URI string`
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct URI(pub String);

impl URI {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for URI {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// `type Method string` — an LSP method name such as `"textDocument/didOpen"`.
/// `Cow` so the `Method::X` associated constants are free to construct.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Method(pub Cow<'static, str>);

impl Method {
    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl Serialize for Method {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for Method {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(Method(Cow::Owned(String::deserialize(d)?)))
    }
}

impl Serialize for DocumentUri {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for DocumentUri {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(DocumentUri(String::deserialize(d)?))
    }
}

impl Serialize for URI {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for URI {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(URI(String::deserialize(d)?))
    }
}

impl fmt::Display for DocumentUri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// --- error helpers (structcodec.go + lsp.go share these) ---

/// `func errNotObject(k json.Kind) error`
pub(crate) fn err_not_object(k: json::Kind) -> serde_json::Error {
    serde::de::Error::custom(format!(
        "expected object start, but encountered {}",
        k as char
    ))
}

/// `func errNull(field string) error`
pub(crate) fn err_null(field: &str) -> serde_json::Error {
    serde::de::Error::custom(format!("null value is not allowed for field \"{field}\""))
}

/// `func errMissing(props []string) error`
pub(crate) fn err_missing(props: &[&str]) -> serde_json::Error {
    serde::de::Error::custom(format!("missing required properties: {}", props.join(", ")))
}

/// `func errInvalidKind(typeName string, got json.Kind) error`
pub(crate) fn err_invalid_kind(type_name: &str, got: json::Kind) -> serde_json::Error {
    serde::de::Error::custom(format!("invalid {type_name}: got {}", got as char))
}

/// `func errInvalidValue(typeName string, data []byte) error`
pub(crate) fn err_invalid_value(type_name: &str, data: &str) -> serde_json::Error {
    serde::de::Error::custom(format!("invalid {type_name}: {data}"))
}

/// `func errLiteralMismatch(typeName, expected string, got []byte) error`
pub(crate) fn err_literal(type_name: &str, expected: &str, got: &str) -> serde_json::Error {
    serde::de::Error::custom(format!("expected {type_name} value {expected}, got {got}"))
}

/// `func jsonKeyCheck(name []byte, key string) bool` — compares a raw JSON key
/// token (including quotes) against a plain string.
fn json_key_check(name: &[u8], key: &str) -> bool {
    name.len() == key.len() + 2 && name[0] == b'"' && &name[1..name.len() - 1] == key.as_bytes()
}

/// `func jsonObjectRawField(data []byte, field string) json.Value` — scans the
/// top-level keys of a JSON object for `field`, returning its raw value.
pub(crate) fn json_object_raw_field(data: &[u8], field: &str) -> Option<json::Value> {
    let mut dec = json::new_decoder(data);
    if dec.peek_kind().ok()? != b'{' {
        return None;
    }
    dec.read_token().ok()?;
    while dec.peek_kind().ok()? != b'}' {
        let name = dec.read_value().ok()?;
        if json_key_check(name.get().as_bytes(), field) {
            return dec.read_value().ok();
        }
        dec.skip_value().ok()?;
    }
    None
}

/// `func jsonObjectHasKey(data []byte, keys ...string) int` — index of the
/// first matching top-level key, or -1.
pub(crate) fn json_object_has_key(data: &[u8], keys: &[&str]) -> i32 {
    let mut dec = json::new_decoder(data);
    if dec.peek_kind().ok() != Some(b'{') {
        return -1;
    }
    if dec.read_token().is_err() {
        return -1;
    }
    while dec.peek_kind().ok() != Some(b'}') {
        let Ok(name) = dec.read_value() else {
            return -1;
        };
        for (i, key) in keys.iter().enumerate() {
            if json_key_check(name.get().as_bytes(), key) {
                return i as i32;
            }
        }
        if dec.skip_value().is_err() {
            return -1;
        }
    }
    -1
}

/// `norm_kind` — jsontext collapses all number-start bytes (`-`, `1`-`9`) into
/// kind `'0'`; the generated kind switches emulate that.
pub(crate) fn norm_kind(k: u8) -> u8 {
    match k {
        b'1'..=b'9' | b'-' => b'0',
        _ => k,
    }
}

// Inspired by https://www.youtube.com/watch?v=dab3I-HcTVk

/// `type RequestInfo[Params, Resp any] struct` — compile-time description of a
/// request method: its param and response types plus the method name.
pub struct RequestInfo<P, R> {
    pub method: Method,
    _pd: std::marker::PhantomData<fn() -> (P, R)>,
}

impl<P, R> RequestInfo<P, R> {
    pub const fn new(method: Method) -> Self {
        Self {
            method,
            _pd: std::marker::PhantomData,
        }
    }

    /// `func (info RequestInfo[P, R]) UnmarshalResult(result any) (R, error)`
    ///
    /// Inbound results are stored as raw JSON (`json.Value`) because the
    /// method — and therefore the result type — is not known at decode time.
    pub fn unmarshal_result(&self, result: Option<&json::Value>) -> Result<R, serde_json::Error>
    where
        R: DeserializeOwned,
    {
        let Some(raw) = result else {
            return Err(serde::de::Error::custom("expected json.Value, got <nil>"));
        };
        json::unmarshal(raw.get().as_bytes(), &[])
    }

    /// `func (info RequestInfo[P, R]) NewRequestMessage(id *jsonrpc.ID, params P) *RequestMessage`
    ///
    /// PORT: Go stores the typed `params` in `Params any` and marshals lazily;
    /// we marshal eagerly to a `json::Value` (raw JSON) — identical wire
    /// output, and marshal failures surface here instead of at write time.
    pub fn new_request_message(&self, id: Option<tsc_jsonrpc::ID>, params: P) -> RequestMessage
    where
        P: Serialize,
    {
        let __bytes =
            json::marshal(&params, &[]).expect("RequestInfo.NewRequestMessage: marshal params");
        let params = serde_json::value::RawValue::from_string(
            String::from_utf8(__bytes).expect("marshal produced invalid UTF-8"),
        )
        .expect("marshal produced invalid JSON");
        RequestMessage {
            jsonrpc: tsc_jsonrpc::JSONRPCVersion,
            id,
            method: self.method.clone(),
            params: Some(params),
        }
    }
}

/// `type NotificationInfo[Params any] struct`
pub struct NotificationInfo<P> {
    pub method: Method,
    _pd: std::marker::PhantomData<fn() -> P>,
}

impl<P> NotificationInfo<P> {
    pub const fn new(method: Method) -> Self {
        Self {
            method,
            _pd: std::marker::PhantomData,
        }
    }

    /// `func (info NotificationInfo[P]) NewNotificationMessage(params P) *RequestMessage`
    pub fn new_notification_message(&self, params: P) -> RequestMessage
    where
        P: Serialize,
    {
        let __bytes = json::marshal(&params, &[])
            .expect("NotificationInfo.NewNotificationMessage: marshal params");
        let params = serde_json::value::RawValue::from_string(
            String::from_utf8(__bytes).expect("marshal produced invalid UTF-8"),
        )
        .expect("marshal produced invalid JSON");
        RequestMessage {
            jsonrpc: tsc_jsonrpc::JSONRPCVersion,
            id: None,
            method: self.method.clone(),
            params: Some(params),
        }
    }
}

/// The error returned by [`RequestMessage::unmarshal_params`] — `fmt.Errorf`
/// wrapping an [`ErrorCode`]. Callers match on [`ParamsError::code`], the Rust
/// analog of Go's `errors.Is(err, ErrorCodeInvalidParams)`.
#[derive(Clone, Debug)]
pub struct ParamsError {
    code: ErrorCode,
    message: String,
}

impl ParamsError {
    fn new(code: ErrorCode, message: String) -> ParamsError {
        ParamsError { code, message }
    }

    /// The wrapped `ErrorCode` (e.g. `ErrorCode::InvalidParams`).
    pub fn code(&self) -> ErrorCode {
        self.code
    }
}

impl fmt::Display for ParamsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.message)
    }
}

impl std::error::Error for ParamsError {}

impl RequestMessage {
    /// `func (r *RequestMessage) UnmarshalParams[T]() (T, error)` — decodes the
    /// params of an inbound request/notification into `T`.
    ///
    /// A `NoParams` method must be given no params; every other method must be
    /// given params as an object or array. Violations return
    /// `ErrorCode::InvalidParams`.
    pub fn unmarshal_params<T>(&self) -> Result<T, ParamsError>
    where
        T: DeserializeOwned + Default + 'static,
    {
        // `params` is the zero value of T; this asserts on its type, i.e.
        // whether the method was declared with NoParams.
        if std::any::TypeId::of::<T>() == std::any::TypeId::of::<NoParams>() {
            // Go: `if len(raw) != 0` — an absent param decodes to a nil
            // json.Value (len 0), and an empty RawValue is likewise len 0;
            // both are accepted. Only actual content (`null` included) errs.
            let raw = self.params.as_ref().map(|v| v.get()).unwrap_or("");
            if !raw.is_empty() {
                return Err(ParamsError::new(
                    ErrorCode::InvalidParams,
                    format!("expected no params, got {raw}"),
                ));
            }
            return Ok(T::default());
        }

        // The base protocol defines params as `array | object`; reject
        // anything else (absent, null, or a scalar).
        let Some(raw) = &self.params else {
            return Err(ParamsError::new(
                ErrorCode::InvalidParams,
                "params must be an object or array".to_string(),
            ));
        };
        let k = raw.get().as_bytes().first().copied().unwrap_or(0);
        if k != b'{' && k != b'[' {
            return Err(ParamsError::new(
                ErrorCode::InvalidParams,
                "params must be an object or array".to_string(),
            ));
        }
        json::unmarshal(raw.get().as_bytes(), &[])
            .map_err(|e| ParamsError::new(ErrorCode::InvalidParams, e.to_string()))
    }
}

/// `type Null struct{}` — marshals as JSON `null` and only accepts `null`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Null;

impl json::UnmarshalerFrom for Null {
    fn unmarshal_json_from<R: std::io::Read>(
        &mut self,
        dec: &mut json::Decoder<R>,
    ) -> Result<(), serde_json::Error> {
        let data = dec.read_value()?;
        if data.get() != "null" {
            return Err(serde::de::Error::custom(format!(
                "expected null, got {}",
                data.get()
            )));
        }
        Ok(())
    }
}

impl json::MarshalerTo for Null {
    fn marshal_json_to<W: std::io::Write>(
        &self,
        enc: &mut json::Encoder<W>,
    ) -> Result<(), serde_json::Error> {
        enc.write_token(&json::NULL)
    }
}

impl Serialize for Null {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_unit()
    }
}

impl<'de> Deserialize<'de> for Null {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        json::deserialize_unmarshaler_from(d)
    }
}

/// `struct{}` — Go's empty struct, used as a union arm marker (e.g.
/// `BooleanOrEmptyObject.EmptyObject`). Marshals as `{}` and accepts any
/// object (all members skipped), matching the reflective decoder.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EmptyObject;

impl Serialize for EmptyObject {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_map(Some(0))?.end()
    }
}

impl json::UnmarshalerFrom for EmptyObject {
    fn unmarshal_json_from<R: std::io::Read>(
        &mut self,
        dec: &mut json::Decoder<R>,
    ) -> Result<(), serde_json::Error> {
        if dec.peek_kind()? != b'{' {
            return Err(err_not_object(dec.peek_kind()?));
        }
        dec.read_token()?;
        while dec.peek_kind()? != b'}' {
            dec.read_value()?;
            dec.skip_value()?;
        }
        dec.read_token()?;
        Ok(())
    }
}

impl<'de> Deserialize<'de> for EmptyObject {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        json::deserialize_unmarshaler_from(d)
    }
}

/// `type NoParams struct{}` — marker type for methods taking no parameters.
/// `IsZero` -> always true, so `omitzero` omits it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct NoParams {}

impl NoParams {
    /// `func (NoParams) IsZero() bool`
    pub fn is_zero(&self) -> bool {
        true
    }
}

// --- client capabilities on the request context ---

struct ClientCapabilitiesKey;

const CLIENT_CAPABILITIES_KEY: tsc_core::context::ContextKey<
    ClientCapabilitiesKey,
    ResolvedClientCapabilities,
> = tsc_core::context::ContextKey::new();

/// `func WithClientCapabilities(ctx, caps) context.Context`
pub fn with_client_capabilities(
    ctx: &tsc_core::context::Context,
    caps: ResolvedClientCapabilities,
) -> tsc_core::context::Context {
    ctx.with_value(CLIENT_CAPABILITIES_KEY, caps)
}

/// `func GetClientCapabilities(ctx) *ResolvedClientCapabilities`
///
/// PORT: returns an owned clone — Go returns a mutable pointer but no caller
/// mutates it. Absence yields the zero (fully-disabled) capabilities.
pub fn get_client_capabilities(ctx: &tsc_core::context::Context) -> ResolvedClientCapabilities {
    ctx.value(CLIENT_CAPABILITIES_KEY)
        .cloned()
        .unwrap_or_default()
}

/// `func PreferredMarkupKind(formats []MarkupKind) MarkupKind` — first
/// (most preferred) kind, or `MarkupKind::PlainText` when empty.
pub fn preferred_markup_kind(formats: &[MarkupKind]) -> MarkupKind {
    formats.first().cloned().unwrap_or(MarkupKind::PlainText)
}

impl CodeActionKind {
    /// `func (kind CodeActionKind) Contains(other CodeActionKind) bool` —
    /// whether `other` is this kind or one of its children.
    pub fn contains(&self, other: &CodeActionKind) -> bool {
        self == other
            || *self == CodeActionKind::Empty
            || other.as_str().starts_with(&format!("{}.", self.as_str()))
    }

    /// `const CodeActionKindSourceFixAllTs = CodeActionKindSourceFixAll + ".ts"`
    pub const SOURCE_FIX_ALL_TS: CodeActionKind = CodeActionKind(Cow::Borrowed("source.fixAll.ts"));
    /// `const CodeActionKindSourceOrganizeImportsTs = ... + ".ts"`
    pub const SOURCE_ORGANIZE_IMPORTS_TS: CodeActionKind =
        CodeActionKind(Cow::Borrowed("source.organizeImports.ts"));
    /// `const CodeActionKindSourceRemoveUnusedImportsTs = CodeActionKindSource + ".removeUnusedImports.ts"`
    pub const SOURCE_REMOVE_UNUSED_IMPORTS_TS: CodeActionKind =
        CodeActionKind(Cow::Borrowed("source.removeUnusedImports.ts"));
    /// `const CodeActionKindSourceSortImportsTs = CodeActionKindSource + ".sortImports.ts"`
    pub const SOURCE_SORT_IMPORTS_TS: CodeActionKind =
        CodeActionKind(Cow::Borrowed("source.sortImports.ts"));
}

// `use super::*`-adjacent items that lsp.go references and the generated file
// needs from the crate root:
use crate::lsp_generated::{Location, Position};
