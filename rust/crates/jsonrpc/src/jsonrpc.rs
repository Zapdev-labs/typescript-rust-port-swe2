// Ported from tsc/internal/jsonrpc/jsonrpc.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Generic JSON-RPC 2.0 types and utilities that can be shared between LSP
// and other JSON-RPC based protocols.
//
// PORT: serde replaces encoding/json/v2 via the tsc-json facade. Go
// `json:"x,omitzero"` tags become `skip_serializing_if`; absent fields fall
// back to `#[serde(default)]` like Go's zero-value fill. Where Go's
// Unmarshal tolerates `"x": null` on a non-pointer field (a no-op leaving
// the zero value), `null_to_default` reproduces it.

use std::fmt;

use serde::Deserialize;
use serde::Deserializer;
use serde::Serialize;
use serde::Serializer;
use tsc_json as json;

/// `func Unmarshal` into a non-pointer Go field is a no-op for JSON `null`
/// (leaving the zero value); serde rejects it. Field-level
/// `deserialize_with` helper restoring that tolerance.
fn null_to_default<'de, D, T>(d: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de> + Default,
{
    Ok(Option::<T>::deserialize(d)?.unwrap_or_default())
}

/// `json.Value` (jsontext.Value) fields record the raw member bytes, so an
/// explicit `"x": null` survives a round trip as `Some(RawValue("null"))`
/// rather than collapsing to `None`. Absence is handled by
/// `#[serde(default)]`.
fn deserialize_raw<'de, D>(d: D) -> Result<Option<json::Value>, D::Error>
where
    D: Deserializer<'de>,
{
    Ok(Some(<json::Value>::deserialize(d)?))
}

/// `type JSONRPCVersion struct{}` — the JSON-RPC version field, always "2.0".
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JSONRPCVersion;

/// `const jsonRPCVersion = `"2.0"``
const JSONRPC_VERSION_JSON: &str = "\"2.0\"";

/// `func (JSONRPCVersion) MarshalJSON()`
impl Serialize for JSONRPCVersion {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str("2.0")
    }
}

/// `func (*JSONRPCVersion) UnmarshalJSON(data []byte)` —
/// `ErrInvalidJSONRPCVersion` becomes a serde custom error.
impl<'de> Deserialize<'de> for JSONRPCVersion {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        // PORT: Go compares the raw token bytes (`string(data) != `"2.0"``);
        // RawValue keeps the byte-for-byte check — an equivalently escaped
        // spelling like "\u0032.0" is rejected just as in Go.
        let raw = <json::Value>::deserialize(d)?;
        if raw.get() != JSONRPC_VERSION_JSON {
            return Err(serde::de::Error::custom("invalid JSON-RPC version"));
        }
        Ok(JSONRPCVersion)
    }
}

/// `type ID struct { str string; int int32 }` — a JSON-RPC message ID, either
/// a string or an integer.
///
/// PORT: Go distinguishes string vs integer IDs by `str != ""`, so an empty
/// string ID is indistinguishable from the integer 0 — preserved verbatim.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ID {
    str: String,
    int: i32,
}

/// `func NewID(rawValue IntegerOrString) *ID`
///
/// PORT: returns a value, not a pointer; Go's nil-deref panic when neither
/// IntegerOrString field is set becomes an `expect` panic.
pub fn new_id(raw_value: IntegerOrString) -> ID {
    if let Some(s) = raw_value.string {
        return ID { str: s, int: 0 };
    }
    ID {
        str: String::new(),
        int: raw_value
            .integer
            .expect("NewID: IntegerOrString.Integer must be set when String is not"),
    }
}

/// `func NewIDString(str string) *ID`
pub fn new_id_string(s: &str) -> ID {
    ID {
        str: s.to_string(),
        int: 0,
    }
}

/// `func NewIDInt(i int32) *ID`
pub fn new_id_int(i: i32) -> ID {
    ID {
        str: String::new(),
        int: i,
    }
}

impl ID {
    /// `func (id *ID) TryInt() (int32, bool)` — the nil-receiver case folds
    /// into `Option<ID>` at call sites.
    pub fn try_int(&self) -> Option<i32> {
        if !self.str.is_empty() {
            return None;
        }
        Some(self.int)
    }

    /// `func (id *ID) MustInt() int32`
    pub fn must_int(&self) -> i32 {
        if !self.str.is_empty() {
            panic!("ID is not an integer");
        }
        self.int
    }
}

/// `func (id *ID) String() string`
impl fmt::Display for ID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.str.is_empty() {
            return f.write_str(&self.str);
        }
        // `strconv.Itoa(int(id.int))`
        write!(f, "{}", self.int)
    }
}

/// `func (id *ID) MarshalJSON()`
impl Serialize for ID {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        if !self.str.is_empty() {
            return self.str.serialize(s);
        }
        self.int.serialize(s)
    }
}

/// `func (id *ID) UnmarshalJSON(data []byte)`
impl<'de> Deserialize<'de> for ID {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        // PORT: Go resets the receiver, unmarshals into `str` when the first
        // byte is '"', else into `int`. `null` reaches the int branch where
        // Go's Unmarshal is a no-op leaving the zero ID — serde_json would
        // reject `null` for i32, so it is handled explicitly. Other
        // non-string/non-number tokens (e.g. `true`) fail in both.
        let raw = <json::Value>::deserialize(d)?;
        let bytes = raw.get();
        if bytes.as_bytes().first() == Some(&b'"') {
            return Ok(ID {
                str: serde_json::from_str(bytes).map_err(serde::de::Error::custom)?,
                int: 0,
            });
        }
        if bytes == "null" {
            return Ok(ID::default());
        }
        Ok(ID {
            str: String::new(),
            int: serde_json::from_str(bytes).map_err(serde::de::Error::custom)?,
        })
    }
}

/// `type IntegerOrString struct` — a helper for creating IDs.
#[derive(Clone, Debug, Default)]
pub struct IntegerOrString {
    /// `Integer *int32`
    pub integer: Option<i32>,
    /// `String *string`
    pub string: Option<String>,
}

/// `type ResponseError struct` — a JSON-RPC error response.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ResponseError {
    /// `Code int32 json:"code"`
    #[serde(rename = "code", default, deserialize_with = "null_to_default")]
    pub code: i32,
    /// `Message string json:"message"`
    #[serde(rename = "message", default, deserialize_with = "null_to_default")]
    pub message: String,
    /// `Data any json:"data,omitzero"` — `null` unmarshals to a nil interface
    /// and re-omits, so `Option<serde_json::Value>` is the exact analog.
    #[serde(rename = "data", default, skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

/// `func (r *ResponseError) String() string` — the nil-receiver case is a
/// call-site `Option<ResponseError>` concern.
impl fmt::Display for ResponseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // PORT: Go prints the marshaled Data only when Marshal fails (where
        // the returned bytes are nil, rendered "[]" by %v); on success the
        // code/message stand alone.
        match json::marshal(&self.data, &[]) {
            Ok(_) => write!(f, "[{}]: {}", self.code, self.message),
            Err(_) => write!(f, "[{}]: {}\n[]", self.code, self.message),
        }
    }
}

/// `func (r *ResponseError) Error() string`
impl std::error::Error for ResponseError {}

/// Standard JSON-RPC error codes — `const ( CodeParseError int32 = -32700; ... )`.
pub const CODE_PARSE_ERROR: i32 = -32700;
/// `CodeInvalidRequest`
pub const CODE_INVALID_REQUEST: i32 = -32600;
/// `CodeMethodNotFound`
pub const CODE_METHOD_NOT_FOUND: i32 = -32601;
/// `CodeInvalidParams`
pub const CODE_INVALID_PARAMS: i32 = -32602;
/// `CodeInternalError`
pub const CODE_INTERNAL_ERROR: i32 = -32603;

/// `type MessageKind int` — what type of message this is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MessageKind {
    /// `MessageKindNotification` (iota = 0)
    Notification,
    /// `MessageKindRequest` (iota = 1)
    Request,
    /// `MessageKindResponse` (iota = 2)
    Response,
}

/// `type Message struct` — a raw JSON-RPC message that can be a request,
/// notification, or response. Like the Go original, params/result are kept
/// as raw JSON for generic handling.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Message {
    /// `JSONRPC JSONRPCVersion json:"jsonrpc"`
    #[serde(rename = "jsonrpc", default)]
    pub jsonrpc: JSONRPCVersion,
    /// `ID *ID json:"id,omitzero"` — `"id": null` decodes to nil in Go and
    /// `None` here; both omit the member on marshal.
    #[serde(rename = "id", default, skip_serializing_if = "Option::is_none")]
    pub id: Option<ID>,
    /// `Method string json:"method,omitzero"`
    #[serde(
        rename = "method",
        default,
        skip_serializing_if = "String::is_empty",
        deserialize_with = "null_to_default"
    )]
    pub method: String,
    /// `Params json.Value json:"params,omitzero"` — see `deserialize_raw`.
    #[serde(
        rename = "params",
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "deserialize_raw"
    )]
    pub params: Option<json::Value>,
    /// `Result json.Value json:"result,omitzero"` — see `deserialize_raw`.
    #[serde(
        rename = "result",
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "deserialize_raw"
    )]
    pub result: Option<json::Value>,
    /// `Error *ResponseError json:"error,omitzero"`
    #[serde(rename = "error", default, skip_serializing_if = "Option::is_none")]
    pub error: Option<ResponseError>,
}

impl Message {
    /// `func (m *Message) Kind() MessageKind`
    pub fn kind(&self) -> MessageKind {
        if self.id.is_some() && self.method.is_empty() {
            return MessageKind::Response;
        }
        if self.id.is_none() {
            return MessageKind::Notification;
        }
        MessageKind::Request
    }

    /// `func (m *Message) IsRequest() bool` — has ID and method.
    pub fn is_request(&self) -> bool {
        self.id.is_some() && !self.method.is_empty()
    }

    /// `func (m *Message) IsNotification() bool` — has method but no ID.
    pub fn is_notification(&self) -> bool {
        self.id.is_none() && !self.method.is_empty()
    }

    /// `func (m *Message) IsResponse() bool` — has ID but no method.
    pub fn is_response(&self) -> bool {
        self.id.is_some() && self.method.is_empty()
    }
}

/// `type RequestMessage struct` — a convenience type for creating
/// request/notification messages.
///
/// PORT: `Params any` becomes generic `params: Option<T>` (default
/// `serde_json::Value`); `None` omits the member like a nil interface, and
/// `Some(serde_json::Value::Null)` / `Some(json::Value("null"))` emits an
/// explicit `"params":null` like a non-nil interface holding `null`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RequestMessage<T = serde_json::Value> {
    /// `JSONRPC JSONRPCVersion json:"jsonrpc"`
    #[serde(rename = "jsonrpc", default)]
    pub jsonrpc: JSONRPCVersion,
    /// `ID *ID json:"id,omitzero"`
    #[serde(rename = "id", default, skip_serializing_if = "Option::is_none")]
    pub id: Option<ID>,
    /// `Method string json:"method"` — no omitzero; always emitted.
    #[serde(rename = "method", default, deserialize_with = "null_to_default")]
    pub method: String,
    /// `Params any json:"params,omitzero"`
    #[serde(rename = "params", default, skip_serializing_if = "Option::is_none")]
    pub params: Option<T>,
}

/// `type ResponseMessage struct` — a convenience type for creating response
/// messages.
///
/// PORT: `Result any` is generic like `RequestMessage::params`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ResponseMessage<T = serde_json::Value> {
    /// `JSONRPC JSONRPCVersion json:"jsonrpc"`
    #[serde(rename = "jsonrpc", default)]
    pub jsonrpc: JSONRPCVersion,
    /// `ID *ID json:"id,omitzero"`
    #[serde(rename = "id", default, skip_serializing_if = "Option::is_none")]
    pub id: Option<ID>,
    /// `Result any json:"result,omitzero"`
    #[serde(rename = "result", default, skip_serializing_if = "Option::is_none")]
    pub result: Option<T>,
    /// `Error *ResponseError json:"error,omitzero"`
    #[serde(rename = "error", default, skip_serializing_if = "Option::is_none")]
    pub error: Option<ResponseError>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw(s: &str) -> json::Value {
        serde_json::value::RawValue::from_string(s.to_string()).unwrap()
    }

    #[test]
    fn version_round_trip() {
        assert_eq!(json::marshal(&JSONRPCVersion, &[]).unwrap(), b"\"2.0\"");
        let v: JSONRPCVersion = json::unmarshal(b"\"2.0\"", &[]).unwrap();
        assert_eq!(v, JSONRPCVersion);
        assert!(json::unmarshal::<JSONRPCVersion>(b"\"1.0\"", &[]).is_err());
        assert!(json::unmarshal::<JSONRPCVersion>(b"2.0", &[]).is_err());
        // Byte-for-byte comparison, as in Go: escaped "2.0" is rejected.
        assert!(json::unmarshal::<JSONRPCVersion>(b"\"\\u0032.0\"", &[]).is_err());
    }

    #[test]
    fn id_round_trip() {
        let id = new_id_int(-7);
        assert_eq!(id.to_string(), "-7");
        assert_eq!(id.try_int(), Some(-7));
        assert_eq!(id.must_int(), -7);
        assert_eq!(json::marshal(&id, &[]).unwrap(), b"-7");

        let id = new_id_string("abc");
        assert_eq!(id.to_string(), "abc");
        assert_eq!(id.try_int(), None);
        assert_eq!(json::marshal(&id, &[]).unwrap(), b"\"abc\"");

        let id: ID = json::unmarshal(b"\"xyz\"", &[]).unwrap();
        assert_eq!(id, new_id_string("xyz"));
        let id: ID = json::unmarshal(b"42", &[]).unwrap();
        assert_eq!(id, new_id_int(42));
        // `null` unmarshals to the zero ID (Go no-op on the int branch).
        let id: ID = json::unmarshal(b"null", &[]).unwrap();
        assert_eq!(id, ID::default());
        // Non-numeric, non-string tokens error.
        assert!(json::unmarshal::<ID>(b"true", &[]).is_err());
        assert!(json::unmarshal::<ID>(b"1.5", &[]).is_err());
    }

    #[test]
    fn new_id_from_integer_or_string() {
        assert_eq!(
            new_id(IntegerOrString {
                integer: Some(3),
                string: None,
            }),
            new_id_int(3)
        );
        // String wins when both are set, as in Go.
        assert_eq!(
            new_id(IntegerOrString {
                integer: Some(3),
                string: Some("s".into()),
            }),
            new_id_string("s")
        );
    }

    #[test]
    fn message_kinds() {
        let req: Message = json::unmarshal(
            br#"{"jsonrpc":"2.0","id":1,"method":"m","params":{"a":1}}"#,
            &[],
        )
        .unwrap();
        assert_eq!(req.kind(), MessageKind::Request);
        assert!(req.is_request());
        assert!(!req.is_notification());
        assert!(!req.is_response());
        assert_eq!(req.id.as_ref().unwrap().must_int(), 1);
        assert_eq!(req.params.as_ref().unwrap().get(), "{\"a\":1}");

        let notif: Message = json::unmarshal(br#"{"jsonrpc":"2.0","method":"m"}"#, &[]).unwrap();
        assert_eq!(notif.kind(), MessageKind::Notification);
        assert!(notif.is_notification());

        let resp: Message =
            json::unmarshal(br#"{"jsonrpc":"2.0","id":"r1","result":true}"#, &[]).unwrap();
        assert_eq!(resp.kind(), MessageKind::Response);
        assert!(resp.is_response());
        assert_eq!(resp.id.as_ref().unwrap(), &new_id_string("r1"));

        // `"id":null` decodes to nil in Go — still a notification.
        let null_id: Message =
            json::unmarshal(br#"{"jsonrpc":"2.0","id":null,"method":"m"}"#, &[]).unwrap();
        assert!(null_id.is_notification());
    }

    #[test]
    fn message_preserves_explicit_null_params() {
        let msg: Message =
            json::unmarshal(br#"{"jsonrpc":"2.0","method":"m","params":null}"#, &[]).unwrap();
        assert_eq!(msg.params.as_ref().unwrap().get(), "null");
        let out = json::marshal(&msg, &[]).unwrap();
        assert_eq!(out, br#"{"jsonrpc":"2.0","method":"m","params":null}"#);

        // Absent params omit the member entirely.
        let msg: Message = json::unmarshal(br#"{"jsonrpc":"2.0","method":"m"}"#, &[]).unwrap();
        assert!(msg.params.is_none());
        assert_eq!(
            json::marshal(&msg, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","method":"m"}"#
        );
    }

    #[test]
    fn message_marshal_order_and_omits() {
        let msg = Message {
            jsonrpc: JSONRPCVersion,
            id: Some(new_id_int(3)),
            result: Some(raw("true")),
            ..Default::default()
        };
        assert_eq!(
            json::marshal(&msg, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","id":3,"result":true}"#
        );

        let msg = Message {
            jsonrpc: JSONRPCVersion,
            id: Some(new_id_int(3)),
            error: Some(ResponseError {
                code: CODE_METHOD_NOT_FOUND,
                message: "nope".into(),
                data: None,
            }),
            ..Default::default()
        };
        assert_eq!(
            json::marshal(&msg, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","id":3,"error":{"code":-32601,"message":"nope"}}"#
        );
    }

    #[test]
    fn message_tolerates_null_fields() {
        // Go leaves zero values for `"x":null` on non-pointer fields.
        let msg: Message = json::unmarshal(
            br#"{"jsonrpc":"2.0","id":1,"method":null,"error":null}"#,
            &[],
        )
        .unwrap();
        assert_eq!(msg.method, "");
        assert!(msg.error.is_none());
        assert!(msg.is_response());
    }

    #[test]
    fn request_and_response_message_marshal() {
        let req = RequestMessage::<serde_json::Value> {
            jsonrpc: JSONRPCVersion,
            id: Some(new_id_int(7)),
            method: "textDocument/hover".into(),
            params: None,
        };
        assert_eq!(
            json::marshal(&req, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","id":7,"method":"textDocument/hover"}"#
        );

        // Notification form: no id member.
        let notif = RequestMessage::<serde_json::Value> {
            jsonrpc: JSONRPCVersion,
            id: None,
            method: "exit".into(),
            params: None,
        };
        assert_eq!(
            json::marshal(&notif, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","method":"exit"}"#
        );

        // Generic params — a typed struct serializes in place.
        #[derive(Serialize)]
        struct Params {
            line: u32,
        }
        let req = RequestMessage {
            jsonrpc: JSONRPCVersion,
            id: Some(new_id_string("x")),
            method: "m".into(),
            params: Some(Params { line: 1 }),
        };
        assert_eq!(
            json::marshal(&req, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","id":"x","method":"m","params":{"line":1}}"#
        );

        // An explicit null result is emitted, not omitted (Go: `any` holding
        // json.Value("null")).
        let resp = ResponseMessage::<serde_json::Value> {
            jsonrpc: JSONRPCVersion,
            id: Some(new_id_int(1)),
            result: Some(serde_json::Value::Null),
            error: None,
        };
        assert_eq!(
            json::marshal(&resp, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","id":1,"result":null}"#
        );

        let err = ResponseMessage::<serde_json::Value> {
            jsonrpc: JSONRPCVersion,
            id: Some(new_id_int(1)),
            result: None,
            error: Some(ResponseError {
                code: CODE_PARSE_ERROR,
                message: "bad".into(),
                data: Some(serde_json::json!({"detail": 1})),
            }),
        };
        assert_eq!(
            json::marshal(&err, &[]).unwrap(),
            br#"{"jsonrpc":"2.0","id":1,"error":{"code":-32700,"message":"bad","data":{"detail":1}}}"#
        );
    }

    #[test]
    fn response_error_display() {
        let e = ResponseError {
            code: CODE_INVALID_PARAMS,
            message: "bad params".into(),
            data: None,
        };
        assert_eq!(e.to_string(), "[-32602]: bad params");
        let e: ResponseError =
            json::unmarshal(br#"{"code":-32603,"message":"oops","data":{"x":2}}"#, &[]).unwrap();
        assert_eq!(e.to_string(), "[-32603]: oops");
        assert_eq!(e.data.as_ref().unwrap(), &serde_json::json!({"x": 2}));
    }
}
