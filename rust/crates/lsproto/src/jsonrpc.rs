// Ported from tsc/internal/lsp/lsproto/jsonrpc.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use serde::{Deserialize, Serialize};
use tsc_json as json;

use crate::lsp::Method;
use crate::lsp_generated::{ErrorCode, IntegerOrString};

/// `func NewID(rawValue IntegerOrString) *jsonrpc.ID` — creates a JSON-RPC ID
/// from an lsproto `IntegerOrString` (distinct from `jsonrpc.IntegerOrString`).
///
/// PORT: Go nil-derefs when `Integer` is unset and `String` is nil; `expect`
/// preserves the panic.
pub fn new_id(raw_value: &IntegerOrString) -> tsc_jsonrpc::ID {
    if let Some(s) = &raw_value.string {
        return tsc_jsonrpc::new_id_string(s);
    }
    tsc_jsonrpc::new_id_int(
        raw_value
            .integer
            .expect("NewID: IntegerOrString.Integer must be set when String is not"),
    )
}

/// `type Message struct` — a decoded inbound message: request, notification,
/// or response, per `Kind`.
#[derive(Debug)]
pub struct Message {
    pub kind: tsc_jsonrpc::MessageKind,
    msg: MessagePayload,
}

#[derive(Debug)]
enum MessagePayload {
    Request(RequestMessage),
    Response(ResponseMessage),
}

impl Message {
    /// `func (m *Message) AsRequest() *RequestMessage` — panics when `Kind` is
    /// not a request/notification, matching the Go type assertion.
    pub fn as_request(&self) -> &RequestMessage {
        match &self.msg {
            MessagePayload::Request(r) => r,
            _ => panic!("Message.AsRequest: message is not a request"),
        }
    }

    /// `func (m *Message) AsResponse() *ResponseMessage`
    pub fn as_response(&self) -> &ResponseMessage {
        match &self.msg {
            MessagePayload::Response(r) => r,
            _ => panic!("Message.AsResponse: message is not a response"),
        }
    }
}

/// Wire shape used to discriminate inbound messages: `params`/`result` stay
/// raw because the response carries no method to pick a type by.
#[derive(Deserialize)]
struct RawMessage {
    #[serde(rename = "jsonrpc", default)]
    #[allow(dead_code)]
    jsonrpc: tsc_jsonrpc::JSONRPCVersion,
    /// `ID *jsonrpc.ID` — `"id": null` decodes to nil / `None`.
    #[serde(rename = "id", default)]
    id: Option<tsc_jsonrpc::ID>,
    #[serde(
        rename = "method",
        default,
        deserialize_with = "crate::null_to_default"
    )]
    method: Method,
    /// `Params json.Value` — raw member bytes, including an explicit `null`.
    #[serde(rename = "params", default, deserialize_with = "deserialize_raw")]
    params: Option<json::Value>,
    /// `Result json.Value` — same.
    #[serde(rename = "result", default, deserialize_with = "deserialize_raw")]
    result: Option<json::Value>,
    #[serde(rename = "error", default)]
    error: Option<tsc_jsonrpc::ResponseError>,
}

/// `json.Value` member decode: absence is `#[serde(default)]`'s job; an
/// explicit `null` member must survive as `Some(RawValue("null"))` (the Go
/// `len(raw) > 0` check treats `"null"` as present).
fn deserialize_raw<'de, D>(d: D) -> Result<Option<json::Value>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    Ok(Some(<json::Value>::deserialize(d)?))
}

/// `func (m *Message) UnmarshalJSON(data []byte) error`
impl<'de> Deserialize<'de> for Message {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let raw = RawMessage::deserialize(d).map_err(|e| {
            serde::de::Error::custom(format!("{}: {}", ErrorCode::InvalidRequest, e))
        })?;
        if raw.id.is_some() && raw.method.is_empty() {
            return Ok(Message {
                kind: tsc_jsonrpc::MessageKind::Response,
                msg: MessagePayload::Response(ResponseMessage {
                    jsonrpc: tsc_jsonrpc::JSONRPCVersion,
                    id: raw.id,
                    result: raw.result,
                    error: raw.error,
                }),
            });
        }

        let kind = if raw.id.is_none() {
            tsc_jsonrpc::MessageKind::Notification
        } else {
            tsc_jsonrpc::MessageKind::Request
        };
        Ok(Message {
            kind,
            msg: MessagePayload::Request(RequestMessage {
                jsonrpc: tsc_jsonrpc::JSONRPCVersion,
                id: raw.id,
                method: raw.method,
                params: raw.params,
            }),
        })
    }
}

/// `func (m *Message) MarshalJSON() ([]byte, error)`
impl Serialize for Message {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        match &self.msg {
            MessagePayload::Request(r) => r.serialize(s),
            MessagePayload::Response(r) => r.serialize(s),
        }
    }
}

/// `type RequestMessage struct` — an inbound request/notification (or a
/// message being constructed outbound).
#[derive(Clone, Debug, Default, Serialize)]
pub struct RequestMessage {
    /// `JSONRPC jsonrpc.JSONRPCVersion json:"jsonrpc"`
    #[serde(rename = "jsonrpc")]
    pub jsonrpc: tsc_jsonrpc::JSONRPCVersion,
    /// `ID *jsonrpc.ID json:"id,omitzero"`
    #[serde(rename = "id", skip_serializing_if = "Option::is_none")]
    pub id: Option<tsc_jsonrpc::ID>,
    /// `Method Method json:"method"`
    #[serde(rename = "method")]
    pub method: Method,
    /// `Params any json:"params,omitzero"`
    ///
    /// PORT: inbound messages store the raw `json.Value`; outbound
    /// [`crate::RequestInfo::new_request_message`] marshals typed params to a
    /// `json::Value` eagerly. `None` omits the member like a nil interface.
    #[serde(rename = "params", skip_serializing_if = "Option::is_none")]
    pub params: Option<json::Value>,
}

impl RequestMessage {
    /// `func (r *RequestMessage) Message() *Message`
    pub fn message(self) -> Message {
        let kind = if self.id.is_none() {
            tsc_jsonrpc::MessageKind::Notification
        } else {
            tsc_jsonrpc::MessageKind::Request
        };
        Message {
            kind,
            msg: MessagePayload::Request(self),
        }
    }
}

/// `func (r *RequestMessage) UnmarshalJSON(data []byte) error`
impl<'de> Deserialize<'de> for RequestMessage {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let raw = RawMessage::deserialize(d).map_err(|e| {
            serde::de::Error::custom(format!("{}: {}", ErrorCode::InvalidRequest, e))
        })?;
        Ok(RequestMessage {
            jsonrpc: raw.jsonrpc,
            id: raw.id,
            method: raw.method,
            params: raw.params,
        })
    }
}

/// `type ResponseMessage struct` — an inbound response (or one being built
/// outbound).
#[derive(Clone, Debug, Default, Serialize)]
pub struct ResponseMessage {
    /// `JSONRPC jsonrpc.JSONRPCVersion json:"jsonrpc"`
    #[serde(rename = "jsonrpc")]
    pub jsonrpc: tsc_jsonrpc::JSONRPCVersion,
    /// `ID *jsonrpc.ID json:"id"`
    #[serde(rename = "id")]
    pub id: Option<tsc_jsonrpc::ID>,
    /// `Result any json:"result,omitzero"`
    ///
    /// PORT: `any` becomes `Option<json::Value>` — inbound decode stores the
    /// raw result bytes (the method, hence the result type, is unavailable),
    /// and outbound callers marshal the typed result through
    /// [`crate::RequestInfo::unmarshal_result`]'s counterpart.
    #[serde(rename = "result", skip_serializing_if = "Option::is_none")]
    pub result: Option<json::Value>,
    /// `Error *jsonrpc.ResponseError json:"error,omitzero"`
    #[serde(rename = "error", skip_serializing_if = "Option::is_none")]
    pub error: Option<tsc_jsonrpc::ResponseError>,
}

impl ResponseMessage {
    /// `func (r *ResponseMessage) Message() *Message`
    pub fn message(self) -> Message {
        Message {
            kind: tsc_jsonrpc::MessageKind::Response,
            msg: MessagePayload::Response(self),
        }
    }
}

/// ResponseMessage uses the default unmarshal in Go; keeping the raw `result`
/// bytes is more faithful to how [`Message`] populates it.
impl<'de> Deserialize<'de> for ResponseMessage {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let raw = RawMessage::deserialize(d)?;
        Ok(ResponseMessage {
            jsonrpc: raw.jsonrpc,
            id: raw.id,
            result: raw.result,
            error: raw.error,
        })
    }
}
