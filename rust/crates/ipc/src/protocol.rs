// Ported from tsc/internal/ipc/protocol.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `Protocol` methods take `&self` (not `&mut self`) because the async
// connection's handler threads write while the run loop reads — Go's
// `io.ReadWriter` halves are independently usable, so implementations keep
// per-half internal locks (`Mutex` inside `JsonRpcProtocol`).
//
// `id *jsonrpc.ID` → `Option<&jsonrpc::ID>`; `params any` →
// `Option<json::Value>` (pre-marshaled raw JSON — trait-object safety forbids
// generic methods; `None` behaves like a nil interface). `result any` →
// `Option<ResponsePayload>` — the enum carries the `api.RawBinary` case
// (`MessagePackProtocol.WriteResponse`'s non-JSON payload fast-path) that
// `json::Value` cannot express.

use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::Error;

/// `type Message = jsonrpc.Message` — alias for convenience.
pub type Message = jsonrpc::Message;

/// The `any` of `Handler.HandleRequest` results and
/// `Protocol.WriteResponse(id, result)`: raw JSON text, or `api.RawBinary`'s
/// non-JSON payload bytes.
pub enum ResponsePayload {
    /// Raw JSON — the `json.Value` case. Written verbatim by JSON
    /// protocols and as the msgpack payload bytes by
    /// `MessagePackProtocol`.
    Json(json::Value),
    /// `api.RawBinary` — non-JSON bytes. `MessagePackProtocol` writes them
    /// verbatim; JSON protocols marshal them like Go's
    /// `json.Marshal([]byte)` (a base64 string).
    Binary(Vec<u8>),
}

/// A `json::Value` is always the `Json` case.
impl From<json::Value> for ResponsePayload {
    fn from(v: json::Value) -> Self {
        ResponsePayload::Json(v)
    }
}

/// `type Protocol interface` — reading and writing API messages.
pub trait Protocol: Send + Sync {
    /// `ReadMessage() (*Message, error)`
    fn read_message(&self) -> Result<Message, Error>;
    /// `WriteRequest(id *jsonrpc.ID, method string, params any) error`
    fn write_request(
        &self,
        id: Option<&jsonrpc::ID>,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), Error>;
    /// `WriteNotification(method string, params any) error`
    fn write_notification(&self, method: &str, params: Option<json::Value>) -> Result<(), Error>;
    /// `WriteResponse(id *jsonrpc.ID, result any) error`
    fn write_response(
        &self,
        id: Option<&jsonrpc::ID>,
        result: Option<ResponsePayload>,
    ) -> Result<(), Error>;
    /// `WriteError(id *jsonrpc.ID, err *jsonrpc.ResponseError) error`
    fn write_error(
        &self,
        id: Option<&jsonrpc::ID>,
        err: &jsonrpc::ResponseError,
    ) -> Result<(), Error>;
}
