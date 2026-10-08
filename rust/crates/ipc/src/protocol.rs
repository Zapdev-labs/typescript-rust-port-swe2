// Ported from tsc/internal/ipc/protocol.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `Protocol` methods take `&self` (not `&mut self`) because the async
// connection's handler threads write while the run loop reads — Go's
// `io.ReadWriter` halves are independently usable, so implementations keep
// per-half internal locks (`Mutex` inside `JsonRpcProtocol`).
//
// `id *jsonrpc.ID` → `Option<&jsonrpc::ID>`; `params any` / `result any` →
// `Option<json::Value>` (pre-marshaled raw JSON — trait-object safety forbids
// generic methods; `None` behaves like a nil interface). Note for the future
// `api` port: `MessagePackProtocol.WriteResponse`'s `RawBinary` fast-path
// (non-JSON payload bytes) cannot be expressed as `json::Value` and will
// need a dedicated escape hatch.

use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::Error;

/// `type Message = jsonrpc.Message` — alias for convenience.
pub type Message = jsonrpc::Message;

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
        result: Option<json::Value>,
    ) -> Result<(), Error>;
    /// `WriteError(id *jsonrpc.ID, err *jsonrpc.ResponseError) error`
    fn write_error(
        &self,
        id: Option<&jsonrpc::ID>,
        err: &jsonrpc::ResponseError,
    ) -> Result<(), Error>;
}
