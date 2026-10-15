// Ported from tsc/internal/ipc/protocol_jsonrpc.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `NewJSONRPCProtocol(rw)` hands one `io.ReadWriter` to both
// `jsonrpc.NewReader` and `jsonrpc.NewWriter`. Rust needs owned halves, so a
// single stream is shared as `Arc<S>` behind `SharedIo`, which forwards
// `Read`/`Write` through `&S` — std provides those impls for `&UnixStream`
// and `&TcpStream`. The reader and writer each get their own `Mutex` so a
// read blocked on the peer never stalls a handler's write, matching Go where
// the stream itself is safe for concurrent Read/Write.

use std::io;
use std::sync::{Arc, Mutex};

use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::{Error, Message, Protocol};

/// A read/write half sharing one `Arc<S>` — the Rust equivalent of passing a
/// single `io.ReadWriter` to both `jsonrpc.NewReader` and `jsonrpc.NewWriter`.
/// Requires `&S: Read`/`Write` (see [`new_json_rpc_protocol`]).
pub struct SharedIo<S: ?Sized>(pub Arc<S>);

impl<S: ?Sized> Clone for SharedIo<S> {
    fn clone(&self) -> Self {
        SharedIo(self.0.clone())
    }
}

impl<S: ?Sized> io::Read for SharedIo<S>
where
    for<'a> &'a S: io::Read,
{
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut half = &*self.0;
        half.read(buf)
    }
}

impl<S: ?Sized> io::Write for SharedIo<S>
where
    for<'a> &'a S: io::Write,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let mut half = &*self.0;
        half.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        let mut half = &*self.0;
        half.flush()
    }
}

/// `type JSONRPCProtocol struct` — the `Protocol` implementation using
/// JSON-RPC 2.0 with the LSP base protocol framing (Content-Length headers).
pub struct JsonRpcProtocol<R: io::Read + Send, W: io::Write + Send> {
    /// `reader *jsonrpc.Reader`
    reader: Mutex<jsonrpc::Reader<R>>,
    /// `writer *jsonrpc.Writer`
    writer: Mutex<jsonrpc::Writer<W>>,
}

impl<R: io::Read + Send, W: io::Write + Send> JsonRpcProtocol<R, W> {
    /// Builds a protocol over separate read/write halves — the shape Go gets
    /// for free from a single `io.ReadWriter` (see [`new_json_rpc_protocol`],
    /// the `NewJSONRPCProtocol` port).
    pub fn from_halves(read: R, write: W) -> Self {
        JsonRpcProtocol {
            reader: Mutex::new(jsonrpc::new_reader(read)),
            writer: Mutex::new(jsonrpc::new_writer(write)),
        }
    }
}

/// `func NewJSONRPCProtocol(rw io.ReadWriter) *JSONRPCProtocol`
pub fn new_json_rpc_protocol<S>(rw: Arc<S>) -> JsonRpcProtocol<SharedIo<S>, SharedIo<S>>
where
    S: Send + Sync + 'static + ?Sized,
    for<'a> &'a S: io::Read + io::Write,
{
    JsonRpcProtocol::from_halves(SharedIo(rw.clone()), SharedIo(rw))
}

impl<R: io::Read + Send, W: io::Write + Send> Protocol for JsonRpcProtocol<R, W> {
    /// `ReadMessage`
    fn read_message(&self) -> Result<Message, Error> {
        let data = self.reader.lock().unwrap().read().map_err(Error::from)?;
        Ok(json::unmarshal(&data, &[])?)
    }

    /// `WriteRequest`
    fn write_request(
        &self,
        id: Option<&jsonrpc::ID>,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), Error> {
        let msg = jsonrpc::RequestMessage::<json::Value> {
            jsonrpc: jsonrpc::JSONRPCVersion,
            id: id.cloned(),
            method: method.to_string(),
            params,
        };
        let data = json::marshal(&msg, &[])?;
        Ok(self.writer.lock().unwrap().write(&data)?)
    }

    /// `WriteNotification`
    fn write_notification(&self, method: &str, params: Option<json::Value>) -> Result<(), Error> {
        let msg = jsonrpc::RequestMessage::<json::Value> {
            jsonrpc: jsonrpc::JSONRPCVersion,
            id: None,
            method: method.to_string(),
            params,
        };
        let data = json::marshal(&msg, &[])?;
        Ok(self.writer.lock().unwrap().write(&data)?)
    }

    /// `WriteResponse`
    fn write_response(
        &self,
        id: Option<&jsonrpc::ID>,
        result: Option<crate::ResponsePayload>,
    ) -> Result<(), Error> {
        // Go: `if result == nil { result = json.Value("null") }` — a nil
        // `any` still produces an explicit `"result":null`.
        let result = match result {
            Some(crate::ResponsePayload::Json(r)) => Some(r),
            // `json.Marshal(api.RawBinary)` — Go marshals `[]byte` as a
            // base64 string. Unreached today: `UseBinaryResponses` is only
            // set on the msgpack path.
            Some(crate::ResponsePayload::Binary(b)) => {
                Some(crate::marshal_params(&base64_std_encode(&b))?)
            }
            None => Some(crate::marshal_params(&serde_json::Value::Null)?),
        };
        let msg = jsonrpc::ResponseMessage::<json::Value> {
            jsonrpc: jsonrpc::JSONRPCVersion,
            id: id.cloned(),
            result,
            error: None,
        };
        let data = json::marshal(&msg, &[])?;
        Ok(self.writer.lock().unwrap().write(&data)?)
    }

    /// `WriteError`
    fn write_error(
        &self,
        id: Option<&jsonrpc::ID>,
        resp_err: &jsonrpc::ResponseError,
    ) -> Result<(), Error> {
        let msg = jsonrpc::ResponseMessage::<json::Value> {
            jsonrpc: jsonrpc::JSONRPCVersion,
            id: id.cloned(),
            result: None,
            error: Some(resp_err.clone()),
        };
        let data = json::marshal(&msg, &[])?;
        Ok(self.writer.lock().unwrap().write(&data)?)
    }
}

/// `base64.StdEncoding.EncodeToString` — the alphabet `encoding/json` uses
/// when marshaling `[]byte`. (`tsc-sourcemap`'s port is not a dependency of
/// this crate.) Exported for `LoggingProtocol`-style wrappers that must
/// render `ResponsePayload::Binary` the way `json.Marshal` would.
pub fn base64_std_encode(data: &[u8]) -> String {
    const ALPHABET: &[u8; 64] =
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(data.len().div_ceil(3) * 4);
    for chunk in data.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = *chunk.get(1).unwrap_or(&0) as u32;
        let b2 = *chunk.get(2).unwrap_or(&0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(ALPHABET[(n >> 18) as usize & 63] as char);
        out.push(ALPHABET[(n >> 12) as usize & 63] as char);
        out.push(if chunk.len() > 1 {
            ALPHABET[(n >> 6) as usize & 63] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            ALPHABET[n as usize & 63] as char
        } else {
            '='
        });
    }
    out
}
