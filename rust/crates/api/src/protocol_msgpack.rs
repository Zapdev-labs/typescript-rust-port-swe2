// Ported from tsc/internal/api/protocol_msgpack.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `bufio.Reader`/`bufio.Writer` → `std::io::BufReader`/`BufWriter`,
// each behind a `Mutex` (the `Protocol` methods take `&self`; Go's halves
// are used from separate goroutines). `NewMessagePackProtocol(rw)` splits
// one `io.ReadWriter` — Rust gets the same via `SharedIo`. `params any` /
// `result any` arrive pre-marshaled as `Option<json::Value>`; `api.RawBinary`
// arrives as `ResponsePayload::Binary`.
//
// Go's `string(payload)` conversions become `String::from_utf8` for JSON
// payloads (they are always valid UTF-8) and `from_utf8_lossy` for the
// CallError message (Go's conversion never fails; lossy is closest).

use std::io::{self, BufReader, BufWriter, Read, Write};
use std::sync::{Arc, Mutex};

use tsc_ipc::{self as ipc, ResponsePayload, SharedIo};
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

/// `MessageType` represents the type of message in the msgpack protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum MessageType {
    Unknown = 0,
    Request = 1,
    CallResponse = 2,
    CallError = 3,
    Response = 4,
    Error = 5,
    Call = 6,
}

impl MessageType {
    /// `func (m MessageType) IsValid() bool`
    pub fn is_valid(self) -> bool {
        matches!(
            self,
            MessageType::Request
                | MessageType::CallResponse
                | MessageType::CallError
                | MessageType::Response
                | MessageType::Error
                | MessageType::Call
        )
    }

    fn from_u8(v: u8) -> MessageType {
        match v {
            1 => MessageType::Request,
            2 => MessageType::CallResponse,
            3 => MessageType::CallError,
            4 => MessageType::Response,
            5 => MessageType::Error,
            6 => MessageType::Call,
            _ => MessageType::Unknown,
        }
    }
}

// MessagePack format constants
const MSGPACK_FIXED_ARRAY3: u8 = 0x93;
const MSGPACK_BIN8: u8 = 0xC4;
const MSGPACK_BIN16: u8 = 0xC5;
const MSGPACK_BIN32: u8 = 0xC6;
const MSGPACK_U8: u8 = 0xCC;

/// `fmt.Errorf("%w: ...", ErrInvalidRequest)` — the sentinel's text plus the
/// detail, wrapped so `is`/`errors.Is`-style checks still match.
fn invalid_request(detail: String) -> ipc::Error {
    ipc::Error::Wrapped {
        msg: format!("api: invalid request: {detail}"),
        source: Box::new(ipc::Error::Message("api: invalid request".into())),
    }
}

/// `MessagePackProtocol` implements the `Protocol` interface using a custom
/// msgpack-based tuple format: `[MessageType, method, payload]`.
pub struct MessagePackProtocol<R: Read + Send, W: Write + Send> {
    r: Mutex<BufReader<R>>,
    w: Mutex<BufWriter<W>>,
}

/// `var _ ipc.Protocol = (*MessagePackProtocol)(nil)`
impl<R: Read + Send, W: Write + Send> MessagePackProtocol<R, W> {
    /// Builds a protocol over separate read/write halves — the Rust
    /// equivalent of `bufio.NewReader`/`bufio.NewWriter` over one stream.
    pub fn from_halves(read: R, write: W) -> Self {
        MessagePackProtocol {
            r: Mutex::new(BufReader::new(read)),
            w: Mutex::new(BufWriter::new(write)),
        }
    }

    /// `p.readTuple`
    fn read_tuple(&self) -> Result<(MessageType, String, Vec<u8>), ipc::Error> {
        let mut r = self.r.lock().unwrap();

        // Read fixed array marker (0x93 = 3-element array)
        let t = read_byte(&mut *r)?;
        if t != MSGPACK_FIXED_ARRAY3 {
            return Err(invalid_request(format!(
                "expected fixed 3-element array (0x93), received: 0x{t:02x}"
            )));
        }

        // Read message type - can be positive fixint (0x00-0x7F) or
        // uint8 (0xCC + value)
        let t = read_byte(&mut *r)?;
        let raw_type = if t <= 0x7F {
            // Positive fixint - the byte IS the value
            t
        } else if t == MSGPACK_U8 {
            // uint8 marker - next byte is the value
            read_byte(&mut *r)?
        } else {
            return Err(invalid_request(format!(
                "expected positive fixint or uint8 marker, received: 0x{t:02x}"
            )));
        };
        let msg_type = MessageType::from_u8(raw_type);
        if !msg_type.is_valid() {
            return Err(invalid_request(format!(
                "unknown message type: {}",
                raw_type
            )));
        }

        // Read method (binary)
        let method_bytes = read_bin(&mut *r)?;
        let method = String::from_utf8(method_bytes)
            .map_err(|e| ipc::Error::Message(e.to_string()))?;

        // Read payload (binary)
        let payload = read_bin(&mut *r)?;

        Ok((msg_type, method, payload))
    }

    /// `p.writeTuple`
    fn write_tuple(
        &self,
        msg_type: MessageType,
        method: &str,
        payload: &[u8],
    ) -> Result<(), ipc::Error> {
        let mut w = self.w.lock().unwrap();
        // Write fixed array marker
        w.write_all(&[MSGPACK_FIXED_ARRAY3])?;
        // Write message type as positive fixint (values 0-127 are written
        // directly)
        w.write_all(&[msg_type as u8])?;
        // Write method
        write_bin(&mut *w, method.as_bytes())?;
        // Write payload
        write_bin(&mut *w, payload)?;
        w.flush()?;
        Ok(())
    }
}

/// `func NewMessagePackProtocol(rw io.ReadWriter) *MessagePackProtocol`
pub fn new_message_pack_protocol<S>(rw: Arc<S>) -> MessagePackProtocol<SharedIo<S>, SharedIo<S>>
where
    S: Send + Sync + 'static + ?Sized,
    for<'a> &'a S: Read + Write,
{
    MessagePackProtocol::from_halves(SharedIo(rw.clone()), SharedIo(rw))
}

impl<R: Read + Send, W: Write + Send> ipc::Protocol for MessagePackProtocol<R, W> {
    /// `ReadMessage` — converts the msgpack tuple into a JSON-RPC-shaped
    /// `ipc::Message`, using the method as a pseudo-ID (the protocol has no
    /// explicit IDs).
    fn read_message(&self) -> Result<ipc::Message, ipc::Error> {
        let (msg_type, method, payload) = self.read_tuple()?;

        let mut msg = ipc::Message::default();
        match msg_type {
            MessageType::Request => {
                // Client request - needs an ID for response
                let id = jsonrpc::new_id_string(&method);
                msg.id = Some(id);
                msg.method = method;
                msg.params = Some(raw_json(&payload)?);
            }
            MessageType::CallResponse => {
                // Response to our Call - use method as ID
                // Note: Method must be empty for IsResponse() to return true
                let id = jsonrpc::new_id_string(&method);
                msg.id = Some(id);
                msg.result = Some(raw_json(&payload)?);
            }
            MessageType::CallError => {
                // Error response to our Call
                // Note: Method must be empty for IsResponse() to return true
                let id = jsonrpc::new_id_string(&method);
                msg.id = Some(id);
                msg.error = Some(jsonrpc::ResponseError {
                    code: jsonrpc::CODE_INTERNAL_ERROR,
                    message: String::from_utf8_lossy(&payload).into_owned(),
                    data: None,
                });
            }
            _ => {
                return Err(ipc::Error::Message(format!(
                    "unexpected message type: {}",
                    msg_type as u8
                )));
            }
        }
        Ok(msg)
    }

    /// `WriteRequest` — for msgpack protocol, requests from server are
    /// "Call" type. `json.Marshal(params)` is identity here: `params`
    /// already arrives as raw JSON.
    fn write_request(
        &self,
        _id: Option<&jsonrpc::ID>,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), ipc::Error> {
        let payload = raw_json_bytes(params);
        self.write_tuple(MessageType::Call, method, &payload)
    }

    /// `WriteNotification` — msgpack protocol doesn't distinguish
    /// notifications from calls.
    fn write_notification(
        &self,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), ipc::Error> {
        self.write_request(None, method, params)
    }

    /// `WriteResponse` — `ResponsePayload::Binary` is `api.RawBinary`: the
    /// bytes become the payload verbatim instead of JSON text.
    fn write_response(
        &self,
        id: Option<&jsonrpc::ID>,
        result: Option<ResponsePayload>,
    ) -> Result<(), ipc::Error> {
        let method = id.map(|id| id.to_string()).unwrap_or_default();
        let payload = match result {
            Some(ResponsePayload::Binary(b)) => b,
            // `json.Marshal(nil)` → `"null"`.
            Some(ResponsePayload::Json(v)) => v.get().as_bytes().to_vec(),
            None => b"null".to_vec(),
        };
        self.write_tuple(MessageType::Response, &method, &payload)
    }

    /// `WriteError`
    fn write_error(
        &self,
        id: Option<&jsonrpc::ID>,
        resp_err: &jsonrpc::ResponseError,
    ) -> Result<(), ipc::Error> {
        let method = id.map(|id| id.to_string()).unwrap_or_default();
        self.write_tuple(MessageType::Error, &method, resp_err.message.as_bytes())
    }
}

/// `io.ReadFull` on one byte — `p.r.ReadByte`.
fn read_byte(r: &mut impl Read) -> Result<u8, ipc::Error> {
    let mut b = [0u8; 1];
    r.read_exact(&mut b)?;
    Ok(b[0])
}

/// `p.readBin`
fn read_bin(r: &mut impl Read) -> Result<Vec<u8>, ipc::Error> {
    let t = read_byte(r)?;
    let size: usize = match t {
        MSGPACK_BIN8 => read_byte(r)? as usize,
        MSGPACK_BIN16 => {
            let mut b = [0u8; 2];
            r.read_exact(&mut b)?;
            u16::from_be_bytes(b) as usize
        }
        MSGPACK_BIN32 => {
            let mut b = [0u8; 4];
            r.read_exact(&mut b)?;
            u32::from_be_bytes(b) as usize
        }
        _ => {
            return Err(invalid_request(format!(
                "expected binary data (0xc4-0xc6), received: 0x{t:02x}"
            )));
        }
    };
    let mut payload = vec![0u8; size];
    r.read_exact(&mut payload)?;
    Ok(payload)
}

/// `p.writeBin`
fn write_bin(w: &mut impl Write, data: &[u8]) -> io::Result<()> {
    let length = data.len();
    if length < 256 {
        w.write_all(&[MSGPACK_BIN8, length as u8])?;
    } else if length < (1 << 16) {
        w.write_all(&[MSGPACK_BIN16])?;
        w.write_all(&(length as u16).to_be_bytes())?;
    } else {
        w.write_all(&[MSGPACK_BIN32])?;
        w.write_all(&(length as u32).to_be_bytes())?;
    }
    w.write_all(data)
}

/// `json.Value(payload)` — the JSON-text bytes the client already placed in
/// the msgpack bin. `RawValue::from_string` validates the JSON here; Go's
/// `jsontext.Value` assignment doesn't, but a malformed payload would fail
/// the downstream `unmarshal_params` anyway.
fn raw_json(payload: &[u8]) -> Result<json::Value, ipc::Error> {
    let text = String::from_utf8(payload.to_vec())
        .map_err(|e| ipc::Error::Message(e.to_string()))?;
    Ok(serde_json::value::RawValue::from_string(text)?)
}

/// `json.Marshal(params)` — `params` is already raw JSON; `None` marshals
/// to `null` like a nil `any`.
fn raw_json_bytes(params: Option<json::Value>) -> Vec<u8> {
    match params {
        Some(v) => v.get().as_bytes().to_vec(),
        None => b"null".to_vec(),
    }
}
