// Ported from tsc/internal/ipc/conn.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go `error` returns become the `Error` enum. The `ErrConnClosed` /
//   `ErrRequestTimeout` sentinels are unit variants; `fmt.Errorf("...: %w")`
//   becomes `Wrapped` and `errors.Join` becomes `Joined`, so `Error::is`
//   reproduces `errors.Is` chain walking (see `is`/`leaf_eq`).
// - `context.Context` → `tsc_core::Context`; `ctx.Err()` →
//   `Error::ContextCanceled` (the ported `Context` has no deadline support,
//   so `DeadlineExceeded` cannot occur).
// - `params any` / `result any` → `Option<json::Value>` (raw JSON). `None`
//   is the nil interface: omitted for params, `"null"` for results.
// - `HandleRequest`'s `error` result → `Box<dyn std::error::Error>`; only its
//   message is used, matching `err.Error()` in the response payload.
// - `io.Closer` → `IoClose` (`&self`, because the async conn may close the
//   transport from a handler thread while the read loop is blocked on it).
// - `Error` is `Clone` (leaves are `Arc`-wrapped) because the Go code stores
//   the terminal error *and* returns it / sends it on a channel — `interface`
//   values share freely, enum values do not.

use std::fmt;
use std::io;
use std::sync::Arc;

use serde::Serialize;
use tsc_core::context::Context;
use tsc_json as json;
use tsc_jsonrpc::ReadError;

use crate::ResponsePayload;

/// `var ( ErrConnClosed; ErrRequestTimeout )` plus every error shape this
/// package produces. The Go sentinels are unit variants:
/// `ErrConnClosed` → [`Error::ConnClosed`], `ErrRequestTimeout` →
/// [`Error::RequestTimeout`].
#[derive(Clone, Debug)]
pub enum Error {
    /// `ErrConnClosed` — "ipc: connection closed".
    ConnClosed,
    /// `ErrRequestTimeout` — "ipc: request timeout".
    RequestTimeout,
    /// `ctx.Err()` — `context.Canceled`. The `Context` port has no deadline,
    /// so `context.DeadlineExceeded` has no equivalent.
    ContextCanceled,
    /// `fmt.Errorf("ipc: remote error [%d]: %s", code, message)` — an error
    /// response returned by the peer.
    Remote {
        /// `resp.Error.Code`
        code: i32,
        /// `resp.Error.Message`
        message: String,
    },
    /// A `jsonrpc` base-protocol read failure (`ReadError`, including its
    /// `io.EOF` equivalent `ReadError::Eof`).
    Read(Arc<ReadError>),
    /// A `json.Marshal`/`Unmarshal` failure.
    Json(Arc<serde_json::Error>),
    /// An `io` failure (transport reads/writes, custom `Protocol` impls).
    Io(Arc<io::Error>),
    /// `errors.New` / `fmt.Errorf` without `%w` — a plain message.
    Message(String),
    /// `fmt.Errorf("...%w...", err)` — `msg` is the fully rendered message
    /// (matching Go's `Error()` output); `source` is the wrapped error.
    Wrapped {
        /// The rendered `fmt.Errorf` message.
        msg: String,
        /// The `%w` operand.
        source: Box<Error>,
    },
    /// `errors.Join(a, b)` — Display renders each operand on its own line,
    /// as Go's `joinError.Error()` does.
    Joined(Box<Error>, Box<Error>),
}

impl Error {
    /// `fmt.Errorf(msg_with_%w, source)` — `msg` must already contain the
    /// rendered source text where `%w` appeared.
    pub(crate) fn wrapped(msg: impl Into<String>, source: Error) -> Error {
        Error::Wrapped {
            msg: msg.into(),
            source: Box::new(source),
        }
    }

    /// `errors.Is(err, target)`. Go compares the error value itself (pointer
    /// identity for sentinels) then walks `Unwrap`; here leaf variants compare
    /// by value and `Wrapped`/`Joined` recurse into their source chain.
    pub fn is(&self, target: &Error) -> bool {
        match self {
            // `errors.Join` — Is checks each operand.
            Error::Joined(a, b) => a.is(target) || b.is(target),
            // `fmt.wrapError` — never equal to the target itself; unwrap.
            Error::Wrapped { source, .. } => source.is(target),
            _ => self.leaf_eq(target),
        }
    }

    /// Value equality for non-wrapping variants — the `err == target` half of
    /// `errors.Is`.
    fn leaf_eq(&self, target: &Error) -> bool {
        match (self, target) {
            (Error::ConnClosed, Error::ConnClosed)
            | (Error::RequestTimeout, Error::RequestTimeout)
            | (Error::ContextCanceled, Error::ContextCanceled) => true,
            (
                Error::Remote {
                    code: c1,
                    message: m1,
                },
                Error::Remote {
                    code: c2,
                    message: m2,
                },
            ) => c1 == c2 && m1 == m2,
            (Error::Message(a), Error::Message(b)) => a == b,
            (Error::Io(a), Error::Io(b)) => a.kind() == b.kind() && a.to_string() == b.to_string(),
            (Error::Json(a), Error::Json(b)) => a.to_string() == b.to_string(),
            (Error::Read(a), Error::Read(b)) => a.to_string() == b.to_string(),
            _ => false,
        }
    }

    /// `errors.Is(err, io.EOF)` — the read loop treats EOF as a clean close.
    pub fn is_eof(&self) -> bool {
        match self {
            Error::Read(e) => e.is_eof(),
            Error::Io(e) => e.kind() == io::ErrorKind::UnexpectedEof,
            _ => false,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ConnClosed => f.write_str("ipc: connection closed"),
            Error::RequestTimeout => f.write_str("ipc: request timeout"),
            Error::ContextCanceled => f.write_str("context canceled"),
            Error::Remote { code, message } => {
                write!(f, "ipc: remote error [{code}]: {message}")
            }
            Error::Read(e) => e.fmt(f),
            Error::Json(e) => e.fmt(f),
            Error::Io(e) => e.fmt(f),
            Error::Message(m) => f.write_str(m),
            Error::Wrapped { msg, .. } => f.write_str(msg),
            // Go `joinError.Error()` joins operands with '\n'.
            Error::Joined(a, b) => write!(f, "{a}\n{b}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Wrapped { source, .. } => Some(source),
            Error::Read(e) => Some(e),
            Error::Json(e) => Some(e),
            Error::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::Io(Arc::new(e))
    }
}

impl From<ReadError> for Error {
    fn from(e: ReadError) -> Error {
        Error::Read(Arc::new(e))
    }
}

impl From<serde_json::Error> for Error {
    fn from(e: serde_json::Error) -> Error {
        Error::Json(Arc::new(e))
    }
}

/// `io.Closer` — `Close() error`.
pub trait IoClose: Send + Sync {
    /// `Close() error`
    fn close(&self) -> io::Result<()>;
}

/// `type Handler interface` — processes incoming API requests and
/// notifications.
pub trait Handler: Send + Sync {
    /// `HandleRequest(ctx, method, params) (any, error)` — `None` produces a
    /// `null` result like a nil `any`; `ResponsePayload::Binary` is the
    /// `api.RawBinary` case.
    fn handle_request(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<Option<ResponsePayload>, Box<dyn std::error::Error + Send + Sync>>;

    /// `HandleNotification(ctx, method, params) error` — the return value is
    /// discarded by the connection, as in Go.
    fn handle_notification(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
}

/// `type Conn interface` — a bidirectional connection for API communication.
pub trait Conn: Send + Sync {
    /// `Run(ctx) error` — processes messages until the context is cancelled
    /// or an error occurs.
    fn run(&self, ctx: &Context) -> Result<(), Error>;

    /// `Call(ctx, method, params) (json.Value, error)` — sends a request and
    /// waits for a response. `params` is raw JSON (`None` omits the member,
    /// like a nil `any`); the return is the raw `result` member (`None` when
    /// the response carried none).
    fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Error>;

    /// `Notify(ctx, method, params) error` — sends a notification (no
    /// response expected).
    fn notify(&self, ctx: &Context, method: &str, params: Option<json::Value>)
    -> Result<(), Error>;
}

/// Marshals `params` into a raw `json::Value` for [`Conn::call`] /
/// [`Conn::notify`] — the `params any` half of those Go signatures.
///
/// PORT: `serde_json::value::to_raw_value` produces the same compact JSON
/// `json.Marshal` would splice into the request.
pub fn marshal_params<T: Serialize + ?Sized>(params: &T) -> Result<json::Value, Error> {
    Ok(serde_json::value::to_raw_value(params)?)
}

/// `func UnmarshalParams[T any](params json.Value) (*T, error)` — `None`
/// (absent params) becomes `Ok(None)`, like Go's nil pointer return.
pub fn unmarshal_params<T: serde::de::DeserializeOwned>(
    params: Option<&json::Value>,
) -> Result<Option<T>, Error> {
    let Some(p) = params else {
        return Ok(None);
    };
    // Go: `len(params) == 0` — an empty jsontext.Value yields a nil *T.
    if p.get().is_empty() {
        return Ok(None);
    }
    Ok(Some(json::unmarshal(p.get().as_bytes(), &[])?))
}
