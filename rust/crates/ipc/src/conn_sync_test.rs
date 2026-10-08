// Ported from tsc/internal/ipc/conn_sync_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `io.EOF` from `ReadMessage` → `UnexpectedEof`; `errors.Is(err,
// responseErr)` → `err.is(&response_err)`; `t.Context()` →
// `Context::background()`. The panic-path test still writes the default
// panic-hook message to stderr (Go's `recover` suppresses it) — cosmetic.

use std::io;
use std::sync::{Arc, Mutex};

use tsc_core::context::Context;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::conn_async_test::NoOpHandler;
use crate::{Error, Handler, Message, Protocol, SyncConn};

/// `syncFailingResponseProtocol` — returns one message then `io.EOF`;
/// writes fail with `responseErr`.
struct SyncFailingResponseProtocol {
    message: Mutex<Option<Message>>,
    response_err: Option<Error>,
}

impl Protocol for SyncFailingResponseProtocol {
    fn read_message(&self) -> Result<Message, Error> {
        match self.message.lock().unwrap().take() {
            Some(m) => Ok(m),
            None => Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF").into()),
        }
    }

    fn write_request(
        &self,
        _id: Option<&jsonrpc::ID>,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn write_notification(&self, _method: &str, _params: Option<json::Value>) -> Result<(), Error> {
        Ok(())
    }

    fn write_response(
        &self,
        _id: Option<&jsonrpc::ID>,
        _result: Option<json::Value>,
    ) -> Result<(), Error> {
        match &self.response_err {
            Some(e) => Err(e.clone()),
            None => Ok(()),
        }
    }

    fn write_error(
        &self,
        _id: Option<&jsonrpc::ID>,
        _err: &jsonrpc::ResponseError,
    ) -> Result<(), Error> {
        match &self.response_err {
            Some(e) => Err(e.clone()),
            None => Ok(()),
        }
    }
}

/// `panicHandler`
struct PanicHandler;

impl Handler for PanicHandler {
    fn handle_request(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Box<dyn std::error::Error + Send + Sync>> {
        panic!("handler panic")
    }

    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

fn sync_protocol(response_err: &Error) -> SyncFailingResponseProtocol {
    SyncFailingResponseProtocol {
        message: Mutex::new(Some(Message {
            id: Some(jsonrpc::new_id_int(1)),
            method: "transform".to_string(),
            ..Default::default()
        })),
        response_err: Some(response_err.clone()),
    }
}

/// `TestSyncConnRunReturnsResponseWriteFailure`
#[test]
fn run_returns_response_write_failure() {
    let response_err = Error::Message("response write failed".to_string());
    let protocol = sync_protocol(&response_err);
    let conn = SyncConn::new_sync_conn(None, Arc::new(protocol), Arc::new(NoOpHandler));

    let err = conn.run(&Context::background()).unwrap_err();
    assert!(
        err.is(&response_err),
        "expected response write error, got {err}"
    );
}

/// `TestSyncConnRunReturnsPanicResponseWriteFailure`
#[test]
fn run_returns_panic_response_write_failure() {
    let response_err = Error::Message("response write failed".to_string());
    let protocol = sync_protocol(&response_err);
    let conn = SyncConn::new_sync_conn(None, Arc::new(protocol), Arc::new(PanicHandler));

    let err = conn.run(&Context::background()).unwrap_err();
    assert!(
        err.is(&response_err),
        "expected panic response write error, got {err}"
    );
    assert!(
        err.to_string().contains("original panic: handler panic"),
        "got {err}"
    );
}
