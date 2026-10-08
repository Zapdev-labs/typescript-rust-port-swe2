// Ported from tsc/internal/lsp/lsproto/baseproto_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;

use crate::*;

#[test]
fn test_base_reader() {
    struct Case {
        name: &'static str,
        input: &'static [u8],
        value: Option<&'static [u8]>,
        err: &'static str,
    }
    let tests = [
        Case {
            name: "empty",
            input: b"Content-Length: 0\r\n\r\n",
            value: None,
            err: "jsonrpc: no content length",
        },
        Case {
            name: "early end",
            input: b"oops",
            value: None,
            err: "EOF",
        },
        Case {
            name: "negative length",
            input: b"Content-Length: -1\r\n\r\n",
            value: None,
            err: "jsonrpc: invalid content length: negative value -1",
        },
        Case {
            name: "invalid content",
            input: b"Content-Length: 1\r\n\r\n{",
            value: Some(b"{"),
            err: "",
        },
        Case {
            name: "valid content",
            input: b"Content-Length: 2\r\n\r\n{}",
            value: Some(b"{}"),
            err: "",
        },
        Case {
            name: "extra header values",
            input: b"Content-Length: 2\r\nExtra: 1\r\n\r\n{}",
            value: Some(b"{}"),
            err: "",
        },
        Case {
            name: "too long content length",
            input: b"Content-Length: 100\r\n\r\n{}",
            value: None,
            // Go: "jsonrpc: read content: unexpected EOF"; io::Error renders
            // "failed to fill whole buffer", so these are prefix-matched.
            err: "jsonrpc: read content",
        },
        Case {
            name: "missing content length",
            input: b"Content-Length: \r\n\r\n{}",
            value: None,
            err: "jsonrpc: invalid content length: parse error",
        },
        Case {
            name: "invalid header",
            input: b"Nope\r\n\r\n{}",
            value: None,
            err: "jsonrpc: invalid header",
        },
    ];

    for tt in tests {
        let mut r = new_base_reader(tt.input);
        let out = r.read();
        if !tt.err.is_empty() {
            let err = out.unwrap_err();
            assert!(
                err.to_string().starts_with(tt.err),
                "case {:?}: wrong error {:?}, expected prefix {:?}",
                tt.name,
                err.to_string(),
                tt.err,
            );
            continue;
        }
        let out = out.unwrap_or_else(|e| panic!("case {:?}: {}", tt.name, e));
        assert_eq!(out, tt.value.unwrap(), "case {:?}", tt.name);
    }
}

#[test]
fn test_base_reader_multiple_reads() {
    let data = b"Content-Length: 4\r\n\r\n1234Content-Length: 2\r\n\r\n{}";
    let mut r = new_base_reader(&data[..]);

    let v1 = r.read().unwrap();
    assert_eq!(v1, b"1234");

    let v2 = r.read().unwrap();
    assert_eq!(v2, b"{}");

    let err = r.read().unwrap_err();
    assert!(err.is_eof());
}

struct ErrorWriter;

impl io::Write for ErrorWriter {
    fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
        Err(io::Error::other("test error"))
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn test_base_writer() {
    let tests = [
        (b"{}" as &[u8], b"Content-Length: 2\r\n\r\n{}" as &[u8]),
        (
            b"{\"key\":\"value\"}",
            b"Content-Length: 15\r\n\r\n{\"key\":\"value\"}",
        ),
    ];

    for (value, input) in tests {
        let mut b = Vec::new();
        let mut w = new_base_writer(&mut b);
        w.write(value).unwrap();
        drop(w);
        assert_eq!(b, input);
    }
}

#[test]
fn test_base_writer_write_error() {
    let mut w = new_base_writer(ErrorWriter);
    let err = w.write(b"{}").unwrap_err();
    assert_eq!(err.to_string(), "test error");
}
