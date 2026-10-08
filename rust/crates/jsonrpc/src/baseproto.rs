// Ported from tsc/internal/jsonrpc/baseproto.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Base protocol for JSON-RPC with Content-Length headers (as used by LSP).
// https://microsoft.github.io/language-server-protocol/specifications/base/0.9/specification/
//
// PORT: Go's sentinel errors (ErrInvalidHeader, ErrInvalidContentLength,
// ErrNoContentLength, io.EOF) become variants of `ReadError`; callers match
// variants or `ReadError::is_eof` instead of `errors.Is`. I/O failures keep
// `std::io::Error` wrapped in the matching variant.

use std::fmt;
use std::io;
use std::io::BufRead;
use std::io::Read as _;
use std::io::Write as _;

/// `var ( ErrInvalidHeader; ErrInvalidContentLength; ErrNoContentLength )`
/// plus the `io.EOF`/wrapped-io returns of `Reader.Read`.
#[derive(Debug)]
pub enum ReadError {
    /// `io.EOF` — the stream ended before or during a header line.
    Eof,
    /// `fmt.Errorf("jsonrpc: read header: %w", err)`
    ReadHeader(io::Error),
    /// `fmt.Errorf("%w: %q", ErrInvalidHeader, line)`
    InvalidHeader(Vec<u8>),
    /// `fmt.Errorf("%w: parse error: %w", ErrInvalidContentLength, err)` or
    /// `fmt.Errorf("%w: negative value %d", ErrInvalidContentLength, n)`;
    /// the payload is the message following the sentinel.
    InvalidContentLength(String),
    /// `ErrNoContentLength`
    NoContentLength,
    /// `fmt.Errorf("jsonrpc: read content: %w", err)`
    ReadContent(io::Error),
}

impl ReadError {
    /// `errors.Is(err, io.EOF)`.
    pub fn is_eof(&self) -> bool {
        matches!(self, ReadError::Eof)
    }
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReadError::Eof => write!(f, "EOF"),
            ReadError::ReadHeader(e) => write!(f, "jsonrpc: read header: {e}"),
            // PORT: Go prints `%q` of the raw line bytes; `{:?}` on the
            // lossy string is the closest std equivalent.
            ReadError::InvalidHeader(line) => write!(
                f,
                "jsonrpc: invalid header: {:?}",
                String::from_utf8_lossy(line)
            ),
            ReadError::InvalidContentLength(detail) => {
                write!(f, "jsonrpc: invalid content length: {detail}")
            }
            ReadError::NoContentLength => write!(f, "jsonrpc: no content length"),
            ReadError::ReadContent(e) => write!(f, "jsonrpc: read content: {e}"),
        }
    }
}

impl std::error::Error for ReadError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ReadError::ReadHeader(e) | ReadError::ReadContent(e) => Some(e),
            _ => None,
        }
    }
}

/// `type Reader struct` — reads JSON-RPC messages with Content-Length framing.
pub struct Reader<R: io::Read> {
    /// `r *bufio.Reader`
    r: io::BufReader<R>,
}

/// `func NewReader(r io.Reader) *Reader`
pub fn new_reader<R: io::Read>(r: R) -> Reader<R> {
    Reader {
        r: io::BufReader::new(r),
    }
}

impl<R: io::Read> Reader<R> {
    /// `func (r *Reader) Read() ([]byte, error)`
    pub fn read(&mut self) -> Result<Vec<u8>, ReadError> {
        let mut content_length: i64 = 0;

        loop {
            let mut line = Vec::new();
            // PORT: Go's `ReadBytes('\n')` returns `io.EOF` alongside partial
            // data when the stream ends without the delimiter; `read_until`
            // reports Ok(partial), so a returned line not ending in '\n' is
            // also EOF.
            match self.r.read_until(b'\n', &mut line) {
                Err(e) => return Err(ReadError::ReadHeader(e)),
                Ok(0) => return Err(ReadError::Eof),
                Ok(_) if !line.ends_with(b"\n") => return Err(ReadError::Eof),
                Ok(_) => {}
            }

            if line == b"\r\n" {
                break;
            }

            // `bytes.Cut(line, ":")` — split at the first ':'.
            let Some(colon) = line.iter().position(|&b| b == b':') else {
                return Err(ReadError::InvalidHeader(line));
            };
            let key = &line[..colon];
            let value = &line[colon + 1..];

            if key == b"Content-Length" {
                // PORT: `strconv.ParseInt(string(bytes.TrimSpace(value)), 10, 64)`.
                let text = std::str::from_utf8(value)
                    .map_err(|e| ReadError::InvalidContentLength(format!("parse error: {e}")))?;
                let parsed = text
                    .trim()
                    .parse::<i64>()
                    .map_err(|e| ReadError::InvalidContentLength(format!("parse error: {e}")))?;
                if parsed < 0 {
                    return Err(ReadError::InvalidContentLength(format!(
                        "negative value {parsed}"
                    )));
                }
                content_length = parsed;
            }
        }

        if content_length <= 0 {
            return Err(ReadError::NoContentLength);
        }

        let mut data = vec![0u8; content_length as usize];
        // `io.ReadFull(r.r, data)`
        self.r
            .read_exact(&mut data)
            .map_err(ReadError::ReadContent)?;

        Ok(data)
    }
}

/// `type Writer struct` — writes JSON-RPC messages with Content-Length framing.
pub struct Writer<W: io::Write> {
    /// `w *bufio.Writer`
    w: io::BufWriter<W>,
}

/// `func NewWriter(w io.Writer) *Writer`
pub fn new_writer<W: io::Write>(w: W) -> Writer<W> {
    Writer {
        w: io::BufWriter::new(w),
    }
}

impl<W: io::Write> Writer<W> {
    /// `func (w *Writer) Write(data []byte) error`
    pub fn write(&mut self, data: &[u8]) -> io::Result<()> {
        write!(self.w, "Content-Length: {}\r\n\r\n", data.len())?;
        self.w.write_all(data)?;
        self.w.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_framing() {
        let mut buf = Vec::new();
        new_writer(&mut buf).write(b"{}").unwrap();
        assert_eq!(buf, b"Content-Length: 2\r\n\r\n{}");
    }

    #[test]
    fn read_round_trip() {
        let mut buf = Vec::new();
        {
            let mut w = new_writer(&mut buf);
            w.write(b"{\"a\":1}").unwrap();
            w.write(b"[]").unwrap();
        }
        let mut r = new_reader(&buf[..]);
        assert_eq!(r.read().unwrap(), b"{\"a\":1}");
        assert_eq!(r.read().unwrap(), b"[]");
        assert!(r.read().unwrap_err().is_eof());
    }

    #[test]
    fn read_ignores_other_headers() {
        let input = b"Content-Type: application/json\r\nContent-Length: 1\r\n\r\nx";
        let mut r = new_reader(&input[..]);
        assert_eq!(r.read().unwrap(), b"x");
    }

    #[test]
    fn read_eof_mid_header() {
        // Partial header line without '\n' at EOF is io.EOF in Go, not an
        // invalid-header error.
        let input = b"Content-Length: 5";
        let mut r = new_reader(&input[..]);
        assert!(r.read().unwrap_err().is_eof());
        assert!(new_reader(&b""[..]).read().unwrap_err().is_eof());
    }

    #[test]
    fn read_invalid_header() {
        let input = b"garbage\r\n\r\n";
        let mut r = new_reader(&input[..]);
        match r.read() {
            Err(ReadError::InvalidHeader(line)) => assert_eq!(line, b"garbage\r\n"),
            other => panic!("expected InvalidHeader, got {other:?}"),
        }
        // A bare "\n" is not the CRLF terminator and has no ':' either.
        let input = b"Content-Length: 1\r\n\n";
        let mut r = new_reader(&input[..]);
        assert!(matches!(r.read(), Err(ReadError::InvalidHeader(_))));
    }

    #[test]
    fn read_invalid_content_length() {
        for input in [
            &b"Content-Length: abc\r\n\r\n"[..],
            &b"Content-Length: -3\r\n\r\n"[..],
        ] {
            let mut r = new_reader(input);
            assert!(matches!(r.read(), Err(ReadError::InvalidContentLength(_))));
        }
    }

    #[test]
    fn read_no_content_length() {
        for input in [
            &b"Content-Type: application/json\r\n\r\n"[..],
            &b"Content-Length: 0\r\n\r\n"[..],
        ] {
            let mut r = new_reader(input);
            assert!(matches!(r.read(), Err(ReadError::NoContentLength)));
        }
    }

    #[test]
    fn read_truncated_content() {
        let input = b"Content-Length: 10\r\n\r\n{}";
        let mut r = new_reader(&input[..]);
        assert!(matches!(r.read(), Err(ReadError::ReadContent(_))));
    }
}
