// Ported from tsc/internal/lsp/lsproto/baseproto.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;

// https://microsoft.github.io/language-server-protocol/specifications/base/0.9/specification/

/// `type BaseReader struct { *jsonrpc.Reader }` — wraps jsonrpc.Reader for
/// backwards compatibility.
pub struct BaseReader<R: io::Read> {
    reader: tsc_jsonrpc::Reader<R>,
}

/// `func NewBaseReader(r io.Reader) *BaseReader`
pub fn new_base_reader<R: io::Read>(r: R) -> BaseReader<R> {
    BaseReader {
        reader: tsc_jsonrpc::new_reader(r),
    }
}

impl<R: io::Read> BaseReader<R> {
    /// `func (r *Reader) Read() ([]byte, error)`
    pub fn read(&mut self) -> Result<Vec<u8>, tsc_jsonrpc::ReadError> {
        self.reader.read()
    }
}

impl<R: io::Read> std::ops::Deref for BaseReader<R> {
    type Target = tsc_jsonrpc::Reader<R>;
    fn deref(&self) -> &Self::Target {
        &self.reader
    }
}

/// `type BaseWriter struct { *jsonrpc.Writer }`
pub struct BaseWriter<W: io::Write> {
    writer: tsc_jsonrpc::Writer<W>,
}

/// `func NewBaseWriter(w io.Writer) *BaseWriter`
pub fn new_base_writer<W: io::Write>(w: W) -> BaseWriter<W> {
    BaseWriter {
        writer: tsc_jsonrpc::new_writer(w),
    }
}

impl<W: io::Write> BaseWriter<W> {
    /// `func (w *Writer) Write(data []byte) error`
    pub fn write(&mut self, data: &[u8]) -> io::Result<()> {
        self.writer.write(data)
    }
}

impl<W: io::Write> std::ops::Deref for BaseWriter<W> {
    type Target = tsc_jsonrpc::Writer<W>;
    fn deref(&self) -> &Self::Target {
        &self.writer
    }
}
