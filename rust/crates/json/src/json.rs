// Ported from tsc/internal/json/json.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
//nolint:depguard
//
// PORT: the Go file is a facade over encoding/json/v2 + encoding/json/jsontext;
// this port is a facade over serde_json. Semantic deltas vs jsontext:
//   - The Go facade always applies jsontext.AllowInvalidUTF8(true). Rust
//     strings are always valid UTF-8, so the flag is a resolved no-op; a
//     jsontext.Value carrying invalid UTF-8 cannot round-trip through
//     serde_json::value::RawValue (it is a &str internally).
//   - jsontext rejects duplicate object member names unless
//     AllowDuplicateNames(true); serde_json accepts duplicates (last wins for
//     map-like targets). allow_duplicate_names(false) is a documented no-op —
//     serde_json offers no duplicate-name rejection for derived impls.
//   - jsontext writes float64 per ECMAScript Number::toString (integral
//     floats print as "1", magnitudes >= 1e21 print as "1e+21"); serde_json's
//     ryu prints "1.0" and "1e21". A marshal_f64/marshal_number helper should
//     be added if a ported caller needs byte parity for bare floats.
//   - jsontext.Deterministic(true) sorts map keys; serde_json serializes a
//     map in its own iteration order. deterministic(true) routes through
//     serde_json::Value, which sorts keys under serde_json's default BTreeMap
//     (diverges only if the serde_json "preserve_order" feature is enabled).
//   - Errors are serde_json::Error, not *jsontext errors; io errors are
//     wrapped via serde_json::Error::io.
//   - Encoder/Decoder implement jsontext's streaming token model (auto ','
//     and ':' separators, member-name tracking) but do not replicate its
//     strict grammar validation — callers are trusted, matching how the Go
//     callers use it.

use std::borrow::Cow;
use std::io;
use std::io::BufRead;

use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;

/// `[]json.Options` — the Go facade always prepends AllowInvalidUTF8(true);
/// that is folded into `resolve_options` instead of a stored slice.
#[derive(Clone, Default)]
pub struct Options {
    allow_invalid_utf8: Option<bool>,
    allow_duplicate_names: Option<bool>,
    deterministic: Option<bool>,
    indent: Option<String>,
    indent_prefix: Option<String>,
}

#[derive(Clone, Default)]
struct ResolvedOptions {
    allow_invalid_utf8: bool,
    #[allow(dead_code)]
    allow_duplicate_names: bool,
    deterministic: bool,
    indent: Option<String>,
    indent_prefix: Option<String>,
}

impl ResolvedOptions {
    fn apply(&mut self, o: &Options) {
        if let Some(v) = o.allow_invalid_utf8 {
            self.allow_invalid_utf8 = v;
        }
        if let Some(v) = o.allow_duplicate_names {
            self.allow_duplicate_names = v;
        }
        if let Some(v) = o.deterministic {
            self.deterministic = v;
        }
        if let Some(v) = &o.indent {
            self.indent = Some(v.clone());
        }
        if let Some(v) = &o.indent_prefix {
            self.indent_prefix = Some(v.clone());
        }
    }

    fn merged_with(&self, opts: &[Options]) -> ResolvedOptions {
        let mut resolved = self.clone();
        for o in opts {
            resolved.apply(o);
        }
        resolved
    }
}

fn resolve_options(opts: &[Options]) -> ResolvedOptions {
    // PORT: `slices.Clip([]json.Options{jsontext.AllowInvalidUTF8(true)})`
    // prepended to every call.
    let mut resolved = ResolvedOptions {
        allow_invalid_utf8: true,
        ..Default::default()
    };
    for o in opts {
        resolved.apply(o);
    }
    resolved
}

/// Serializes a value honoring indent/deterministic. The indent_prefix is
/// *not* applied here — see `apply_prefix` (jsontext writes the prefix after
/// every newline; a post-pass is byte-identical because raw '\n' bytes can
/// only appear between tokens, never inside strings).
fn marshal_impl<T: ?Sized + Serialize>(
    in_: &T,
    o: &ResolvedOptions,
) -> Result<Vec<u8>, serde_json::Error> {
    let mut buf = Vec::new();
    match &o.indent {
        Some(indent) => {
            let formatter = serde_json::ser::PrettyFormatter::with_indent(indent.as_bytes());
            let mut ser = serde_json::Serializer::with_formatter(&mut buf, formatter);
            if o.deterministic {
                serde_json::to_value(in_)?.serialize(&mut ser)?;
            } else {
                in_.serialize(&mut ser)?;
            }
        }
        None => {
            let mut ser = serde_json::Serializer::new(&mut buf);
            if o.deterministic {
                serde_json::to_value(in_)?.serialize(&mut ser)?;
            } else {
                in_.serialize(&mut ser)?;
            }
        }
    }
    apply_prefix(&mut buf, o);
    Ok(buf)
}

/// jsontext.WithIndentPrefix inserts `prefix` after every newline inside the
/// encoded value; equivalent to a post-pass over the finished output.
fn apply_prefix(buf: &mut Vec<u8>, o: &ResolvedOptions) {
    let Some(prefix) = &o.indent_prefix else {
        return;
    };
    if prefix.is_empty() {
        return;
    }
    let mut out = Vec::with_capacity(buf.len() + prefix.len() * 8);
    for &b in buf.iter() {
        out.push(b);
        if b == b'\n' {
            out.extend_from_slice(prefix.as_bytes());
        }
    }
    *buf = out;
}

/// `func Marshal(in any, opts ...json.Options) (out []byte, err error)`
pub fn marshal<T: ?Sized + Serialize>(
    in_: &T,
    opts: &[Options],
) -> Result<Vec<u8>, serde_json::Error> {
    marshal_impl(in_, &resolve_options(opts))
}

/// `func MarshalEncode(out *jsontext.Encoder, in any, opts ...json.Options) (err error)`
pub fn marshal_encode<W: io::Write, T: ?Sized + Serialize>(
    out: &mut Encoder<W>,
    in_: &T,
    opts: &[Options],
) -> Result<(), serde_json::Error> {
    // PORT: a nested value is encoded standalone, then depth-shifted into the
    // encoder's indent context by `write_blob` — jsontext encodes directly at
    // the current depth; the byte output is identical.
    let resolved = out.resolved.merged_with(opts);
    // write_blob inserts prefix + indent*depth after each newline; serialize
    // the blob without the prefix so it isn't doubled.
    let blob_resolved = ResolvedOptions {
        indent_prefix: None,
        ..resolved
    };
    let bytes = marshal_impl(in_, &blob_resolved)?;
    out.before_element()?;
    out.write_blob(&bytes)
}

/// `func MarshalWrite(out io.Writer, in any, opts ...json.Options) (err error)`
pub fn marshal_write<W: io::Write, T: ?Sized + Serialize>(
    mut out: W,
    in_: &T,
    opts: &[Options],
) -> Result<(), serde_json::Error> {
    // PORT: Go streams into `out`; we buffer via marshal — same bytes.
    out.write_all(&marshal(in_, opts)?)
        .map_err(serde_json::Error::io)
}

/// `func MarshalIndent(in any, prefix, indent string) (out []byte, err error)`
pub fn marshal_indent<T: ?Sized + Serialize>(
    in_: &T,
    prefix: &str,
    indent: &str,
) -> Result<Vec<u8>, serde_json::Error> {
    if prefix.is_empty() && indent.is_empty() {
        // WithIndentPrefix and WithIndent imply multiline output, so skip them.
        return marshal(in_, &[]);
    }
    marshal(in_, &[with_indent_prefix(prefix), with_indent(indent)])
}

/// `func MarshalIndentWrite(out io.Writer, in any, prefix, indent string) (err error)`
pub fn marshal_indent_write<W: io::Write, T: ?Sized + Serialize>(
    out: W,
    in_: &T,
    prefix: &str,
    indent: &str,
) -> Result<(), serde_json::Error> {
    if prefix.is_empty() && indent.is_empty() {
        // WithIndentPrefix and WithIndent imply multiline output, so skip them.
        return marshal_write(out, in_, &[]);
    }
    marshal_write(out, in_, &[with_indent_prefix(prefix), with_indent(indent)])
}

/// `func Unmarshal(in []byte, out any, opts ...json.Options) (err error)`
///
/// PORT: returns the value rather than writing through an `any` pointer.
pub fn unmarshal<T: serde::de::DeserializeOwned>(
    in_: &[u8],
    opts: &[Options],
) -> Result<T, serde_json::Error> {
    let _ = resolve_options(opts); // options are parse-side no-ops (see header)
    serde_json::from_slice(in_)
}

/// `func UnmarshalDecode(in *jsontext.Decoder, out any, opts ...json.Options) (err error)`
pub fn unmarshal_decode<R: io::Read, T: serde::de::DeserializeOwned>(
    in_: &mut Decoder<R>,
    opts: &[Options],
) -> Result<T, serde_json::Error> {
    let _ = resolve_options(opts);
    let value = in_.read_value()?;
    serde_json::from_str(value.get())
}

/// `func UnmarshalRead(in io.Reader, out any, opts ...json.Options) (err error)`
pub fn unmarshal_read<R: io::Read, T: serde::de::DeserializeOwned>(
    in_: R,
    opts: &[Options],
) -> Result<T, serde_json::Error> {
    let _ = resolve_options(opts);
    // PORT: jsontext errors on trailing data after the top-level value;
    // serde_json::from_reader ignores trailing bytes.
    serde_json::from_reader(in_)
}

/// `func AllowDuplicateNames(allow bool) json.Options` —
/// `jsontext.AllowDuplicateNames`.
pub fn allow_duplicate_names(allow: bool) -> Options {
    Options {
        allow_duplicate_names: Some(allow),
        ..Default::default()
    }
}

/// `func Deterministic(v bool) json.Options` — `json.Deterministic`.
pub fn deterministic(v: bool) -> Options {
    Options {
        deterministic: Some(v),
        ..Default::default()
    }
}

/// `func WithIndent(indent string) json.Options` — `jsontext.WithIndent`.
pub fn with_indent(indent: &str) -> Options {
    Options {
        indent: Some(indent.to_string()),
        ..Default::default()
    }
}

/// `jsontext.WithIndentPrefix` — used by MarshalIndent/MarshalIndentWrite;
/// not part of the Go facade's exported surface.
pub(crate) fn with_indent_prefix(prefix: &str) -> Options {
    Options {
        indent_prefix: Some(prefix.to_string()),
        ..Default::default()
    }
}

/// `func NewDecoder(r io.Reader) *jsontext.Decoder`
pub fn new_decoder<R: io::Read>(r: R) -> Decoder<R> {
    Decoder::new(r)
}

/// `type Value = jsontext.Value` — a raw, uninterpreted JSON buffer.
/// PORT: serde_json::value::RawValue is the serde equivalent. Construct with
/// `serde_json::value::RawValue::from_string`.
pub type Value = Box<RawValue>;

/// `type Kind = jsontext.Kind` — the leading byte of a JSON token's grammar,
/// with numbers normalized to '0'.
pub type Kind = u8;

/// Kind normalization (jsontext's normKind table): number-starting bytes map
/// to '0'; punctuation/literal kinds pass through.
fn normalize_kind(b: u8) -> Kind {
    match b {
        b'-' | b'0'..=b'9' => b'0',
        b => b,
    }
}

/// jsontext reports stream exhaustion as `io.EOF`; an io error is the closest
/// serde_json-error channel.
fn unexpected_eof() -> serde_json::Error {
    serde_json::Error::io(io::Error::new(
        io::ErrorKind::UnexpectedEof,
        "unexpected EOF",
    ))
}

/// `type Token = jsontext.Token` — a JSON token: structural punctuation, a
/// literal (`null`/`true`/`false`), a string, or a number. `raw` holds the
/// token's JSON bytes.
#[derive(Clone, Debug)]
pub struct Token {
    kind: Kind,
    raw: Cow<'static, [u8]>,
}

impl Token {
    /// `func (t Token) Kind() Kind`
    pub fn kind(&self) -> Kind {
        self.kind
    }

    /// The token's raw JSON bytes (jsontext stores the same internally).
    pub fn bytes(&self) -> &[u8] {
        &self.raw
    }

    /// `jsontext.String(s)` — a string token.
    pub fn string(s: &str) -> Token {
        Token {
            kind: b'"',
            raw: Cow::Owned(serde_json::to_string(s).unwrap_or_default().into_bytes()),
        }
    }

    /// `jsontext.Bool(v)` — a bool token.
    pub fn bool(v: bool) -> Token {
        Token {
            kind: if v { b't' } else { b'f' },
            raw: Cow::Borrowed(if v { b"true" } else { b"false" }),
        }
    }

    /// `jsontext.Int(n)` — a number token.
    pub fn int(n: i64) -> Token {
        Token {
            kind: b'0',
            raw: Cow::Owned(n.to_string().into_bytes()),
        }
    }

    /// `jsontext.Uint(n)` — a number token.
    pub fn uint(n: u64) -> Token {
        Token {
            kind: b'0',
            raw: Cow::Owned(n.to_string().into_bytes()),
        }
    }

    /// `jsontext.Float(n)` — a number token.
    /// PORT: serde_json's f64 formatting differs from jsontext's ECMAScript
    /// formatting for integral floats and exponent style — see header.
    pub fn float(n: f64) -> Token {
        Token {
            kind: b'0',
            raw: Cow::Owned(serde_json::to_string(&n).unwrap_or_default().into_bytes()),
        }
    }
}

// `var ( BeginObject = jsontext.BeginObject; ... )` — Token constants.
pub const BEGIN_OBJECT: Token = Token {
    kind: b'{',
    raw: Cow::Borrowed(b"{"),
};
pub const END_OBJECT: Token = Token {
    kind: b'}',
    raw: Cow::Borrowed(b"}"),
};
pub const NULL: Token = Token {
    kind: b'n',
    raw: Cow::Borrowed(b"null"),
};
pub const BEGIN_ARRAY: Token = Token {
    kind: b'[',
    raw: Cow::Borrowed(b"["),
};
pub const END_ARRAY: Token = Token {
    kind: b']',
    raw: Cow::Borrowed(b"]"),
};

/// `type MarshalerTo = json.MarshalerTo` — a type with a `MarshalJSONTo`
/// method writing itself through a token `Encoder`.
/// PORT: Go has the encoding side hook this directly; here a type porting a
/// `MarshalJSONTo` impl implements `serde::Serialize` by buffering through an
/// `Encoder` and re-emitting as `RawValue` — use `serialize_marshaler_to`.
pub trait MarshalerTo {
    fn marshal_json_to<W: io::Write>(&self, enc: &mut Encoder<W>) -> Result<(), serde_json::Error>;
}

/// Helper for `impl serde::Serialize` on a `MarshalerTo` port:
/// `serialize_marshaler_to(self, serializer)`.
pub fn serialize_marshaler_to<T: MarshalerTo + ?Sized, S: serde::Serializer>(
    value: &T,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut buf = Vec::new();
    let mut enc = Encoder::new(&mut buf);
    value
        .marshal_json_to(&mut enc)
        .map_err(serde::ser::Error::custom)?;
    let raw = RawValue::from_string(String::from_utf8(buf).map_err(serde::ser::Error::custom)?)
        .map_err(serde::ser::Error::custom)?;
    raw.serialize(serializer)
}

/// `type UnmarshalerFrom = json.UnmarshalerFrom` — a type with an
/// `UnmarshalJSONFrom` method reading itself from a token `Decoder`.
/// PORT: Go calls this on a pre-existing receiver; ports need
/// `Default`-constructible receivers — use `deserialize_unmarshaler_from`.
pub trait UnmarshalerFrom {
    fn unmarshal_json_from<R: io::Read>(
        &mut self,
        dec: &mut Decoder<R>,
    ) -> Result<(), serde_json::Error>;
}

/// Helper for `impl serde::Deserialize` on an `UnmarshalerFrom` port:
/// `deserialize_unmarshaler_from(deserializer)` with `T: Default`.
pub fn deserialize_unmarshaler_from<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: serde::Deserializer<'de>,
    T: UnmarshalerFrom + Default,
{
    let raw = <&RawValue>::deserialize(deserializer)?;
    let mut dec = Decoder::new(raw.get().as_bytes());
    let mut value = T::default();
    value
        .unmarshal_json_from(&mut dec)
        .map_err(serde::de::Error::custom)?;
    Ok(value)
}

/// One open container's decode/encode state — jsontext tracks this to insert
/// or skip `,`/`:` separators automatically.
struct Frame {
    is_object: bool,
    /// Elements written/read so far (an object member counts once, at its value).
    count: usize,
    /// Object only: the next element position is a member name, not a value.
    expect_name: bool,
}

/// `type Decoder = jsontext.Decoder` — a streaming token reader over one or
/// more consecutive JSON values.
pub struct Decoder<R: io::Read> {
    r: io::BufReader<R>,
    stack: Vec<Frame>,
    /// Kind computed by `preamble` and cached between `peek_kind` and the
    /// following `read_token`/`read_value`.
    pending: Option<Kind>,
}

impl<R: io::Read> Decoder<R> {
    fn new(r: R) -> Decoder<R> {
        Decoder {
            r: io::BufReader::new(r),
            stack: Vec::new(),
            pending: None,
        }
    }

    fn peek_byte(&mut self) -> io::Result<Option<u8>> {
        Ok(self.r.fill_buf()?.first().copied())
    }

    fn consume_byte(&mut self) {
        self.r.consume(1);
    }

    fn skip_whitespace(&mut self) -> io::Result<()> {
        while let Some(b) = self.peek_byte()? {
            if !matches!(b, b' ' | b'\t' | b'\n' | b'\r') {
                break;
            }
            self.consume_byte();
        }
        Ok(())
    }

    /// Consumes `,`/`:` separators implied by the container stack, updates
    /// element bookkeeping, and returns the kind of the next token without
    /// consuming it — mirrors the state tracking jsontext performs before
    /// every token read. The result is cached so `peek_kind` is idempotent.
    fn preamble(&mut self) -> Result<Kind, serde_json::Error> {
        if let Some(kind) = self.pending {
            return Ok(kind);
        }
        self.skip_whitespace().map_err(serde_json::Error::io)?;
        // Snapshot the frame state; `expect_byte`/`skip_whitespace` need
        // `&mut self`, so the frame is updated after them.
        if let Some(&(is_object, expect_name, count)) = self
            .stack
            .last()
            .map(|f| (f.is_object, f.expect_name, f.count))
            .as_ref()
        {
            if is_object {
                if expect_name {
                    // A member name position that starts with '}' is the
                    // end-of-object token, not a name.
                    match self.peek_byte().map_err(serde_json::Error::io)? {
                        Some(b'}') => {}
                        Some(_) => {
                            if count > 0 {
                                self.expect_byte(b',')?;
                            }
                            self.skip_whitespace().map_err(serde_json::Error::io)?;
                            if let Some(frame) = self.stack.last_mut() {
                                frame.expect_name = false;
                            }
                        }
                        None => return Err(unexpected_eof()),
                    }
                } else {
                    self.expect_byte(b':')?;
                    self.skip_whitespace().map_err(serde_json::Error::io)?;
                    if let Some(frame) = self.stack.last_mut() {
                        frame.expect_name = true;
                        frame.count += 1;
                    }
                }
            } else {
                match self.peek_byte().map_err(serde_json::Error::io)? {
                    Some(b']') => {}
                    Some(_) => {
                        if count > 0 {
                            self.expect_byte(b',')?;
                        }
                        self.skip_whitespace().map_err(serde_json::Error::io)?;
                        if let Some(frame) = self.stack.last_mut() {
                            frame.count += 1;
                        }
                    }
                    None => return Err(unexpected_eof()),
                }
            }
        }
        let Some(b) = self.peek_byte().map_err(serde_json::Error::io)? else {
            return Err(unexpected_eof());
        };
        let kind = normalize_kind(b);
        self.pending = Some(kind);
        Ok(kind)
    }

    fn expect_byte(&mut self, want: u8) -> Result<(), serde_json::Error> {
        self.skip_whitespace().map_err(serde_json::Error::io)?;
        match self.peek_byte().map_err(serde_json::Error::io)? {
            Some(b) if b == want => {
                self.consume_byte();
                Ok(())
            }
            Some(b) => Err(serde_json::Error::io(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("expected '{}' but found '{}'", want as char, b as char),
            ))),
            None => Err(serde_json::Error::io(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "unexpected EOF",
            ))),
        }
    }

    /// `func (d *Decoder) PeekKind() Kind` — the kind of the next token.
    pub fn peek_kind(&mut self) -> Result<Kind, serde_json::Error> {
        self.preamble()
    }

    /// `func (d *Decoder) ReadToken() (Token, error)` — consumes one token.
    /// Object member names are returned as string tokens, as in jsontext.
    pub fn read_token(&mut self) -> Result<Token, serde_json::Error> {
        let kind = self.preamble()?;
        let token = match kind {
            b'{' | b'[' => {
                self.consume_byte();
                self.stack.push(Frame {
                    is_object: kind == b'{',
                    count: 0,
                    expect_name: true,
                });
                Token {
                    kind,
                    raw: Cow::Owned(vec![kind]),
                }
            }
            b'}' | b']' => {
                self.consume_byte();
                self.stack.pop();
                Token {
                    kind,
                    raw: Cow::Owned(vec![kind]),
                }
            }
            b'"' => Token {
                kind,
                raw: Cow::Owned(self.read_string_raw()?),
            },
            b'n' | b't' | b'f' => Token {
                kind,
                raw: Cow::Owned(self.read_literal_raw()?),
            },
            b'0' => Token {
                kind,
                raw: Cow::Owned(self.read_number_raw()?),
            },
            _ => {
                return Err(serde_json::Error::io(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid token kind {}", kind as char),
                )));
            }
        };
        self.pending = None;
        Ok(token)
    }

    /// `func (d *Decoder) ReadValue() (Value, error)` — consumes one whole
    /// JSON value and returns its raw bytes.
    pub fn read_value(&mut self) -> Result<Value, serde_json::Error> {
        let kind = self.preamble()?;
        let mut raw = Vec::new();
        match kind {
            b'{' | b'[' => {
                // Consume through the matching close bracket, skipping over
                // string contents (brackets inside strings don't count).
                let mut depth = 0i32;
                loop {
                    let Some(b) = self.peek_byte().map_err(serde_json::Error::io)? else {
                        return Err(serde_json::Error::io(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "unexpected EOF in JSON value",
                        )));
                    };
                    match b {
                        b'"' => raw.extend_from_slice(&self.read_string_raw()?),
                        b'{' | b'[' => {
                            depth += 1;
                            raw.push(b);
                            self.consume_byte();
                        }
                        b'}' | b']' => {
                            depth -= 1;
                            raw.push(b);
                            self.consume_byte();
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {
                            raw.push(b);
                            self.consume_byte();
                        }
                    }
                }
            }
            b'"' => raw = self.read_string_raw()?,
            b'n' | b't' | b'f' => raw = self.read_literal_raw()?,
            b'0' => raw = self.read_number_raw()?,
            _ => {
                return Err(serde_json::Error::io(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid token kind {}", kind as char),
                )));
            }
        }
        self.pending = None;
        let s = String::from_utf8(raw).map_err(|_| {
            serde_json::Error::io(io::Error::new(
                io::ErrorKind::InvalidData,
                "JSON value is not valid UTF-8",
            ))
        })?;
        // RawValue::from_string validates the raw JSON (jsontext does the
        // same validation on ReadValue).
        RawValue::from_string(s)
    }

    /// `func (d *Decoder) SkipValue() error`
    pub fn skip_value(&mut self) -> Result<(), serde_json::Error> {
        self.read_value().map(|_| ())
    }

    /// Reads a `"..."` string token verbatim (escapes kept raw).
    fn read_string_raw(&mut self) -> Result<Vec<u8>, serde_json::Error> {
        let mut raw = Vec::new();
        self.expect_byte(b'"')?;
        raw.push(b'"');
        loop {
            let Some(b) = self.peek_byte().map_err(serde_json::Error::io)? else {
                return Err(serde_json::Error::io(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "unexpected EOF in JSON string",
                )));
            };
            raw.push(b);
            self.consume_byte();
            match b {
                b'\\' => {
                    let Some(escaped) = self.peek_byte().map_err(serde_json::Error::io)? else {
                        return Err(serde_json::Error::io(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "unexpected EOF in JSON string escape",
                        )));
                    };
                    raw.push(escaped);
                    self.consume_byte();
                }
                b'"' => return Ok(raw),
                _ => {}
            }
        }
    }

    /// Reads a `null`/`true`/`false` literal verbatim. PORT: spelling is not
    /// validated (jsontext rejects e.g. "nul").
    fn read_literal_raw(&mut self) -> Result<Vec<u8>, serde_json::Error> {
        let mut raw = Vec::new();
        while let Some(b) = self.peek_byte().map_err(serde_json::Error::io)? {
            if !b.is_ascii_alphabetic() {
                break;
            }
            raw.push(b);
            self.consume_byte();
        }
        Ok(raw)
    }

    /// Reads a number token verbatim. PORT: grammar is not validated.
    fn read_number_raw(&mut self) -> Result<Vec<u8>, serde_json::Error> {
        let mut raw = Vec::new();
        while let Some(b) = self.peek_byte().map_err(serde_json::Error::io)? {
            if !matches!(b, b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
                break;
            }
            raw.push(b);
            self.consume_byte();
        }
        Ok(raw)
    }
}

/// `type Encoder = jsontext.Encoder` — a streaming token writer. `,` and `:`
/// separators are inserted automatically, as in jsontext; the resolved
/// options are set at construction (jsontext takes them on NewEncoder).
pub struct Encoder<W: io::Write> {
    out: W,
    resolved: ResolvedOptions,
    stack: Vec<Frame>,
    root_written: bool,
}

impl<W: io::Write> Encoder<W> {
    /// `jsontext.NewEncoder(w)` — the Go facade doesn't export a constructor
    /// (encoders arrive via `MarshalJSONTo`), but Rust callers building a
    /// `MarshalJSONTo` port need one.
    pub fn new(out: W) -> Encoder<W> {
        Encoder {
            out,
            resolved: resolve_options(&[]),
            stack: Vec::new(),
            root_written: false,
        }
    }

    /// NewEncoder with resolved options.
    pub fn with_options(out: W, opts: &[Options]) -> Encoder<W> {
        Encoder {
            out,
            resolved: resolve_options(opts),
            stack: Vec::new(),
            root_written: false,
        }
    }

    /// Returns the wrapped writer (jsontext has no equivalent; needed to
    /// recover a `&mut Vec<u8>` or finish an owned writer).
    pub fn into_inner(self) -> W {
        self.out
    }

    fn depth(&self) -> usize {
        self.stack.len()
    }

    /// Writes the newline+prefix+indent that precedes an element at the
    /// current depth — only when an indent option is set.
    fn write_indent(&mut self) -> Result<(), serde_json::Error> {
        if let Some(indent) = &self.resolved.indent {
            self.out.write_all(b"\n").map_err(serde_json::Error::io)?;
            if let Some(prefix) = &self.resolved.indent_prefix {
                self.out
                    .write_all(prefix.as_bytes())
                    .map_err(serde_json::Error::io)?;
            }
            for _ in 0..self.depth() {
                self.out
                    .write_all(indent.as_bytes())
                    .map_err(serde_json::Error::io)?;
            }
        }
        Ok(())
    }

    /// Writes the `,`/`:` separators implied by the container stack and
    /// updates element bookkeeping — mirrors jsontext's pre-token state work.
    fn before_element(&mut self) -> Result<(), serde_json::Error> {
        match self.stack.last_mut() {
            None => {
                // PORT: jsontext rejects a second top-level value.
                if self.root_written {
                    return Err(serde_json::Error::io(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "cannot write multiple JSON values",
                    )));
                }
                self.root_written = true;
            }
            Some(frame) if frame.is_object => {
                if frame.expect_name {
                    if frame.count > 0 {
                        self.out.write_all(b",").map_err(serde_json::Error::io)?;
                    }
                    frame.expect_name = false;
                } else {
                    if self.resolved.indent.is_some() {
                        self.out.write_all(b": ").map_err(serde_json::Error::io)?;
                    } else {
                        self.out.write_all(b":").map_err(serde_json::Error::io)?;
                    }
                    frame.expect_name = true;
                    frame.count += 1;
                }
            }
            Some(frame) => {
                if frame.count > 0 {
                    self.out.write_all(b",").map_err(serde_json::Error::io)?;
                }
                frame.count += 1;
            }
        }
        // Element-start indent (not before the ':' of a member value).
        let needs_indent = match self.stack.last() {
            None => false,
            Some(frame) if frame.is_object => !frame.expect_name,
            Some(_) => true,
        };
        if needs_indent {
            self.write_indent()?;
        }
        Ok(())
    }

    /// `func (e *Encoder) WriteToken(t Token) error`
    pub fn write_token(&mut self, t: &Token) -> Result<(), serde_json::Error> {
        match t.kind {
            b'{' | b'[' => {
                self.before_element()?;
                self.out.write_all(&t.raw).map_err(serde_json::Error::io)?;
                self.stack.push(Frame {
                    is_object: t.kind == b'{',
                    count: 0,
                    expect_name: true,
                });
            }
            b'}' | b']' => {
                // PORT: jsontext validates bracket matching; we trust callers.
                let Some(frame) = self.stack.pop() else {
                    return Err(serde_json::Error::io(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "unmatched close bracket",
                    )));
                };
                if frame.count > 0 {
                    self.write_indent()?;
                }
                self.out.write_all(&t.raw).map_err(serde_json::Error::io)?;
            }
            _ => {
                self.before_element()?;
                self.out.write_all(&t.raw).map_err(serde_json::Error::io)?;
            }
        }
        Ok(())
    }

    /// `func (e *Encoder) WriteValue(v Value) error` — writes raw JSON bytes
    /// verbatim (PORT: jsontext validates `v` on write; we don't).
    pub fn write_value(&mut self, v: &Value) -> Result<(), serde_json::Error> {
        self.before_element()?;
        self.write_blob(v.get().as_bytes())
    }

    /// Writes a fully-formed JSON blob, shifting its pretty-printed lines by
    /// the encoder's current depth (jsontext encodes nested values directly
    /// at depth; identical output).
    fn write_blob(&mut self, bytes: &[u8]) -> Result<(), serde_json::Error> {
        if self.resolved.indent.is_none() || self.depth() == 0 {
            return self.out.write_all(bytes).map_err(serde_json::Error::io);
        }
        let mut insert = Vec::new();
        if let Some(prefix) = &self.resolved.indent_prefix {
            insert.extend_from_slice(prefix.as_bytes());
        }
        let indent = self.resolved.indent.clone().unwrap_or_default();
        for _ in 0..self.depth() {
            insert.extend_from_slice(indent.as_bytes());
        }
        for (i, &b) in bytes.iter().enumerate() {
            self.out.write_all(&[b]).map_err(serde_json::Error::io)?;
            if b == b'\n' && i + 1 < bytes.len() {
                self.out.write_all(&insert).map_err(serde_json::Error::io)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn point() -> BTreeMap<&'static str, i32> {
        BTreeMap::from([("x", 1), ("y", 2)])
    }

    #[test]
    fn test_marshal() {
        let bytes = marshal(&point(), &[]).unwrap();
        assert_eq!(bytes, br#"{"x":1,"y":2}"#);
    }

    #[test]
    fn test_marshal_indent() {
        // MarshalIndent with empty prefix+indent is plain Marshal.
        let bytes = marshal_indent(&point(), "", "").unwrap();
        assert_eq!(bytes, br#"{"x":1,"y":2}"#);

        let bytes = marshal_indent(&vec![1, 2], "", "  ").unwrap();
        assert_eq!(String::from_utf8(bytes).unwrap(), "[\n  1,\n  2\n]");
    }

    #[test]
    fn test_marshal_indent_prefix() {
        let bytes = marshal_indent(&vec![1], ">>", "  ").unwrap();
        assert_eq!(String::from_utf8(bytes).unwrap(), "[\n>>  1\n>>]");
    }

    #[test]
    fn test_marshal_write() {
        let mut buf = Vec::new();
        marshal_write(&mut buf, &point(), &[]).unwrap();
        assert_eq!(buf, br#"{"x":1,"y":2}"#);
    }

    #[test]
    fn test_unmarshal() {
        let p: BTreeMap<String, i32> = unmarshal(br#"{"x":1,"y":2}"#, &[]).unwrap();
        assert_eq!(
            p,
            BTreeMap::from([("x".to_string(), 1), ("y".to_string(), 2)])
        );
    }

    #[test]
    fn test_unmarshal_read() {
        let p: BTreeMap<String, i32> = unmarshal_read(br#"{"x":1,"y":2}"#.as_slice(), &[]).unwrap();
        assert_eq!(
            p,
            BTreeMap::from([("x".to_string(), 1), ("y".to_string(), 2)])
        );
    }

    #[test]
    fn test_encoder_object_stream() {
        // Mirrors api/proto.go's MarshalJSONTo shape.
        let mut buf = Vec::new();
        let mut enc = Encoder::new(&mut buf);
        enc.write_token(&BEGIN_OBJECT).unwrap();
        enc.write_value(&RawValue::from_string("\"responses\"".to_string()).unwrap())
            .unwrap();
        enc.write_token(&BEGIN_ARRAY).unwrap();
        marshal_encode(&mut enc, &1, &[]).unwrap();
        marshal_encode(&mut enc, &2, &[]).unwrap();
        enc.write_token(&END_ARRAY).unwrap();
        enc.write_token(&END_OBJECT).unwrap();
        assert_eq!(buf, br#"{"responses":[1,2]}"#);
    }

    #[test]
    fn test_decoder_read_tokens() {
        let mut dec = new_decoder(br#"{"a":1,"b":[2,null]}"#.as_slice());
        assert_eq!(dec.peek_kind().unwrap(), b'{');
        assert_eq!(dec.read_token().unwrap().kind(), b'{');
        assert_eq!(dec.peek_kind().unwrap(), b'"');
        let name = dec.read_token().unwrap();
        assert_eq!(name.bytes(), b"\"a\"");
        assert_eq!(dec.read_token().unwrap().kind(), b'0');
        let name = dec.read_token().unwrap();
        assert_eq!(name.bytes(), b"\"b\"");
        assert_eq!(dec.read_token().unwrap().kind(), b'[');
        assert_eq!(dec.read_token().unwrap().kind(), b'0');
        assert_eq!(dec.read_token().unwrap().kind(), b'n');
        assert_eq!(dec.read_token().unwrap().kind(), b']');
        assert_eq!(dec.read_token().unwrap().kind(), b'}');
    }

    #[test]
    fn test_decoder_unmarshal_decode() {
        // Mirrors collections/ordered_map.go's UnmarshalJSONFrom shape:
        // ReadToken '{' / 'n', PeekKind '}', UnmarshalDecode key/value pairs.
        let mut dec = new_decoder(br#"{"a":1,"b":2}"#.as_slice());
        let token = dec.read_token().unwrap();
        assert_eq!(token.kind(), b'{');
        let mut entries = Vec::new();
        loop {
            if dec.peek_kind().unwrap() == b'}' {
                dec.read_token().unwrap();
                break;
            }
            let key: String = unmarshal_decode(&mut dec, &[]).unwrap();
            let value: i64 = unmarshal_decode(&mut dec, &[]).unwrap();
            entries.push((key, value));
        }
        assert_eq!(entries, vec![("a".to_string(), 1), ("b".to_string(), 2)]);
    }

    #[test]
    fn test_decoder_null() {
        let mut dec = new_decoder(b"null".as_slice());
        let token = dec.read_token().unwrap();
        assert_eq!(token.kind(), b'n');
    }
}
