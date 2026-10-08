// Ported from tsc/internal/sourcemap @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: this module is a local port of Go's `encoding/base64` StdEncoding —
// it is not part of tsc/internal/sourcemap but the Go code depends on it
// (generator.go's `Base64DataURL` encodes; source_mapper.go's data: URL
// handling decodes). Only the entry points used by the port are provided.
// As in Go, the decoder skips '\r' and '\n' anywhere in the input; every
// other character outside the alphabet, and any padding that is not the
// final one or two characters, is a corrupt-input error.

use std::fmt;

const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// `base64.StdEncoding.EncodedLen`/`Encode` — standard base64 with '=' padding.
pub fn encode(data: &[u8]) -> String {
    let mut out = String::with_capacity(data.len().div_ceil(3) * 4);
    for chunk in data.chunks(3) {
        let b0 = u32::from(chunk[0]);
        let b1 = u32::from(*chunk.get(1).unwrap_or(&0));
        let b2 = u32::from(*chunk.get(2).unwrap_or(&0));
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(ALPHABET[((n >> 18) & 63) as usize] as char);
        out.push(ALPHABET[((n >> 12) & 63) as usize] as char);
        out.push(if chunk.len() > 1 {
            ALPHABET[((n >> 6) & 63) as usize] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            ALPHABET[(n & 63) as usize] as char
        } else {
            '='
        });
    }
    out
}

/// `base64.CorruptInputError`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CorruptInputError;

impl fmt::Display for CorruptInputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("illegal base64 data")
    }
}

impl std::error::Error for CorruptInputError {}

fn decode_char(c: u8) -> Result<u8, CorruptInputError> {
    match c {
        b'A'..=b'Z' => Ok(c - b'A'),
        b'a'..=b'z' => Ok(c - b'a' + 26),
        b'0'..=b'9' => Ok(c - b'0' + 52),
        b'+' => Ok(62),
        b'/' => Ok(63),
        _ => Err(CorruptInputError),
    }
}

/// `base64.StdEncoding.DecodeString`
pub fn decode(s: &str) -> Result<Vec<u8>, CorruptInputError> {
    // Go's decoder ignores '\r' and '\n' anywhere in the input.
    let filtered: Vec<u8> = s.bytes().filter(|&b| !matches!(b, b'\r' | b'\n')).collect();
    if filtered.len() % 4 != 0 {
        return Err(CorruptInputError);
    }
    let n_chunks = filtered.len() / 4;
    let mut out = Vec::with_capacity(n_chunks * 3);
    for (i, chunk) in filtered.chunks(4).enumerate() {
        let is_last = i + 1 == n_chunks;
        let mut vals = [0u8; 4];
        let mut pad = 0;
        for (j, &c) in chunk.iter().enumerate() {
            if c == b'=' {
                // Padding is only legal as the last one or two characters of
                // the final quartet.
                if !is_last || j < 2 || pad > 1 {
                    return Err(CorruptInputError);
                }
                pad += 1;
            } else {
                if pad > 0 {
                    // A non-'=' character after '=' within the quartet.
                    return Err(CorruptInputError);
                }
                vals[j] = decode_char(c)?;
            }
        }
        out.push((vals[0] << 2) | (vals[1] >> 4));
        if pad < 2 {
            out.push((vals[1] << 4) | (vals[2] >> 2));
        }
        if pad < 1 {
            out.push((vals[2] << 6) | vals[3]);
        }
    }
    Ok(out)
}
