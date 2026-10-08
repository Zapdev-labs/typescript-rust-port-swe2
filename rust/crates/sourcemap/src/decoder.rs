// Ported from tsc/internal/sourcemap/decoder.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::core::UTF16Offset;

use crate::generator::{NameIndex, SourceIndex};

/// `type Mapping struct`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Mapping {
    pub generated_line: i32,
    pub generated_character: UTF16Offset,
    pub source_index: SourceIndex,
    pub source_line: i32,
    pub source_character: UTF16Offset,
    pub name_index: NameIndex,
}

impl Mapping {
    /// `func (m *Mapping) Equals(other *Mapping) bool` — Go's pointer-equality
    /// fast path is subsumed by field equality.
    pub fn equals(&self, other: &Mapping) -> bool {
        self == other
    }

    /// `func (m *Mapping) IsSourceMapping() bool`
    pub fn is_source_mapping(&self) -> bool {
        self.source_index != MISSING_SOURCE
            && self.source_line != MISSING_LINE_OR_COLUMN
            && self.source_character != MISSING_UTF16_COLUMN
    }
}

/// `const MissingSource SourceIndex = -1`
pub const MISSING_SOURCE: SourceIndex = -1;
/// `const MissingName NameIndex = -1`
pub const MISSING_NAME: NameIndex = -1;
/// `const MissingLineOrColumn int = -1`
pub const MISSING_LINE_OR_COLUMN: i32 = -1;
/// `const MissingUTF16Column core.UTF16Offset = -1`
pub const MISSING_UTF16_COLUMN: UTF16Offset = -1;

/// `type MappingsDecoder struct`
///
/// PORT: `iter.Seq[*Mapping]` (`Values`) becomes the `Iterator` impl; each
/// yielded `*Mapping` was allocated from a `core.Arena[Mapping]` in Go, while
/// here owned `Mapping` values are yielded. `mappings` is stored as `&str`
/// and indexed by byte position, matching Go's `d.mappings[d.pos]` byte
/// access.
pub struct MappingsDecoder<'a> {
    mappings: &'a str,
    done: bool,
    pos: usize,
    generated_line: i32,
    generated_character: UTF16Offset,
    source_index: SourceIndex,
    source_line: i32,
    source_character: UTF16Offset,
    name_index: NameIndex,
    error: Option<String>,
}

/// `func DecodeMappings(mappings string) *MappingsDecoder`
pub fn decode_mappings(mappings: &str) -> MappingsDecoder<'_> {
    MappingsDecoder {
        mappings,
        done: false,
        pos: 0,
        generated_line: 0,
        generated_character: 0,
        source_index: 0,
        source_line: 0,
        source_character: 0,
        name_index: 0,
        error: None,
    }
}

impl<'a> MappingsDecoder<'a> {
    /// `func (d *MappingsDecoder) MappingsString() string`
    pub fn mappings_string(&self) -> &'a str {
        self.mappings
    }

    /// `func (d *MappingsDecoder) Pos() int`
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// `func (d *MappingsDecoder) Error() error` — returns the error message.
    pub fn error(&self) -> Option<&str> {
        self.error.as_deref()
    }

    /// `func (d *MappingsDecoder) State() *Mapping`
    pub fn state(&self) -> Mapping {
        self.capture_mapping(true /* hasSource */, true /* hasName */)
    }

    /// `func (d *MappingsDecoder) Next() (value *Mapping, done bool)` —
    /// `Some(mapping)` while mappings remain, `None` when done.
    pub fn next_mapping(&mut self) -> Option<Mapping> {
        while !self.done && self.pos < self.mappings.len() {
            let ch = self.mappings.as_bytes()[self.pos];
            if ch == b';' {
                // new line
                self.generated_line += 1;
                self.generated_character = 0;
                self.pos += 1;
                continue;
            }

            if ch == b',' {
                // Next entry is on same line - no action needed
                self.pos += 1;
                continue;
            }

            let mut has_source = false;
            let mut has_name = false;
            // PORT: Go converts the decoded `int` to `core.UTF16Offset`
            // (an int); the Rust port narrows to i32 via `as`.
            self.generated_character += self.base64_vlq_format_decode() as UTF16Offset;
            if self.has_reported_error() {
                return self.stop_iterating();
            }
            if self.generated_character < 0 {
                return self.set_error_and_stop_iterating("Invalid generatedCharacter found");
            }

            if !self.is_source_mapping_segment_end() {
                has_source = true;

                self.source_index += self.base64_vlq_format_decode() as SourceIndex;
                if self.has_reported_error() {
                    return self.stop_iterating();
                }
                if self.source_index < 0 {
                    return self.set_error_and_stop_iterating("Invalid sourceIndex found");
                }
                if self.is_source_mapping_segment_end() {
                    return self.set_error_and_stop_iterating(
                        "Unsupported Format: No entries after sourceIndex",
                    );
                }

                self.source_line += self.base64_vlq_format_decode() as i32;
                if self.has_reported_error() {
                    return self.stop_iterating();
                }
                if self.source_line < 0 {
                    return self.set_error_and_stop_iterating("Invalid sourceLine found");
                }
                if self.is_source_mapping_segment_end() {
                    return self.set_error_and_stop_iterating(
                        "Unsupported Format: No entries after sourceLine",
                    );
                }

                self.source_character += self.base64_vlq_format_decode() as UTF16Offset;
                if self.has_reported_error() {
                    return self.stop_iterating();
                }
                if self.source_character < 0 {
                    return self.set_error_and_stop_iterating("Invalid sourceCharacter found");
                }

                if !self.is_source_mapping_segment_end() {
                    has_name = true;
                    self.name_index += self.base64_vlq_format_decode() as NameIndex;
                    if self.has_reported_error() {
                        return self.stop_iterating();
                    }
                    if self.name_index < 0 {
                        return self.set_error_and_stop_iterating("Invalid nameIndex found");
                    }

                    if !self.is_source_mapping_segment_end() {
                        return self.set_error_and_stop_iterating(
                            "Unsupported Error Format: Entries after nameIndex",
                        );
                    }
                }
            }

            return Some(self.capture_mapping(has_source, has_name));
        }

        self.stop_iterating()
    }

    fn capture_mapping(&self, has_source: bool, has_name: bool) -> Mapping {
        Mapping {
            generated_line: self.generated_line,
            generated_character: self.generated_character,
            source_index: if has_source {
                self.source_index
            } else {
                MISSING_SOURCE
            },
            source_line: if has_source {
                self.source_line
            } else {
                MISSING_LINE_OR_COLUMN
            },
            source_character: if has_source {
                self.source_character
            } else {
                MISSING_UTF16_COLUMN
            },
            name_index: if has_name {
                self.name_index
            } else {
                MISSING_NAME
            },
        }
    }

    fn stop_iterating(&mut self) -> Option<Mapping> {
        self.done = true;
        None
    }

    fn set_error(&mut self, err: &str) {
        self.error = Some(err.to_string());
    }

    fn set_error_and_stop_iterating(&mut self, err: &str) -> Option<Mapping> {
        self.set_error(err);
        self.stop_iterating()
    }

    fn has_reported_error(&self) -> bool {
        self.error.is_some()
    }

    fn is_source_mapping_segment_end(&self) -> bool {
        self.pos == self.mappings.len()
            || self.mappings.as_bytes()[self.pos] == b','
            || self.mappings.as_bytes()[self.pos] == b';'
    }

    /// `func (d *MappingsDecoder) base64VLQFormatDecode() int`
    ///
    /// PORT: Go `int` is 64-bit and wraps on overflow; decoded values here are
    /// i64 with Go's shift semantics (a left shift by >= 64 produces 0) so the
    /// accumulation is byte-exact even for pathological inputs.
    fn base64_vlq_format_decode(&mut self) -> i64 {
        let mut more_digits = true;
        let mut shift_count: u32 = 0;
        let mut value: i64 = 0;
        while more_digits {
            if self.pos >= self.mappings.len() {
                self.set_error("Error in decoding base64VLQFormatDecode, past the mapping string");
                return -1;
            }

            // 6 digit number
            let current_byte = base64_format_decode(self.mappings.as_bytes()[self.pos]);
            if current_byte == -1 {
                self.set_error("Invalid character in VLQ");
                return -1;
            }

            // If msb is set, we still have more bits to continue
            more_digits = (current_byte & 32) != 0;

            // least significant 5 bits are the next msbs in the final value.
            // PORT: Go's `<<` produces 0 for shift counts >= the bit width;
            // Rust would panic, so the shift is clamped instead.
            if shift_count < 64 {
                value |= (current_byte & 31) << shift_count;
            }
            shift_count += 5;
            self.pos += 1;
        }

        // Least significant bit if 1 represents negative and rest of the msb is actual absolute value
        if (value & 1) == 0 {
            // + number
            value >>= 1;
        } else {
            // - number
            value >>= 1;
            value = -value;
        }

        value
    }
}

/// `func (d *MappingsDecoder) Values() iter.Seq[*Mapping]` — the decoder
/// itself is the iterator.
impl Iterator for MappingsDecoder<'_> {
    type Item = Mapping;

    fn next(&mut self) -> Option<Mapping> {
        self.next_mapping()
    }
}

fn base64_format_decode(ch: u8) -> i64 {
    match ch {
        b'A'..=b'Z' => i64::from(ch - b'A'),
        b'a'..=b'z' => i64::from(ch - b'a' + 26),
        b'0'..=b'9' => i64::from(ch - b'0' + 52),
        b'+' => 62,
        b'/' => 63,
        _ => -1,
    }
}
