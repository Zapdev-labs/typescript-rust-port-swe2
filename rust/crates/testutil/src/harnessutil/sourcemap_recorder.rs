// Ported from tsc/internal/testutil/harnessutil/sourcemap_recorder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `writerAggregator` is `WriterAggregator` — a `String` wrapper whose
// `write_line*` append `\r\n`. `*sourcemap.Mapping` is the owned
// `sourcemap::Mapping` value (the Rust `MappingsDecoder` yields owned
// `Mapping`s; Go's `*Mapping` sharing is only observational identity). The
// `decodedMapping.error` Go `error` becomes `Option<String>`.

use std::fmt::Write as _;

use tsc_core::core::compute_ecma_line_starts;
use tsc_core::text::TextPos;
use tsc_scanner::scanner::compute_position_of_line_and_utf16_character;
use tsc_sourcemap::{self as sourcemap, Mapping, MappingsDecoder};
use tsc_stringutil::remove_byte_order_mark;

use super::TestFile;

/// `type writerAggregator struct` — embeds `strings.Builder`.
#[derive(Default)]
pub struct WriterAggregator {
    buf: String,
}

impl WriterAggregator {
    pub fn write_stringf(&mut self, args: std::fmt::Arguments<'_>) {
        self.buf.write_fmt(args).expect("fmt::Write on String");
    }

    /// `WriteString`.
    pub fn write_string(&mut self, s: &str) {
        self.buf.push_str(s);
    }

    pub fn write_line(&mut self, s: &str) {
        self.buf.push_str(s);
        self.buf.push_str("\r\n");
    }

    /// `String()` — returns the accumulated output (`strings.Builder.String`).
    pub fn into_string(self) -> String {
        self.buf
    }

    /// `strings.Builder.String` without consuming.
    pub fn as_str(&self) -> &str {
        &self.buf
    }
}

/// `WriteStringf` — `fmt.Sprintf` is `format!` at the call site.
macro_rules! write_stringf {
    ($w:expr, $($arg:tt)*) => {
        $w.write_stringf(format_args!($($arg)*))
    };
}

/// `WriteLinef`.
macro_rules! write_linef {
    ($w:expr, $($arg:tt)*) => {
        $w.write_line(&format!($($arg)*))
    };
}

/// `type sourceMapSpanWithDecodeErrors struct`.
struct SourceMapSpanWithDecodeErrors {
    source_map_span: Mapping,
    decode_errors: Vec<String>,
}

/// `type decodedMapping struct`.
struct DecodedMapping {
    source_map_span: Mapping,
    error: Option<String>,
}

/// `type sourceMapDecoder struct`.
struct SourceMapDecoder<'a> {
    source_map_mappings: &'a str,
    mappings: MappingsDecoder<'a>,
}

/// `newSourceMapDecoder`.
fn new_source_map_decoder(source_map: &sourcemap::RawSourceMap) -> SourceMapDecoder<'_> {
    SourceMapDecoder {
        source_map_mappings: &source_map.mappings,
        mappings: sourcemap::decode_mappings(&source_map.mappings),
    }
}

impl SourceMapDecoder<'_> {
    /// `decodeNextEncodedSourceMapSpan` — `MappingsDecoder.Next` returns
    /// `Option`; the `done` arm inspects `error()`/`state()`.
    fn decode_next_encoded_source_map_span(&mut self) -> DecodedMapping {
        match self.mappings.next() {
            None => {
                let error = self
                    .mappings
                    .error()
                    .map(|e| e.to_string())
                    .unwrap_or_else(|| "No encoded entry found".to_string());
                DecodedMapping {
                    error: Some(error),
                    source_map_span: self.mappings.state(),
                }
            }
            Some(value) => DecodedMapping {
                source_map_span: value,
                error: None,
            },
        }
    }

    fn has_completed_decoding(&self) -> bool {
        self.mappings.pos() == self.source_map_mappings.len()
    }

    fn get_remaining_decode_string(&self) -> &str {
        &self.source_map_mappings[self.mappings.pos()..]
    }
}

/// `type sourceMapSpanWriter struct`.
pub struct SourceMapSpanWriter<'a> {
    source_map_recorder: &'a mut WriterAggregator,
    source_map_sources: Vec<String>,
    source_map_names: Vec<String>,
    js_file: &'a TestFile,
    js_line_map: Vec<TextPos>,
    ts_code: String,
    ts_line_map: Vec<TextPos>,
    spans_on_single_line: Vec<SourceMapSpanWithDecodeErrors>,
    prev_written_source_pos: usize,
    next_js_line_to_write: i32,
    span_marker_continues: bool,
    source_map_decoder: SourceMapDecoder<'a>,
}

/// `newSourceMapSpanWriter` — writes the recorder header.
pub fn new_source_map_span_writer<'a>(
    source_map_recorder: &'a mut WriterAggregator,
    source_map: &'a sourcemap::RawSourceMap,
    js_file: &'a TestFile,
) -> SourceMapSpanWriter<'a> {
    let writer = SourceMapSpanWriter {
        source_map_recorder,
        source_map_sources: source_map.sources.clone(),
        source_map_names: source_map.names.clone(),
        js_file,
        js_line_map: compute_ecma_line_starts(&js_file.content),
        ts_code: String::new(),
        ts_line_map: Vec::new(),
        spans_on_single_line: Vec::new(),
        prev_written_source_pos: 0,
        next_js_line_to_write: 0,
        span_marker_continues: false,
        source_map_decoder: new_source_map_decoder(source_map),
    };

    writer
        .source_map_recorder
        .write_line("===================================================================");
    write_linef!(writer.source_map_recorder, "JsFile: {}", source_map.file);
    write_linef!(
        writer.source_map_recorder,
        "mapUrl: {}",
        sourcemap::try_get_source_mapping_url(Some(&sourcemap::create_ecma_line_info(
            js_file.content.clone(),
            writer.js_line_map.clone(),
        )))
    );
    write_linef!(
        writer.source_map_recorder,
        "sourceRoot: {}",
        source_map.source_root
    );
    write_linef!(
        writer.source_map_recorder,
        "sources: {}",
        source_map.sources.join(",")
    );
    if let Some(sources_content) = &source_map.sources_content
        && !sources_content.is_empty()
    {
        // `json.Marshal(sourceMap.SourcesContent)` — `[]*string`.
        let content =
            serde_json::to_string(sources_content).expect("sourcesContent serializes to JSON");
        write_linef!(writer.source_map_recorder, "sourcesContent: {}", content);
    }
    writer
        .source_map_recorder
        .write_line("===================================================================");
    writer
}

impl<'a> SourceMapSpanWriter<'a> {
    /// `w.getSourceMapSpanString`.
    fn get_source_map_span_string(
        &self,
        map_entry: &Mapping,
        get_absent_name_index: bool,
    ) -> String {
        let mut map_string = WriterAggregator::default();
        write_stringf!(
            map_string,
            "Emitted({}, {})",
            map_entry.generated_line + 1,
            map_entry.generated_character + 1
        );
        if map_entry.is_source_mapping() {
            write_stringf!(
                map_string,
                " Source({}, {}) + SourceIndex({})",
                map_entry.source_line + 1,
                map_entry.source_character + 1,
                map_entry.source_index
            );
            if map_entry.name_index >= 0
                && (map_entry.name_index as usize) < self.source_map_names.len()
            {
                write_stringf!(
                    map_string,
                    " name ({})",
                    self.source_map_names[map_entry.name_index as usize]
                );
            } else if map_entry.name_index != sourcemap::MISSING_NAME || get_absent_name_index {
                write_stringf!(map_string, " nameIndex ({})", map_entry.name_index);
            }
        }
        map_string.into_string()
    }

    /// `w.recordSourceMapSpan`.
    pub fn record_source_map_span(&mut self, source_map_span: Mapping) {
        // verify the decoded span is same as the new span
        let decode_result = self
            .source_map_decoder
            .decode_next_encoded_source_map_span();
        let mut decode_errors: Vec<String> = Vec::new();
        if decode_result.error.is_some() || !decode_result.source_map_span.equals(&source_map_span)
        {
            if let Some(error) = &decode_result.error {
                decode_errors = vec![
                    "!!^^ !!^^ There was decoding error in the sourcemap at this location: "
                        .to_string()
                        + error,
                ];
            } else {
                decode_errors = vec![
                    "!!^^ !!^^ The decoded span from sourcemap's mapping entry does not match what was encoded for this span:"
                        .to_string(),
                ];
            }
            decode_errors.push(
                "!!^^ !!^^ Decoded span from sourcemap's mappings entry: ".to_string()
                    + &self.get_source_map_span_string(&decode_result.source_map_span, true)
                    + " Span encoded by the emitter:"
                    + &self.get_source_map_span_string(&source_map_span, true),
            );
        }

        if !self.spans_on_single_line.is_empty()
            && self.spans_on_single_line[0].source_map_span.generated_line
                != source_map_span.generated_line
        {
            // On different line from the one that we have been recording till now,
            self.write_recorded_spans();
            self.spans_on_single_line.clear();
        }
        self.spans_on_single_line
            .push(SourceMapSpanWithDecodeErrors {
                source_map_span,
                decode_errors,
            });
    }

    /// `w.recordNewSourceFileSpan`.
    pub fn record_new_source_file_span(
        &mut self,
        source_map_span: Mapping,
        new_source_file_code: &str,
    ) {
        let mut continues_line = false;
        if !self.spans_on_single_line.is_empty()
            && self.spans_on_single_line[0]
                .source_map_span
                .generated_character
                == source_map_span.generated_line
        {
            // !!! char == line seems like a bug in Strada?
            self.write_recorded_spans();
            self.spans_on_single_line.clear();
            self.next_js_line_to_write -= 1; // walk back one line to reprint the line
            continues_line = true;
        }

        self.record_source_map_span(source_map_span);

        assert!(
            self.spans_on_single_line.len() == 1,
            "expected a single span"
        );

        self.source_map_recorder
            .write_line("-------------------------------------------------------------------");
        if continues_line {
            write_linef!(
                self.source_map_recorder,
                "emittedFile:{} ({}, {})",
                self.js_file.unit_name,
                source_map_span.generated_line + 1,
                source_map_span.generated_character + 1
            );
        } else {
            write_linef!(
                self.source_map_recorder,
                "emittedFile:{}",
                self.js_file.unit_name
            );
        }
        write_linef!(
            self.source_map_recorder,
            "sourceFile:{}",
            self.source_map_sources
                [self.spans_on_single_line[0].source_map_span.source_index as usize]
        );
        self.source_map_recorder
            .write_line("-------------------------------------------------------------------");

        self.ts_line_map = compute_ecma_line_starts(new_source_file_code);
        self.ts_code = new_source_file_code.to_string();
        self.prev_written_source_pos = 0;
    }

    /// `w.close`.
    pub fn close(&mut self) {
        // Write the lines pending on the single line
        self.write_recorded_spans();

        if !self.source_map_decoder.has_completed_decoding() {
            self.source_map_recorder.write_line(
                "!!!! **** There are more source map entries in the sourceMap's mapping than what was encoded",
            );
            write_linef!(
                self.source_map_recorder,
                "!!!! **** Remaining decoded string: {}",
                self.source_map_decoder.get_remaining_decode_string()
            );
        }

        // write remaining js lines
        self.write_js_file_lines(self.js_line_map.len() as i32);
    }

    /// `w.getTextOfLine`.
    fn get_text_of_line(&self, line: i32, line_map: &[TextPos], code: &str) -> String {
        let start_pos = line_map[line as usize] as usize;
        let end_pos = if (line as usize) + 1 < line_map.len() {
            line_map[line as usize + 1] as usize
        } else {
            code.len()
        };
        let text = &code.as_bytes()[start_pos..end_pos];
        if line == 0 {
            return String::from_utf8_lossy(remove_byte_order_mark(text)).into_owned();
        }
        String::from_utf8_lossy(text).into_owned()
    }

    /// `w.writeJsFileLines`.
    fn write_js_file_lines(&mut self, end_js_line: i32) {
        while self.next_js_line_to_write < end_js_line {
            let text = self.get_text_of_line(
                self.next_js_line_to_write,
                &self.js_line_map,
                &self.js_file.content,
            );
            write_stringf!(self.source_map_recorder, ">>>{}", text);
            self.next_js_line_to_write += 1;
        }
    }

    /// `w.writeRecordedSpans`.
    fn write_recorded_spans(&mut self) {
        let mut recorded_span_writer = RecordedSpanWriter {
            marker_ids: Vec::new(),
            prev_emitted_col: 0,
            w: self,
        };
        recorded_span_writer.write_recorded_spans();
    }
}

/// `type recordedSpanWriter struct`.
struct RecordedSpanWriter<'a, 'b> {
    marker_ids: Vec<String>,
    prev_emitted_col: i32,
    w: &'a mut SourceMapSpanWriter<'b>,
}

impl RecordedSpanWriter<'_, '_> {
    /// `sw.getMarkerId`.
    fn get_marker_id(&mut self, marker_index: usize) -> String {
        if self.w.span_marker_continues {
            assert!(marker_index == 0, "expected markerIndex to be 0");
            "1->".to_string()
        } else {
            let mut marker_id = (marker_index + 1).to_string();
            if marker_id.len() < 2 {
                marker_id.push(' ');
            }
            marker_id.push('>');
            marker_id
        }
    }

    /// `sw.iterateSpans` — `fn` takes `(&mut self, index)` like Go's closure
    /// fields `prevEmittedCol`.
    fn iterate_spans(&mut self, mut f: impl FnMut(&mut Self, usize)) {
        self.prev_emitted_col = 0;
        for i in 0..self.w.spans_on_single_line.len() {
            f(self, i);
            self.prev_emitted_col = self.w.spans_on_single_line[i]
                .source_map_span
                .generated_character;
        }
    }

    /// `sw.writeSourceMapIndent`.
    fn write_source_map_indent(&mut self, indent_length: i32, indent_prefix: &str) {
        self.w.source_map_recorder.write_string(indent_prefix);
        for _ in 0..indent_length {
            self.w.source_map_recorder.write_string(" ");
        }
    }

    /// `sw.writeSourceMapMarker`.
    fn write_source_map_marker(&mut self, index: usize) {
        let end_column = self.w.spans_on_single_line[index]
            .source_map_span
            .generated_character;
        self.write_source_map_marker_ex(index, end_column, false);
    }

    /// `sw.writeSourceMapMarkerEx`.
    fn write_source_map_marker_ex(&mut self, index: usize, end_column: i32, end_continues: bool) {
        let marker_id = self.get_marker_id(index);
        self.marker_ids.push(marker_id.clone());
        self.write_source_map_indent(self.prev_emitted_col, &marker_id);
        for _ in self.prev_emitted_col..end_column {
            self.w.source_map_recorder.write_string("^");
        }
        if end_continues {
            self.w.source_map_recorder.write_string("->");
        }
        self.w.source_map_recorder.write_line("");
        self.w.span_marker_continues = end_continues;
    }

    /// `sw.writeSourceMapSourceText`.
    fn write_source_map_source_text(&mut self, index: usize) {
        // Convert UTF-16 character offset from the source map to a byte position.
        let source_pos = compute_position_of_line_and_utf16_character(
            &self.w.ts_line_map,
            self.w.spans_on_single_line[index]
                .source_map_span
                .source_line,
            self.w.spans_on_single_line[index]
                .source_map_span
                .source_character,
            &self.w.ts_code,
            true, // allowEdits
        ) as usize;
        // Go: `w.tsCode[w.prevWrittenSourcePos:sourcePos]` slices bytes, which
        // can split a multi-byte character; `from_utf8_lossy` is the closest
        // `&str` analogue.
        let mut source_text = String::new();
        if self.w.prev_written_source_pos < source_pos {
            // Position that goes forward, get text
            source_text = String::from_utf8_lossy(
                &self.w.ts_code.as_bytes()[self.w.prev_written_source_pos..source_pos],
            )
            .into_owned();
        }
        let source_text: &str = &source_text;

        // If there are decode errors, write
        for decode_error in self.w.spans_on_single_line[index].decode_errors.clone() {
            let marker_id = self.marker_ids[index].clone();
            self.write_source_map_indent(self.prev_emitted_col, &marker_id);
            self.w.source_map_recorder.write_line(&decode_error);
        }

        let ts_code_line_map = compute_ecma_line_starts(source_text);
        for i in 0..ts_code_line_map.len() {
            if i == 0 {
                let marker_id = self.marker_ids[index].clone();
                self.write_source_map_indent(self.prev_emitted_col, &marker_id);
            } else {
                self.write_source_map_indent(self.prev_emitted_col, "  >");
            }
            let line = self
                .w
                .get_text_of_line(i as i32, &ts_code_line_map, source_text);
            self.w.source_map_recorder.write_string(&line);
            if i == ts_code_line_map.len() - 1 {
                self.w.source_map_recorder.write_line("");
            }
        }

        self.w.prev_written_source_pos = source_pos;
    }

    /// `sw.writeSpanDetails`.
    fn write_span_details(&mut self, index: usize) {
        let span_string = self.w.get_source_map_span_string(
            &self.w.spans_on_single_line[index].source_map_span,
            false, // getAbsentNameIndex
        );
        write_linef!(
            self.w.source_map_recorder,
            "{}{}",
            self.marker_ids[index],
            span_string
        );
    }

    /// `sw.writeRecordedSpans`.
    fn write_recorded_spans(&mut self) {
        if !self.w.spans_on_single_line.is_empty() {
            let current_js_line = self.w.spans_on_single_line[0]
                .source_map_span
                .generated_line;

            // Write js line
            self.w.write_js_file_lines(current_js_line + 1);

            // Emit markers
            self.iterate_spans(|sw, i| sw.write_source_map_marker(i));

            let js_file_text = self.w.get_text_of_line(
                current_js_line + 1,
                &self.w.js_line_map,
                &self.w.js_file.content,
            ); // TODO: Strada is wrong here, we should be looking at `currentJsLine`, not `currentJsLine+1`
            if self.prev_emitted_col < js_file_text.len() as i32 - 1 {
                // There is remaining text on this line that will be part of next source span so write marker that continues
                self.write_source_map_marker_ex(
                    self.w.spans_on_single_line.len(),
                    js_file_text.len() as i32 - 1, // endColumn
                    true,                          // endContinues
                );
            }

            // Emit Source text
            self.iterate_spans(|sw, i| sw.write_source_map_source_text(i));

            // Emit column number etc
            self.iterate_spans(|sw, i| sw.write_span_details(i));

            self.w.source_map_recorder.write_line("---");
        }
    }
}
