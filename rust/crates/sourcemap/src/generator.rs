// Ported from tsc/internal/sourcemap/generator.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use serde::Serialize;
use tsc_core::core::UTF16Offset;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath};

/// `type SourceIndex int`
pub type SourceIndex = i32;
/// `type NameIndex int`
pub type NameIndex = i32;

const SOURCE_INDEX_NOT_SET: SourceIndex = -1;
const NAME_INDEX_NOT_SET: NameIndex = -1;
const NOT_SET: i32 = -1;
const NOT_SET_UTF16: UTF16Offset = -1;

/// `type Generator struct`
///
/// PORT: `strings.Builder` becomes `String`; `map[string]SourceIndex` becomes
/// `FxHashMap`. Go's `SetSourceContent`/`Add*Mapping` return `error`; here
/// they return `Result<(), &'static str>` carrying the same message.
pub struct Generator {
    case_sensitivity: CaseSensitivity,
    file: String,
    source_root: String,
    sources_directory_path: RootedDirectoryPath,
    raw_sources: Vec<String>,
    sources: Vec<String>,
    source_to_source_index_map: rustc_hash::FxHashMap<String, SourceIndex>,
    /// Go `[]*string`; `None` entries correspond to nil elements.
    sources_content: Vec<Option<String>>,
    names: Vec<String>,
    name_to_name_index_map: rustc_hash::FxHashMap<String, NameIndex>,
    mappings: String,
    last_generated_line: i32,
    last_generated_character: UTF16Offset,
    last_source_index: SourceIndex,
    last_source_line: i32,
    last_source_character: UTF16Offset,
    last_name_index: NameIndex,
    has_last: bool,
    pending_generated_line: i32,
    pending_generated_character: UTF16Offset,
    pending_source_index: SourceIndex,
    pending_source_line: i32,
    pending_source_character: UTF16Offset,
    pending_name_index: NameIndex,
    has_pending: bool,
    has_pending_source: bool,
    has_pending_name: bool,
}

/// `type RawSourceMap struct`
///
/// PORT: Go's `sourceRoot,omitzero` omits the field when the string is empty
/// (`skip_serializing_if = "String::is_empty"`); `sourcesContent,omitzero`
/// omits the field when the slice is nil — modeled as `Option<Vec<..>>` with
/// `None` entries inside the vec matching Go's `*string` elements.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct RawSourceMap {
    pub version: i32,
    pub file: String,
    #[serde(rename = "sourceRoot", skip_serializing_if = "String::is_empty")]
    pub source_root: String,
    pub sources: Vec<String>,
    pub names: Vec<String>,
    pub mappings: String,
    #[serde(rename = "sourcesContent", skip_serializing_if = "Option::is_none")]
    pub sources_content: Option<Vec<Option<String>>>,
}

/// `func NewGenerator(file string, sourceRoot string, sourcesDirectoryPath tspath.RootedDirectoryPath, caseSensitivity tspath.CaseSensitivity) *Generator`
impl Generator {
    pub fn new(
        file: &str,
        source_root: &str,
        sources_directory_path: impl Into<RootedDirectoryPath>,
        case_sensitivity: CaseSensitivity,
    ) -> Generator {
        Generator {
            case_sensitivity,
            file: file.to_string(),
            source_root: source_root.to_string(),
            sources_directory_path: sources_directory_path.into(),
            raw_sources: Vec::new(),
            sources: Vec::new(),
            source_to_source_index_map: rustc_hash::FxHashMap::default(),
            sources_content: Vec::new(),
            names: Vec::new(),
            name_to_name_index_map: rustc_hash::FxHashMap::default(),
            mappings: String::new(),
            last_generated_line: 0,
            last_generated_character: 0,
            last_source_index: 0,
            last_source_line: 0,
            last_source_character: 0,
            last_name_index: 0,
            has_last: false,
            pending_generated_line: 0,
            pending_generated_character: 0,
            pending_source_index: 0,
            pending_source_line: 0,
            pending_source_character: 0,
            pending_name_index: 0,
            has_pending: false,
            has_pending_source: false,
            has_pending_name: false,
        }
    }

    /// `func (gen *Generator) Sources() []string`
    pub fn sources(&self) -> &[String] {
        &self.raw_sources
    }

    /// `func (gen *Generator) AddSource(fileName tspath.RootedFilePath) SourceIndex`
    ///
    /// Adds a source to the source map.
    pub fn add_source(&mut self, file_name: impl Into<RootedFilePath>) -> SourceIndex {
        let file_name = file_name.into();
        let source = tsc_tspath::get_relative_path_to_directory_or_url(
            self.sources_directory_path.as_string(),
            file_name.as_string(),
            true,
            self.case_sensitivity,
        );

        let source_index = match self.source_to_source_index_map.get(&source) {
            Some(&source_index) => source_index,
            None => {
                let source_index = self.sources.len() as SourceIndex;
                self.sources.push(source.clone());
                self.raw_sources.push(file_name.as_string().to_string());
                self.source_to_source_index_map.insert(source, source_index);
                source_index
            }
        };

        source_index
    }

    /// `func (gen *Generator) SetSourceContent(sourceIndex SourceIndex, content string) error`
    ///
    /// Sets the content for a source.
    pub fn set_source_content(
        &mut self,
        source_index: SourceIndex,
        content: &str,
    ) -> Result<(), &'static str> {
        if source_index < 0 || source_index as usize >= self.sources.len() {
            return Err("sourceIndex is out of range");
        }
        while self.sources_content.len() <= source_index as usize {
            self.sources_content.push(None);
        }
        self.sources_content[source_index as usize] = Some(content.to_string());
        Ok(())
    }

    /// `func (gen *Generator) AddName(name string) NameIndex`
    ///
    /// Declares a name in the source map, returning the index of the name.
    pub fn add_name(&mut self, name: &str) -> NameIndex {
        match self.name_to_name_index_map.get(name) {
            Some(&name_index) => name_index,
            None => {
                let name_index = self.names.len() as NameIndex;
                self.names.push(name.to_string());
                self.name_to_name_index_map
                    .insert(name.to_string(), name_index);
                name_index
            }
        }
    }

    fn is_new_generated_position(
        &self,
        generated_line: i32,
        generated_character: UTF16Offset,
    ) -> bool {
        !self.has_pending
            || self.pending_generated_line != generated_line
            || self.pending_generated_character != generated_character
    }

    fn is_backtracking_source_position(
        &self,
        source_index: SourceIndex,
        source_line: i32,
        source_character: UTF16Offset,
    ) -> bool {
        source_index != SOURCE_INDEX_NOT_SET
            && source_line != NOT_SET
            && source_character != NOT_SET_UTF16
            && self.pending_source_index == source_index
            && (self.pending_source_line > source_line
                || (self.pending_source_line == source_line
                    && self.pending_source_character > source_character))
    }

    fn should_commit_mapping(&self) -> bool {
        self.has_pending
            && (!self.has_last
                || self.last_generated_line != self.pending_generated_line
                || self.last_generated_character != self.pending_generated_character
                || self.last_source_index != self.pending_source_index
                || self.last_source_line != self.pending_source_line
                || self.last_source_character != self.pending_source_character
                || self.last_name_index != self.pending_name_index)
    }

    fn append_mapping_char_code(&mut self, char_code: char) {
        self.mappings.push(char_code);
    }

    /// `func (gen *Generator) appendBase64VLQ(inValue int)`
    ///
    /// PORT: Go `int` is 64-bit and wraps on overflow; `wrapping_*` ops keep
    /// this byte-exact for pathological inputs.
    fn append_base64_vlq(&mut self, mut in_value: i64) {
        // Add a new least significant bit that has the sign of the value.
        // if negative number the least significant bit that gets added to the number has value 1
        // else least significant bit value that gets added is 0
        // eg. -1 changes to binary : 01 [1] => 3
        //     +1 changes to binary : 01 [0] => 2
        if in_value < 0 {
            in_value = in_value.wrapping_neg().wrapping_shl(1).wrapping_add(1);
        } else {
            in_value = in_value.wrapping_shl(1);
        }

        // Encode 5 bits at a time starting from least significant bits
        loop {
            let mut current_digit = in_value & 31; // 11111
            in_value >>= 5;
            if in_value > 0 {
                // There are still more digits to decode, set the msb (6th bit)
                current_digit |= 32;
            }
            self.append_mapping_char_code(base64_format_encode(current_digit));
            if in_value <= 0 {
                break;
            }
        }
    }

    fn commit_pending_mapping(&mut self) {
        if !self.should_commit_mapping() {
            return;
        }

        // Line/Comma delimiters
        if self.last_generated_line < self.pending_generated_line {
            // Emit line delimiters
            loop {
                self.append_mapping_char_code(';');
                self.last_generated_line += 1;
                if self.last_generated_line >= self.pending_generated_line {
                    break;
                }
            }
            // Only need to set this once
            self.last_generated_character = 0;
        } else {
            if self.last_generated_line != self.pending_generated_line {
                // panic rather than error as an invariant has been violated
                panic!("generatedLine cannot backtrack");
            }
            // Emit comma to separate the entry
            if self.has_last {
                self.append_mapping_char_code(',');
            }
        }

        // 1. Relative generated character
        self.append_base64_vlq(i64::from(
            self.pending_generated_character - self.last_generated_character,
        ));
        self.last_generated_character = self.pending_generated_character;

        if self.has_pending_source {
            // 2. Relative sourceIndex
            self.append_base64_vlq(i64::from(
                self.pending_source_index - self.last_source_index,
            ));
            self.last_source_index = self.pending_source_index;

            // 3. Relative source line
            self.append_base64_vlq(i64::from(self.pending_source_line - self.last_source_line));
            self.last_source_line = self.pending_source_line;

            // 4. Relative source character
            self.append_base64_vlq(i64::from(
                self.pending_source_character - self.last_source_character,
            ));
            self.last_source_character = self.pending_source_character;

            if self.has_pending_name {
                // 5. Relative nameIndex
                self.append_base64_vlq(i64::from(self.pending_name_index - self.last_name_index));
                self.last_name_index = self.pending_name_index;
            }
        }

        self.has_last = true;
    }

    fn add_mapping(
        &mut self,
        generated_line: i32,
        generated_character: UTF16Offset,
        source_index: SourceIndex,
        source_line: i32,
        source_character: UTF16Offset,
        name_index: NameIndex,
    ) {
        if self.is_new_generated_position(generated_line, generated_character)
            || self.is_backtracking_source_position(source_index, source_line, source_character)
        {
            self.commit_pending_mapping();
            self.pending_generated_line = generated_line;
            self.pending_generated_character = generated_character;
            self.has_pending_source = false;
            self.has_pending_name = false;
            self.has_pending = true;
        }

        if source_index != SOURCE_INDEX_NOT_SET
            && source_line != NOT_SET
            && source_character != NOT_SET_UTF16
        {
            self.pending_source_index = source_index;
            self.pending_source_line = source_line;
            self.pending_source_character = source_character;
            self.has_pending_source = true;
            if name_index != NAME_INDEX_NOT_SET {
                self.pending_name_index = name_index;
                self.has_pending_name = true;
            }
        }
    }

    /// `func (gen *Generator) AddGeneratedMapping(generatedLine int, generatedCharacter core.UTF16Offset) error`
    ///
    /// Adds a mapping without source information.
    pub fn add_generated_mapping(
        &mut self,
        generated_line: i32,
        generated_character: UTF16Offset,
    ) -> Result<(), &'static str> {
        if generated_line < self.pending_generated_line {
            return Err("generatedLine cannot backtrack");
        }
        if generated_character < 0 {
            return Err("generatedCharacter cannot be negative");
        }
        self.add_mapping(
            generated_line,
            generated_character,
            SOURCE_INDEX_NOT_SET,
            NOT_SET,       /* sourceLine */
            NOT_SET_UTF16, /* sourceCharacter */
            NAME_INDEX_NOT_SET,
        );
        self.has_pending_source = false;
        self.has_pending_name = false;
        Ok(())
    }

    /// `func (gen *Generator) AddSourceMapping(generatedLine int, generatedCharacter core.UTF16Offset, sourceIndex SourceIndex, sourceLine int, sourceCharacter core.UTF16Offset) error`
    ///
    /// Adds a mapping with source information.
    pub fn add_source_mapping(
        &mut self,
        generated_line: i32,
        generated_character: UTF16Offset,
        source_index: SourceIndex,
        source_line: i32,
        source_character: UTF16Offset,
    ) -> Result<(), &'static str> {
        if generated_line < self.pending_generated_line {
            return Err("generatedLine cannot backtrack");
        }
        if generated_character < 0 {
            return Err("generatedCharacter cannot be negative");
        }
        if source_index < 0 || source_index as usize >= self.sources.len() {
            return Err("sourceIndex is out of range");
        }
        if source_line < 0 {
            return Err("sourceLine cannot be negative");
        }
        if source_character < 0 {
            return Err("sourceCharacter cannot be negative");
        }
        if self.has_pending
            && !self.is_new_generated_position(generated_line, generated_character)
            && !self.has_pending_source
        {
            return Ok(());
        }
        self.add_mapping(
            generated_line,
            generated_character,
            source_index,
            source_line,
            source_character,
            NAME_INDEX_NOT_SET,
        );
        Ok(())
    }

    /// `func (gen *Generator) AddNamedSourceMapping(generatedLine int, generatedCharacter core.UTF16Offset, sourceIndex SourceIndex, sourceLine int, sourceCharacter core.UTF16Offset, nameIndex NameIndex) error`
    ///
    /// Adds a mapping with source and name information.
    pub fn add_named_source_mapping(
        &mut self,
        generated_line: i32,
        generated_character: UTF16Offset,
        source_index: SourceIndex,
        source_line: i32,
        source_character: UTF16Offset,
        name_index: NameIndex,
    ) -> Result<(), &'static str> {
        if generated_line < self.pending_generated_line {
            return Err("generatedLine cannot backtrack");
        }
        if generated_character < 0 {
            return Err("generatedCharacter cannot be negative");
        }
        if source_index < 0 || source_index as usize >= self.sources.len() {
            return Err("sourceIndex is out of range");
        }
        if source_line < 0 {
            return Err("sourceLine cannot be negative");
        }
        if source_character < 0 {
            return Err("sourceCharacter cannot be negative");
        }
        if name_index < 0 || name_index as usize >= self.names.len() {
            return Err("nameIndex is out of range");
        }
        if self.has_pending
            && !self.is_new_generated_position(generated_line, generated_character)
            && !self.has_pending_source
        {
            return Ok(());
        }
        self.add_mapping(
            generated_line,
            generated_character,
            source_index,
            source_line,
            source_character,
            name_index,
        );
        Ok(())
    }

    /// `func (gen *Generator) RawSourceMap() *RawSourceMap`
    ///
    /// Gets the source map as a `RawSourceMap` object.
    pub fn raw_source_map(&mut self) -> RawSourceMap {
        self.commit_pending_mapping();
        // PORT: `slices.Clone` + nil-to-empty normalization is implicit in the
        // owned Vec; `sourcesContent` nil becomes `None` (see RawSourceMap).
        RawSourceMap {
            version: 3,
            file: self.file.clone(),
            source_root: self.source_root.clone(),
            sources: self.sources.clone(),
            names: self.names.clone(),
            mappings: self.mappings.clone(),
            sources_content: if self.sources_content.is_empty() {
                None
            } else {
                Some(self.sources_content.clone())
            },
        }
    }

    fn bytes(&mut self) -> Vec<u8> {
        match tsc_json::marshal(&self.raw_source_map(), &[]) {
            Ok(buf) => buf,
            Err(err) => panic!("{err}"),
        }
    }

    /// `func (gen *Generator) String() string`
    ///
    /// Gets the string representation of the source map.
    ///
    /// PORT: not implemented via `fmt::Display` — it takes `&mut self`
    /// because producing the map commits the pending mapping.
    pub fn to_json_string(&mut self) -> String {
        // PORT: Go's `string(gen.bytes())` copies; the marshal output is
        // always valid UTF-8 JSON.
        String::from_utf8(self.bytes()).expect("source map JSON is valid UTF-8")
    }

    /// `func (gen *Generator) Base64DataURL() string`
    pub fn base64_data_url(&mut self) -> String {
        const PREFIX: &str = "data:application/json;base64,";
        let data = self.bytes();
        let mut sb = String::with_capacity(PREFIX.len() + data.len().div_ceil(3) * 4);
        sb.push_str(PREFIX);
        sb.push_str(&crate::base64::encode(&data));
        sb
    }
}

/// `func base64FormatEncode(value int) rune`
fn base64_format_encode(value: i64) -> char {
    match value {
        0..=25 => (b'A' + value as u8) as char,
        26..=51 => (b'a' + value as u8 - 26) as char,
        52..=61 => (b'0' + value as u8 - 52) as char,
        62 => '+',
        63 => '/',
        _ => panic!("not a base64 value"),
    }
}
