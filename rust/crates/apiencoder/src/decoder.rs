// Ported from tsc/internal/api/encoder/decoder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go `*ast.Node` results are `NodeId`s into a `Vec<Node>` arena owned
// by the decoder; `decode_nodes`/`decode_source_file` return
// `(root: NodeId, arena: Vec<Node>)`. Go's `*ast.NodeList`/`allocNodeSlice`
// arena is replaced by owned `NodeList` values stored per encoded index
// (cloned on use — see `node_list_at`).
//
// PORT: `getString` substrings Go's `string` (WTF-8 tolerant); Rust `String`
// cannot hold WTF-8, so byte strings are decoded with
// `String::from_utf8_lossy` — the same conversion the parser performs —
// which is lossless for spec-compliant inputs.

use std::fmt;

use tsc_ast::parseoptions::{ExternalModuleIndicatorOptions, SourceFileParseOptions};
use tsc_ast::{Kind, Node, NodeFactory, NodeFlags, NodeId, NodeList, TokenFlags};
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::TextRange;
use tsc_tspath::{try_path_key_from_canonical, try_rooted_file_path_from_normalized};

use crate::decoder_generated::{
    create_children_node, create_extended_node, create_string_node, kind_from_u32,
};
use crate::encoder::{
    HEADER_OFFSET_EXTENDED_DATA, HEADER_OFFSET_METADATA, HEADER_OFFSET_NODES,
    HEADER_OFFSET_PARSE_OPTIONS, HEADER_OFFSET_STRING_DATA, HEADER_OFFSET_STRING_OFFSETS,
    HEADER_SIZE, NODE_DATA_TYPE_EXTENDED_DATA, NODE_DATA_TYPE_MASK, NODE_DATA_TYPE_STRING,
    NODE_DATA_STRING_INDEX_MASK, NODE_OFFSET_DATA, NODE_OFFSET_END, NODE_OFFSET_FLAGS,
    NODE_OFFSET_KIND, NODE_OFFSET_NEXT, NODE_OFFSET_PARENT, NODE_OFFSET_POS, NODE_SIZE,
    PROTOCOL_VERSION,
    SYNTAX_KIND_NODE_LIST,
};

/// `fmt.Errorf`/`errors.New` values become `DecodeError`.
#[derive(Debug)]
pub struct DecodeError(pub String);

impl DecodeError {
    pub(crate) fn new(msg: impl Into<String>) -> DecodeError {
        DecodeError(msg.into())
    }
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for DecodeError {}

/// `astDecoder` reconstructs real AST nodes from binary-encoded data.
pub(crate) struct AstDecoder<'a> {
    raw: &'a [u8],
    str_table: u32,
    str_data: u32,
    ext_data: u32,
    node_off: u32,
    node_count: usize,
    pub(crate) factory: NodeFactory<'static>,
    /// Results: decoded node ids and node lists, per encoded index.
    pub(crate) decoded: Vec<Option<NodeId>>,
    pub(crate) node_lists: Vec<Option<NodeList>>,
    /// The node arena being built.
    pub(crate) arena: Vec<Node>,
}

/// `DecodeSourceFile` decodes binary-encoded data into a source file.
pub fn decode_source_file(data: &[u8]) -> Result<(NodeId, Vec<Node>), DecodeError> {
    let (node, arena) = decode_nodes(data)?;
    if arena[node].kind != Kind::SourceFile {
        return Err(DecodeError::new(format!(
            "expected SourceFile root, got {:?}",
            arena[node].kind
        )));
    }
    Ok((node, arena))
}

/// `DecodeNodes` decodes binary-encoded AST data into a tree of nodes.
/// Returns `(root, arena)`.
pub fn decode_nodes(data: &[u8]) -> Result<(NodeId, Vec<Node>), DecodeError> {
    let mut d = new_ast_decoder(data)?;
    let root = d.decode()?;
    Ok((root, d.arena))
}

fn new_ast_decoder(data: &[u8]) -> Result<AstDecoder<'_>, DecodeError> {
    if data.len() < HEADER_SIZE {
        return Err(DecodeError::new(format!(
            "data too short for header: {} bytes",
            data.len()
        )));
    }
    let version = data[HEADER_OFFSET_METADATA + 3];
    if version != PROTOCOL_VERSION {
        return Err(DecodeError::new(format!(
            "unsupported protocol version {version} (expected {PROTOCOL_VERSION})"
        )));
    }

    let str_table = read_le32(data, HEADER_OFFSET_STRING_OFFSETS);
    let str_data = read_le32(data, HEADER_OFFSET_STRING_DATA);
    let ext_data = read_le32(data, HEADER_OFFSET_EXTENDED_DATA);
    let node_off = read_le32(data, HEADER_OFFSET_NODES);

    let data_len = data.len() as u32;

    // Validate that all offsets are within the buffer.
    if str_table > data_len || str_data > data_len || ext_data > data_len || node_off > data_len {
        return Err(DecodeError::new(format!(
            "invalid AST header offsets: offsets exceed data length ({data_len})"
        )));
    }

    // Validate monotonic non-decreasing order of regions.
    if !(str_table <= str_data && str_data <= ext_data && ext_data <= node_off) {
        return Err(DecodeError::new(format!(
            "invalid AST header offsets: expected strTable <= strData <= extData <= nodeOff (got {str_table}, {str_data}, {ext_data}, {node_off})"
        )));
    }

    let node_count = (data.len() - node_off as usize) / NODE_SIZE;

    Ok(AstDecoder {
        raw: data,
        str_table,
        str_data,
        ext_data,
        node_off,
        node_count,
        factory: NodeFactory::default(),
        decoded: Vec::new(),
        node_lists: Vec::new(),
        arena: Vec::new(),
    })
}

/// `readLE32` — returns 0 for out-of-bounds reads (mirrors Go).
pub(crate) fn read_le32(data: &[u8], offset: usize) -> u32 {
    if offset + 4 > data.len() {
        return 0;
    }
    u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap())
}

impl<'a> AstDecoder<'a> {
    /// `nodeField` reads a uint32 field from node `i` at the given field offset.
    pub(crate) fn node_field(&self, i: usize, field: usize) -> u32 {
        read_le32(self.raw, self.node_off as usize + i * NODE_SIZE + field)
    }

    /// `getString`
    ///
    /// PORT: returns raw bytes; callers apply `from_utf8_lossy` where Go
    /// would hand back a `string` substring.
    pub(crate) fn get_string(&self, idx: u32) -> &'a [u8] {
        let off_base = self.str_table as usize + idx as usize * 4;
        let start = read_le32(self.raw, off_base) as usize;
        let end = read_le32(self.raw, off_base + 4) as usize;
        // Go: `d.allStringData[start:end]` — panics on out-of-range, as does
        // this slice (allStringData = raw[strData:]).
        &self.raw[self.str_data as usize + start..self.str_data as usize + end]
    }

    /// Lossy UTF-8 view of a stored string (see file-level PORT note).
    pub(crate) fn get_string_text(&self, idx: u32) -> String {
        String::from_utf8_lossy(self.get_string(idx)).into_owned()
    }

    /// `collectChildren` returns indices of direct children of node `i`.
    ///
    /// PORT: Go reuses `d.childBuf`; the port passes a caller-owned buffer
    /// (equivalent reuse without aliasing `self`).
    fn collect_children(&self, i: usize, buf: &mut Vec<usize>) {
        buf.clear();
        if i + 1 >= self.node_count {
            return;
        }
        let first_child = i + 1;
        if self.node_field(first_child, NODE_OFFSET_PARENT) != i as u32 {
            return;
        }
        buf.push(first_child);
        let mut next = self.node_field(first_child, NODE_OFFSET_NEXT) as usize;
        while next != 0 {
            buf.push(next);
            next = self.node_field(next, NODE_OFFSET_NEXT) as usize;
        }
    }

    /// `d.decode()`
    fn decode(&mut self) -> Result<NodeId, DecodeError> {
        if self.node_count < 2 {
            return Err(DecodeError::new("no nodes to decode"));
        }

        self.decoded = vec![None; self.node_count];
        self.node_lists = vec![None; self.node_count];

        let mut child_buf: Vec<usize> = Vec::new();

        // Process bottom-up so children exist before parents.
        for i in (1..self.node_count).rev() {
            let kind = self.node_field(i, NODE_OFFSET_KIND);
            let pos = self.node_field(i, NODE_OFFSET_POS);
            let end = self.node_field(i, NODE_OFFSET_END);
            let data = self.node_field(i, NODE_OFFSET_DATA);
            self.collect_children(i, &mut child_buf);

            if kind == SYNTAX_KIND_NODE_LIST {
                let child_nodes: Vec<NodeId> = child_buf
                    .iter()
                    .filter_map(|&ci| self.decoded[ci])
                    .collect();
                let mut nl = self.factory.new_node_list(child_nodes);
                nl.loc = TextRange::new(pos as i32, end as i32);
                self.node_lists[i] = Some(nl);
                continue;
            }

            let node = self
                .create_node(kind, data, &child_buf)
                .map_err(|e| {
                    DecodeError::new(format!("at node {i} (kind {}): {}", kind_from_u32_debug(kind), e))
                })?;
            self.arena[node].loc = TextRange::new(pos as i32, end as i32);
            self.arena[node].flags = NodeFlags(self.node_field(i, NODE_OFFSET_FLAGS));
            if kind == Kind::SourceFile as i16 as u32 {
                let is_declaration_file =
                    self.arena[node].flags.intersects(NodeFlags::AMBIENT);
                self.arena[node].as_source_file_mut().is_declaration_file = is_declaration_file;
            }
            self.decoded[i] = Some(node);
        }

        // `d.nodes[1]` — the root node is always written.
        Ok(self.decoded[1].expect("decoder: root node missing"))
    }

    // `nodeAt`/`nodeListAt`/`modifierListAt`/`singleChild`/
    // `singleNodeListChild`/`getModifierList` live in `decoder_generated.rs`
    // as free functions over the destructured fields so they can be called
    // inside factory-call argument lists without overlapping `self` borrows.

    /// `d.createNode(kind, data, childIndices)`
    fn create_node(
        &mut self,
        kind: u32,
        data: u32,
        child_indices: &[usize],
    ) -> Result<NodeId, DecodeError> {
        let data_type = data & NODE_DATA_TYPE_MASK;
        let common_data = ((data >> 24) & 0x3f) as u8;
        // Go: `ast.Kind(kind)` — an unchecked u32→int16 truncation; out-of-range
        // values reach the switch `default:` and error. The port errors when
        // the truncated ordinal is not a known kind (same observable result).
        let kind = match kind_from_u32(kind) {
            Some(k) => k,
            None => {
                return Err(DecodeError::new(format!(
                    "unhandled node kind {kind} with {} children",
                    child_indices.len()
                )));
            }
        };
        match data_type {
            NODE_DATA_TYPE_STRING => self.create_string_node(kind, data, common_data),
            NODE_DATA_TYPE_EXTENDED_DATA => {
                self.create_extended_node(kind, data, child_indices, common_data)
            }
            _ => self.create_children_node(kind, data, child_indices, common_data),
        }
    }

    fn create_string_node(
        &mut self,
        kind: Kind,
        data: u32,
        common_data: u8,
    ) -> Result<NodeId, DecodeError> {
        create_string_node(self, kind, data, common_data)
    }

    fn create_extended_node(
        &mut self,
        kind: Kind,
        data: u32,
        child_indices: &[usize],
        common_data: u8,
    ) -> Result<NodeId, DecodeError> {
        create_extended_node(self, kind, data, child_indices, common_data)
    }

    fn create_children_node(
        &mut self,
        kind: Kind,
        data: u32,
        child_indices: &[usize],
        common_data: u8,
    ) -> Result<NodeId, DecodeError> {
        create_children_node(self, kind, data, child_indices, common_data)
    }

    /// `decodeExtendedData_SourceFile`
    pub(crate) fn decode_extended_data_source_file(
        &mut self,
        data: u32,
        child_indices: &[usize],
        _common_data: u8,
    ) -> Result<NodeId, DecodeError> {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;

        let text_idx = read_le32(self.raw, ext_off);
        let file_name_idx = read_le32(self.raw, ext_off + 4);
        let path_idx = read_le32(self.raw, ext_off + 8);
        let language_variant = match read_le32(self.raw, ext_off + 12) {
            0 => LanguageVariant::Standard,
            1 => LanguageVariant::Jsx,
            // PORT: Go casts the u32 to `core.LanguageVariant` unchecked; the
            // Rust enum cannot hold an unknown discriminant, so it maps to
            // `Standard`.
            _ => LanguageVariant::Standard,
        };
        let script_kind = match read_le32(self.raw, ext_off + 16) {
            1 => ScriptKind::Js,
            2 => ScriptKind::Jsx,
            3 => ScriptKind::Ts,
            4 => ScriptKind::Tsx,
            6 => ScriptKind::Json,
            // PORT: see language_variant above.
            _ => ScriptKind::Unknown,
        };
        let text = self.get_string(text_idx);
        let file_name = self.get_string(file_name_idx);
        let path_text = self.get_string(path_idx);
        let path = try_path_key_from_canonical(&String::from_utf8_lossy(path_text)).ok_or_else(|| {
            DecodeError::new(format!(
                "invalid source file path {:?}",
                String::from_utf8_lossy(path_text)
            ))
        })?;
        let typed_file_name = try_rooted_file_path_from_normalized(&String::from_utf8_lossy(file_name))
            .ok_or_else(|| {
                DecodeError::new(format!(
                    "invalid source file name {:?}",
                    String::from_utf8_lossy(file_name)
                ))
            })?;

        // Recover parse options from header.
        let parse_opts = read_le32(self.raw, HEADER_OFFSET_PARSE_OPTIONS);
        let opts = SourceFileParseOptions {
            file_name: typed_file_name,
            path_key: path,
            external_module_indicator_options: ExternalModuleIndicatorOptions {
                jsx: parse_opts & 1 != 0,
                force: parse_opts & 2 != 0,
            },
        };

        // Collect children: first is statements NodeList, second is EndOfFile.
        let mut stmts = None;
        let mut end_of_file = None;
        for &ci in child_indices {
            if self.node_field(ci, NODE_OFFSET_KIND) == SYNTAX_KIND_NODE_LIST {
                stmts = self.node_lists[ci].clone();
            } else if self.decoded[ci].is_some()
                && self.arena[self.decoded[ci].unwrap()].kind == Kind::EndOfFile
            {
                end_of_file = self.decoded[ci];
            }
        }
        if end_of_file.is_none() {
            end_of_file = Some(self.factory.new_token(&mut self.arena, Kind::EndOfFile));
        }
        let node = self.factory.new_source_file(
            &mut self.arena,
            &opts,
            &String::from_utf8_lossy(text),
            stmts,
            end_of_file,
        );
        self.arena[node].as_source_file_mut().language_variant = language_variant;
        self.arena[node].as_source_file_mut().script_kind = script_kind;
        Ok(node)
    }

    /// `decodeExtendedData_TemplateHead`
    pub(crate) fn decode_extended_data_template_head(&mut self, data: u32) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let raw_text_idx = read_le32(self.raw, ext_off + 4);
        let flags = read_le32(self.raw, ext_off + 8);
        let text = self.get_string_text(text_idx);
        let raw_text = self.get_string_text(raw_text_idx);
        self.factory
            .new_template_head(&mut self.arena, &text, &raw_text, TokenFlags(flags))
    }

    /// `decodeExtendedData_TemplateMiddle`
    pub(crate) fn decode_extended_data_template_middle(&mut self, data: u32) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let raw_text_idx = read_le32(self.raw, ext_off + 4);
        let flags = read_le32(self.raw, ext_off + 8);
        let text = self.get_string_text(text_idx);
        let raw_text = self.get_string_text(raw_text_idx);
        self.factory
            .new_template_middle(&mut self.arena, &text, &raw_text, TokenFlags(flags))
    }

    /// `decodeExtendedData_TemplateTail`
    pub(crate) fn decode_extended_data_template_tail(&mut self, data: u32) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let raw_text_idx = read_le32(self.raw, ext_off + 4);
        let flags = read_le32(self.raw, ext_off + 8);
        let text = self.get_string_text(text_idx);
        let raw_text = self.get_string_text(raw_text_idx);
        self.factory
            .new_template_tail(&mut self.arena, &text, &raw_text, TokenFlags(flags))
    }

    /// `decodeExtendedData_StringLiteral`
    pub(crate) fn decode_extended_data_string_literal(&mut self, data: u32) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let flags = read_le32(self.raw, ext_off + 4);
        let text = self.get_string_text(text_idx);
        self.factory
            .new_string_literal(&mut self.arena, &text, TokenFlags(flags))
    }

    /// `decodeExtendedData_NumericLiteral`
    pub(crate) fn decode_extended_data_numeric_literal(&mut self, data: u32) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let flags = read_le32(self.raw, ext_off + 4);
        let text = self.get_string_text(text_idx);
        self.factory
            .new_numeric_literal(&mut self.arena, &text, TokenFlags(flags))
    }

    /// `decodeExtendedData_BigIntLiteral`
    pub(crate) fn decode_extended_data_big_int_literal(&mut self, data: u32) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let flags = read_le32(self.raw, ext_off + 4);
        let text = self.get_string_text(text_idx);
        self.factory
            .new_big_int_literal(&mut self.arena, &text, TokenFlags(flags))
    }

    /// `decodeExtendedData_RegularExpressionLiteral`
    pub(crate) fn decode_extended_data_regular_expression_literal(
        &mut self,
        data: u32,
    ) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let flags = read_le32(self.raw, ext_off + 4);
        let text = self.get_string_text(text_idx);
        self.factory
            .new_regular_expression_literal(&mut self.arena, &text, TokenFlags(flags))
    }

    /// `decodeExtendedData_NoSubstitutionTemplateLiteral`
    pub(crate) fn decode_extended_data_no_substitution_template_literal(
        &mut self,
        data: u32,
    ) -> NodeId {
        let ext_off = self.ext_data as usize + (data & NODE_DATA_STRING_INDEX_MASK) as usize;
        let text_idx = read_le32(self.raw, ext_off);
        let flags = read_le32(self.raw, ext_off + 4);
        let text = self.get_string_text(text_idx);
        self.factory
            .new_no_substitution_template_literal(&mut self.arena, &text, TokenFlags(flags))
    }
}

/// Renders the (possibly invalid) wire kind for error messages.
/// Go prints `ast.Kind(kind)` (an int16); match that display shape.
fn kind_from_u32_debug(kind: u32) -> i16 {
    kind as u16 as i16
}
