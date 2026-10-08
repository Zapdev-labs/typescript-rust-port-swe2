// Ported from tsc/internal/api/encoder/stringtable.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go `stringTable.fileText` shares the source-file `string`
// zero-copy; the port stores the source-file `NodeId` and resolves
// `text` against the node arena on each call, since the arena `Vec<Node>`
// cannot be aliased while it is mutably borrowed for encoding.
// `otherText` is a `[]byte` builder instead of `strings.Builder`
// (equivalent append semantics; final bytes are identical).

use tsc_ast::{Kind, Node, NodeId};

/// `type stringTable struct`
pub struct StringTable {
    /// The source file whose text forms the first part of the string data
    /// section, or `None` when encoding a subtree detached from a file.
    file_node: Option<NodeId>,
    /// Start/end offset pairs into the final string data section.
    offsets: Vec<u32>,
    /// Additional strings which could not be represented as slices of
    /// `fileText`.
    strings: Vec<u8>,
}

impl StringTable {
    /// `func newStringTable(fileText string, count int) *stringTable`
    ///
    /// `count` is an estimate of the number of strings that will be added.
    pub fn new(file_node: Option<NodeId>, count: i32) -> Self {
        StringTable {
            file_node,
            offsets: Vec::with_capacity(8 * count.max(0) as usize),
            strings: Vec::new(),
        }
    }

    fn file_text<'a>(&self, nodes: &'a [Node]) -> &'a [u8] {
        match self.file_node {
            Some(file) => nodes[file].as_source_file().text.as_bytes(),
            None => b"",
        }
    }

    /// `func (t *stringTable) add(text string, kind ast.Kind, pos, end int) uint32`
    ///
    /// Adds `text` to the string table, returning the offset of the offsets
    /// entry in the final string offsets section.
    ///
    /// If the text can be represented as a slice of `fileText`, the string
    /// offsets are used directly. Otherwise, the text is appended to
    /// `t.strings`.
    pub fn add(&mut self, nodes: &[Node], text: &[u8], kind: Kind, pos: i32, end: i32) -> u32 {
        if kind == Kind::SourceFile {
            let index = self.offsets.len() as u32;
            self.offsets.push(pos as u32);
            self.offsets.push(end as u32);
            return index;
        }

        let start = pos;
        let mut end = end;
        match kind {
            // Adjust end to point to the closing quote.
            Kind::StringLiteral | Kind::TemplateTail | Kind::NoSubstitutionTemplateLiteral => {
                end -= 1;
            }
            _ => {}
        }

        let file_text = self.file_text(nodes);
        // PORT: the `start >= 0` guard is a safe superset of Go's check —
        // `fileText[start:end]` would panic on a negative index there.
        if end - start > 0
            && (end as usize) <= file_text.len()
            && start >= 0
            && &file_text[start as usize..end as usize] == text
        {
            let index = self.offsets.len() as u32;
            self.offsets.push(start as u32);
            self.offsets.push(end as u32);
            return index;
        }

        // Can't represent the string as a slice of the file text.
        let index = self.offsets.len() as u32;
        self.offsets.push((file_text.len() + self.strings.len()) as u32);
        self.strings.extend_from_slice(text);
        self.offsets
            .push((file_text.len() + self.strings.len()) as u32);
        index
    }

    /// `func (t *stringTable) encode() []byte`
    ///
    /// Encodes the string table as a byte slice, including the file text.
    /// The caller is responsible for prepending the offsets to the output.
    pub fn encode(&self, nodes: &[Node]) -> Vec<u8> {
        let file_text = self.file_text(nodes);
        let mut result = Vec::with_capacity(self.offsets.len() * 4 + file_text.len() + self.strings.len());
        for &offset in &self.offsets {
            result.extend_from_slice(&offset.to_le_bytes());
        }
        result.extend_from_slice(file_text);
        result.extend_from_slice(&self.strings);
        result
    }

    /// `len(t.offsets)` — the number of u32s in the offsets section.
    pub fn offsets_len(&self) -> usize {
        self.offsets.len()
    }

    /// `t.stringLength()` — `len(t.fileText) + len(t.strings)`.
    pub fn string_length(&self, nodes: &[Node]) -> usize {
        self.file_text(nodes).len() + self.strings.len()
    }
}
