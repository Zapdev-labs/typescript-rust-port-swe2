// Ported from tsc/internal/api/encoder/encoder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go AST pointers are `NodeId`s into the arena `Vec<Node>`; the
// `nodeTable` is `Box<[Option<NodeId>]>` (`None` where Go stores nil —
// the index-0 sentinel and NodeList pseudo-node entries).
//
// PORT: `EncodeSourceFile`/`EncodeNode`/`encodeTree` in Go return an
// `error` that is always nil (encoder failures panic). The Rust signatures
// drop the `Result` and keep the panic semantics (`panic!` where Go
// panics).
//
// PORT: `encodeTree`'s visitor `Visit`/`VisitNodes`/`VisitModifiers`
// closures in Go close over `prevIndex`/`parentIndex`/`nodeCount` locals.
// Rust closures cannot share mutable captures through the `Fn` visitor
// contract, so the state lives behind a `RefCell<EncSt>` and is borrowed
// only for the duration of one record emission (never across recursive
// `visit_each_child` calls).

use std::cell::RefCell;
use std::sync::{Arc, LazyLock, OnceLock};

use rustc_hash::FxHashMap;
use tsc_ast::ast_generated::SourceFile;
use tsc_ast::parseoptions::ExternalModuleIndicatorOptions;
use tsc_ast::positionmap::{PositionMap, compute_position_map};
use tsc_ast::{
    FileReference, Kind, MappedDiagnosticDirective, ModifierList, Node, NodeFactory, NodeId,
    NodeList, NodeVisitor, NodeVisitorHooks, SourceFileDataKey, Uint128, VisitorCx,
    get_or_compute_data, js_doc, new_source_file_data_key,
};
use tsc_spanmap::{Feature, SpanMap};
use xxhash_rust::xxh3::xxh3_128;

use crate::encoder_generated::{
    get_children_property_mask, get_node_common_data, get_node_data_type, record_extended_data,
    record_node_strings,
};
use crate::stringtable::StringTable;

// `init` — the 6-bit commonData budget check is a compile-time property.
const _: () = assert!(
    Kind::LAST_UNARY_OPERATOR as i16 <= 0x3f,
    "KindLastUnaryOperator exceeds the 6-bit commonData capacity"
);

pub const NODE_OFFSET_KIND: usize = 0;
pub const NODE_OFFSET_POS: usize = 4;
pub const NODE_OFFSET_END: usize = 8;
pub const NODE_OFFSET_NEXT: usize = 12;
pub const NODE_OFFSET_PARENT: usize = 16;
pub const NODE_OFFSET_DATA: usize = 20;
pub const NODE_OFFSET_FLAGS: usize = 24;
/// `NodeSize` is the number of bytes that represents a single node in the encoded format.
pub const NODE_SIZE: usize = 28;

pub const NODE_DATA_TYPE_CHILDREN: u32 = 0 << 30;
pub const NODE_DATA_TYPE_STRING: u32 = 1 << 30;
pub const NODE_DATA_TYPE_EXTENDED_DATA: u32 = 2 << 30;

pub const NODE_DATA_TYPE_MASK: u32 = 0xc0_00_00_00;
pub const NODE_DATA_CHILD_MASK: u32 = 0x00_00_00_ff;
pub const NODE_DATA_STRING_INDEX_MASK: u32 = 0x00_ff_ff_ff;

pub const SYNTAX_KIND_NODE_LIST: u32 = u32::MAX;

pub const HEADER_OFFSET_METADATA: usize = 0;
pub const HEADER_OFFSET_HASH_LO0: usize = 4;
pub const HEADER_OFFSET_HASH_LO1: usize = 8;
pub const HEADER_OFFSET_HASH_HI0: usize = 12;
pub const HEADER_OFFSET_HASH_HI1: usize = 16;
pub const HEADER_OFFSET_PARSE_OPTIONS: usize = 20;
pub const HEADER_OFFSET_STRING_OFFSETS: usize = 24;
pub const HEADER_OFFSET_STRING_DATA: usize = 28;
pub const HEADER_OFFSET_EXTENDED_DATA: usize = 32;
pub const HEADER_OFFSET_STRUCTURED_DATA: usize = 36;
pub const HEADER_OFFSET_NODES: usize = 40;
pub const HEADER_OFFSET_SOURCE_FILE_ID: usize = 44;
pub const HEADER_OFFSET_SOURCE_FILE_LEASE: usize = 52;
pub const HEADER_OFFSET_BINDER_DATA: usize = 60;
pub const HEADER_SIZE: usize = 64;

pub const PROTOCOL_VERSION: u8 = 9;

/// `noStructuredData` — a structured-data offset of 0xFFFFFFFF means "no data".
pub(crate) const NO_STRUCTURED_DATA: u32 = 0xFFFF_FFFF;

/// `SourceFileHash` returns the 128-bit content hash for a source file as a
/// hex string.
pub fn source_file_hash(source_file: &SourceFile) -> String {
    let h = source_file.hash;
    format!("{:016x}{:016x}", h.hi, h.lo)
}

/// `computeSourceHash` — the xxh3-128 hash of file contents stored on
/// `SourceFile.Hash`.
///
/// PORT: not present in the Go package; the port computes the hash here so
/// the encoder mirrors `sourceFile.Hash` exactly (`xxh3.Uint128{Lo, Hi}`
//  byte order is LE 8-byte halves in the header).
pub fn source_hash(text: &[u8]) -> Uint128 {
    let h = xxh3_128(text);
    Uint128 {
        lo: h as u64,
        hi: (h >> 64) as u64,
    }
}

/// `encodeParseOptions` encodes the per-file `ExternalModuleIndicatorOptions`
/// as a uint32 bitmask.
fn encode_parse_options(opts: &ExternalModuleIndicatorOptions) -> u32 {
    let mut bits = 0u32;
    if opts.jsx {
        bits |= 1;
    }
    if opts.force {
        bits |= 2;
    }
    bits
}

/// `NodeIndexTable` maps between AST nodes and their encoder indices for O(1)
/// node handle resolution.
///
/// PORT: `sortedOnce`/`sortedIdx` map to an `Arc<OnceLock>` so the table is
/// `Clone` (required by `get_or_compute_data`) while keeping lazy, shared
/// initialization.
#[derive(Clone)]
pub struct NodeIndexTable {
    /// index → node (`None` for the sentinel and NodeList pseudo-nodes).
    pub nodes: Box<[Option<NodeId>]>,
    /// indices into `nodes`, sorted by `NodeId`; built lazily.
    sorted_idx: Arc<OnceLock<Vec<u32>>>,
}

impl NodeIndexTable {
    fn new(nodes: Vec<Option<NodeId>>) -> NodeIndexTable {
        NodeIndexTable {
            nodes: nodes.into_boxed_slice(),
            sorted_idx: Arc::new(OnceLock::new()),
        }
    }

    /// `t.GetIndex(node)` returns the encoder index for the given node.
    /// On the first call the sortedIdx array is built (O(n log n) sort on a
    /// flat `Vec<u32>`), then subsequent calls use binary search (O(log n)).
    /// Returns 0 (the nil sentinel) when the node is not in the table.
    pub fn get_index(&self, node: NodeId) -> u32 {
        let nodes = &self.nodes;
        let sorted = self.sorted_idx.get_or_init(|| {
            let mut idx: Vec<u32> = Vec::with_capacity(nodes.len());
            for (i, n) in nodes.iter().enumerate() {
                if n.is_some() {
                    idx.push(i as u32);
                }
            }
            idx.sort_unstable_by_key(|&i| nodes[i as usize]);
            idx
        });
        // `NodeId` order is the packed file/index order — Go sorts by
        // `ast.GetNodeId`, which is the same packed value.
        match sorted.binary_search_by_key(&node, |&i| nodes[i as usize].unwrap()) {
            Ok(i) => sorted[i],
            Err(_) => 0,
        }
    }
}

/// `nodeIndexTableKey`
static NODE_INDEX_TABLE_KEY: LazyLock<SourceFileDataKey<NodeIndexTable>> =
    LazyLock::new(new_source_file_data_key);

/// `BuildNodeIndexTable` walks the AST in the same order as `encode_tree` and
/// builds a `NodeIndexTable` without performing the full binary encoding. The
/// indices produced are guaranteed to match those from `encode_source_file`.
pub fn build_node_index_table(nodes: &mut Vec<Node>, source_file: NodeId) -> NodeIndexTable {
    let node_table = RefCell::new(vec![None]);
    let nt = &node_table;

    // Index 1 = root node (matches encode_tree).
    nt.borrow_mut().push(Some(source_file));

    {
        let mut factory = NodeFactory::default();
        let mut cx = VisitorCx::new(nodes, &mut factory);

        let hooks = NodeVisitorHooks {
            visit_nodes: Some(Box::new(
                |cx: &mut VisitorCx<'_, '_>,
                 node_list: Option<NodeList>,
                 v: &NodeVisitor<'_>|
                 -> Option<NodeList> {
                    let Some(node_list) = node_list else {
                        return None;
                    };
                    nt.borrow_mut().push(None); // NodeLists have no NodeId entry
                    v.visit_slice(cx, &node_list.nodes);
                    Some(node_list)
                },
            )),
            visit_modifiers: Some(Box::new(
                |cx: &mut VisitorCx<'_, '_>,
                 modifiers: Option<ModifierList>,
                 v: &NodeVisitor<'_>|
                 -> Option<ModifierList> {
                    if let Some(m) = &modifiers
                        && !m.nodes.is_empty()
                    {
                        nt.borrow_mut().push(None);
                        v.visit_slice(cx, &m.nodes);
                    }
                    modifiers
                },
            )),
            ..Default::default()
        };

        let visit =
            |v: &NodeVisitor<'_>, cx: &mut VisitorCx<'_, '_>, node: NodeId| -> Option<NodeId> {
                nt.borrow_mut().push(Some(node));
                v.visit_each_child(cx, node);
                for j in js_doc(cx.nodes, node, Some(source_file)) {
                    (v.visit.as_ref().unwrap())(v, cx, j);
                }
                Some(node)
            };

        let visitor = NodeVisitor::new(Box::new(visit), hooks);
        visitor.visit_each_child(&mut cx, source_file);
        for j in js_doc(cx.nodes, source_file, Some(source_file)) {
            (visitor.visit.as_ref().unwrap())(&visitor, &mut cx, j);
        }
    }

    NodeIndexTable::new(node_table.into_inner())
}

/// `GetNodeIndexTable` — lazily computes (and caches on the source file) the
/// `NodeIndexTable`.
pub fn get_node_index_table(nodes: &mut Vec<Node>, source_file: NodeId) -> NodeIndexTable {
    get_or_compute_data(nodes, source_file, &NODE_INDEX_TABLE_KEY, |nodes, file| {
        build_node_index_table(nodes, file)
    })
}

/// `EncodeSourceFile` encodes an entire source file AST into the binary
/// format. Returns the encoded bytes and a `NodeIndexTable` mapping encoder
/// indices to AST nodes.
pub fn encode_source_file(nodes: &mut Vec<Node>, source_file: NodeId) -> (Vec<u8>, NodeIndexTable) {
    let (data, node_table) = encode_tree(nodes, source_file, Some(source_file));
    let node_table = get_or_compute_data(nodes, source_file, &NODE_INDEX_TABLE_KEY, move |_, _| {
        node_table
    });
    (data, node_table)
}

/// `SetSourceFileLease` sets the session-scoped lease ID in an encoded source file.
pub fn set_source_file_lease(data: &mut [u8], lease: u64) {
    data[HEADER_OFFSET_SOURCE_FILE_LEASE..HEADER_OFFSET_SOURCE_FILE_LEASE + 8]
        .copy_from_slice(&lease.to_le_bytes());
}

/// `SetSourceFileID` sets the source file node ID used to validate remote references.
pub fn set_source_file_id(data: &mut [u8], id: u64) {
    data[HEADER_OFFSET_SOURCE_FILE_ID..HEADER_OFFSET_SOURCE_FILE_ID + 8]
        .copy_from_slice(&id.to_le_bytes());
}

/// `EncodeNode` encodes an arbitrary AST node and its descendants into the
/// binary format. The `source_file` provides the position map for UTF-16
/// positions; its text is not part of the string data section when the root
/// is not a SourceFile (matching Go, which builds an empty `stringTable`).
pub fn encode_node(
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: Option<NodeId>,
) -> (Vec<u8>, NodeIndexTable) {
    encode_tree(nodes, node, source_file)
}

/// `utf16` — Go `uint32(positionMap.UTF8ToUTF16(pos))`.
///
/// PORT: `PositionMap::utf8_to_utf16` takes `usize`; negative `pos` values
/// (e.g. `undefined()` ranges) pass through Go's binary search unchanged, so
/// the port converts them directly (`-1` → `0xFFFFFFFF`).
fn utf16(position_map: &PositionMap, pos: i32) -> u32 {
    if pos < 0 {
        return pos as u32;
    }
    position_map.utf8_to_utf16(pos as usize) as u32
}

/// The shared mutable encoder state threaded through the visitor closures.
pub(crate) struct EncSt {
    /// The encoded `nodes` section.
    pub(crate) out: Vec<u8>,
    pub(crate) node_count: u32,
    pub(crate) parent_index: u32,
    pub(crate) prev_index: u32,
    /// index → node (`None` = nil sentinel / NodeList pseudo-node).
    pub(crate) node_table: Vec<Option<NodeId>>,
    /// Small map of nodes we need to track indices for (imports +
    /// moduleAugmentations + externalModuleIndicator). Values start at 0 and
    /// are filled in during the walk.
    pub(crate) node_index_map: Option<FxHashMap<NodeId, u32>>,
    pub(crate) strs: StringTable,
    pub(crate) position_map: PositionMap,
    pub(crate) extended_data: Vec<u8>,
    pub(crate) structured_data: Vec<u8>,
    /// Byte offset in `extended_data` where SourceFile fields start.
    pub(crate) sf_extended_data_offset: usize,
}

impl EncSt {
    /// Writes `index` into the `next` field of the record at `prev_index`.
    fn patch_next(&mut self, prev_index: u32, index: u32) {
        let off = prev_index as usize * NODE_SIZE + NODE_OFFSET_NEXT;
        self.out[off..off + 4].copy_from_slice(&index.to_le_bytes());
    }

    /// Writes the node record for `node` (the body of Go's `visitor.Visit`),
    /// returning `(current_index, saved_parent_index)`. The caller performs
    /// the child traversal, then calls `end_node`.
    fn begin_node(&mut self, nodes: &[Node], node: NodeId) -> (u32, u32) {
        self.node_count += 1;
        self.node_table.push(Some(node));
        if self.prev_index != 0 {
            // this is the next sibling of `prev_node`
            self.patch_next(self.prev_index, self.node_count);
        }
        let n = &nodes[node];
        let kind = n.kind as i16 as u32;
        let pos = n.pos();
        let end = n.end();
        let flags = n.flags.0;
        let data = self.get_node_data(nodes, n);
        append_u32s(
            &mut self.out,
            &[
                kind,
                utf16(&self.position_map, pos),
                utf16(&self.position_map, end),
                0,
                self.parent_index,
                data,
                flags,
            ],
        );
        if let Some(map) = &mut self.node_index_map
            && let Some(slot) = map.get_mut(&node)
        {
            *slot = self.node_count;
        }
        let save_parent_index = self.parent_index;
        let current_index = self.node_count;
        self.prev_index = 0;
        self.parent_index = current_index;
        (current_index, save_parent_index)
    }

    fn end_node(&mut self, current_index: u32, save_parent_index: u32) {
        self.prev_index = current_index;
        self.parent_index = save_parent_index;
    }

    /// Writes a NodeList record (the body of Go's `VisitNodes` hook),
    /// returning `(current_index, saved_parent_index)`. The caller then
    /// visits the list elements and calls `end_node`.
    fn begin_node_list(
        &mut self,
        pos: i32,
        end: i32,
        len: usize,
        has_trailing_comma: bool,
    ) -> (u32, u32) {
        self.node_count += 1;
        self.node_table.push(None);
        if self.prev_index != 0 {
            self.patch_next(self.prev_index, self.node_count);
        }
        append_u32s(
            &mut self.out,
            &[
                SYNTAX_KIND_NODE_LIST,
                utf16(&self.position_map, pos),
                utf16(&self.position_map, end),
                0,
                self.parent_index,
                len as u32,
                has_trailing_comma as u32,
            ],
        );
        let save_parent_index = self.parent_index;
        let current_index = self.node_count;
        self.prev_index = 0;
        self.parent_index = current_index;
        (current_index, save_parent_index)
    }

    /// `getNodeData`
    fn get_node_data(&mut self, nodes: &[Node], node: &Node) -> u32 {
        let t = get_node_data_type(node.kind);
        match t {
            NODE_DATA_TYPE_CHILDREN => {
                t | get_node_common_data(node) | get_children_property_mask(node) as u32
            }
            NODE_DATA_TYPE_STRING => {
                t | get_node_common_data(node) | record_node_strings(node, &mut self.strs, nodes)
            }
            NODE_DATA_TYPE_EXTENDED_DATA => {
                t | get_node_common_data(node) | record_extended_data(node, self, nodes)
            }
            _ => panic!("unreachable"),
        }
    }
}

fn encode_tree(
    nodes: &mut Vec<Node>,
    root_node: NodeId,
    source_file: Option<NodeId>,
) -> (Vec<u8>, NodeIndexTable) {
    let root_is_source_file = nodes[root_node].kind == Kind::SourceFile;
    let strs = if root_is_source_file {
        let sf = nodes[root_node].as_source_file();
        StringTable::new(Some(root_node), sf.text_count)
    } else {
        StringTable::new(None, 0)
    };
    let position_map = if let Some(sf) = source_file {
        nodes[sf].as_source_file().position_map().clone()
    } else {
        compute_position_map(b"")
    };
    let initial_node_count = if let Some(sf) = source_file {
        nodes[sf].as_source_file().node_count as usize
    } else {
        0
    };

    let mut st = EncSt {
        out: Vec::with_capacity((initial_node_count + 1) * NODE_SIZE),
        node_count: 0,
        parent_index: 0,
        prev_index: 0,
        node_table: Vec::with_capacity(initial_node_count + 1),
        node_index_map: None,
        strs,
        position_map,
        extended_data: Vec::new(),
        structured_data: Vec::new(),
        sf_extended_data_offset: 0,
    };

    // Build a small map of nodes we need to track indices for (imports +
    // moduleAugmentations + externalModuleIndicator).
    if root_is_source_file {
        let sf = nodes[root_node].as_source_file();
        let mut total = sf.imports().len() + sf.module_augmentations.len();
        let external_module_indicator = sf.external_module_indicator.filter(|&e| e != root_node);
        if external_module_indicator.is_some() {
            total += 1;
        }
        if total > 0 {
            let mut map = FxHashMap::with_capacity_and_hasher(total, Default::default());
            for &imp in sf.imports() {
                map.insert(imp, 0);
            }
            for &aug in sf.module_augmentations.iter() {
                map.insert(aug, 0);
            }
            if let Some(e) = external_module_indicator {
                map.insert(e, 0);
            }
            st.node_index_map = Some(map);
        }
    }

    // Index 0 is a nil sentinel; real nodes start at index 1.
    append_u32s(&mut st.out, &[0; 7]);
    st.node_table.push(None);

    st.node_count += 1;
    st.parent_index = 1;
    st.node_table.push(Some(root_node)); // index 1 = root node

    st.sf_extended_data_offset = st.extended_data.len();
    {
        let root = &nodes[root_node];
        let data = st.get_node_data(nodes, root);
        append_u32s(
            &mut st.out,
            &[
                root.kind as i16 as u32,
                utf16(&st.position_map, root.pos()),
                utf16(&st.position_map, root.end()),
                0,
                0,
                data,
                root.flags.0,
            ],
        );
    }

    let shared = RefCell::new(st);
    let st_ref = &shared;

    let hooks = NodeVisitorHooks {
        visit_nodes: Some(Box::new(
            move |cx: &mut VisitorCx<'_, '_>,
                  node_list: Option<NodeList>,
                  v: &NodeVisitor<'_>|
                  -> Option<NodeList> {
                let Some(node_list) = node_list else {
                    return None;
                };
                let has_trailing = node_list.has_trailing_comma(cx.nodes);
                let (current_index, save_parent_index) = {
                    let mut st = st_ref.borrow_mut();
                    st.begin_node_list(
                        node_list.pos(),
                        node_list.end(),
                        node_list.nodes.len(),
                        has_trailing,
                    )
                };
                v.visit_slice(cx, &node_list.nodes);
                st_ref
                    .borrow_mut()
                    .end_node(current_index, save_parent_index);
                Some(node_list)
            },
        )),
        visit_modifiers: Some(Box::new(
            move |cx: &mut VisitorCx<'_, '_>,
                  modifiers: Option<ModifierList>,
                  v: &NodeVisitor<'_>|
                  -> Option<ModifierList> {
                if let Some(m) = &modifiers
                    && !m.nodes.is_empty()
                {
                    let has_trailing = m.has_trailing_comma(cx.nodes);
                    let (current_index, save_parent_index) = {
                        let mut st = st_ref.borrow_mut();
                        st.begin_node_list(m.pos(), m.end(), m.nodes.len(), has_trailing)
                    };
                    v.visit_slice(cx, &m.nodes);
                    st_ref
                        .borrow_mut()
                        .end_node(current_index, save_parent_index);
                }
                modifiers
            },
        )),
        ..Default::default()
    };

    let visit =
        move |v: &NodeVisitor<'_>, cx: &mut VisitorCx<'_, '_>, node: NodeId| -> Option<NodeId> {
            let (current_index, save_parent_index) = st_ref.borrow_mut().begin_node(cx.nodes, node);
            v.visit_each_child(cx, node);
            if let Some(sf) = source_file {
                for j in js_doc(cx.nodes, node, Some(sf)) {
                    (v.visit.as_ref().unwrap())(v, cx, j);
                }
            }
            st_ref
                .borrow_mut()
                .end_node(current_index, save_parent_index);
            Some(node)
        };

    {
        let mut factory = NodeFactory::default();
        let mut cx = VisitorCx::new(nodes, &mut factory);
        let visitor = NodeVisitor::new(Box::new(visit), hooks);
        visitor.visit_each_child(&mut cx, root_node);
        if let Some(sf) = source_file {
            for j in js_doc(cx.nodes, root_node, Some(sf)) {
                (visitor.visit.as_ref().unwrap())(&visitor, &mut cx, j);
            }
        }
    }

    let mut st = shared.into_inner();

    let mut hash = Uint128::default();
    let mut parse_opts = 0u32;
    if root_is_source_file {
        let sf = nodes[root_node].as_source_file();
        hash = sf.hash;
        parse_opts = encode_parse_options(&sf.parse_options.external_module_indicator_options);

        // Encode imports, moduleAugmentations, and ambientModuleNames into
        // structured data, and patch the placeholder offsets in the
        // SourceFile extended data.
        let imports_offset = encode_node_index_array(
            sf.imports(),
            st.node_index_map.as_ref(),
            &mut st.structured_data,
        );
        let module_augmentations_offset = encode_node_index_array(
            &sf.module_augmentations,
            st.node_index_map.as_ref(),
            &mut st.structured_data,
        );
        let ambient_module_names_offset =
            encode_string_array(&sf.ambient_module_names, &mut st.structured_data);
        // Patch the 3 placeholder uint32s at sfExtendedDataOffset + 32, 36, 40
        st.extended_data[st.sf_extended_data_offset + 32..st.sf_extended_data_offset + 36]
            .copy_from_slice(&imports_offset.to_le_bytes());
        st.extended_data[st.sf_extended_data_offset + 36..st.sf_extended_data_offset + 40]
            .copy_from_slice(&module_augmentations_offset.to_le_bytes());
        st.extended_data[st.sf_extended_data_offset + 40..st.sf_extended_data_offset + 44]
            .copy_from_slice(&ambient_module_names_offset.to_le_bytes());
        // Patch externalModuleIndicator node index at offset 44
        let external_module_indicator_index = match sf.external_module_indicator {
            Some(e) if e == root_node => 1, // root node index
            Some(e) => st
                .node_index_map
                .as_ref()
                .and_then(|m| m.get(&e).copied())
                .unwrap_or(0),
            None => 0,
        };
        st.extended_data[st.sf_extended_data_offset + 44..st.sf_extended_data_offset + 48]
            .copy_from_slice(&external_module_indicator_index.to_le_bytes());
    }

    let metadata = (PROTOCOL_VERSION as u32) << 24;
    let offset_string_table_offsets = HEADER_SIZE;
    let offset_string_table_data = HEADER_SIZE + st.strs.offsets_len() * 4;
    let offset_extended_data = offset_string_table_data + st.strs.string_length(nodes);
    let offset_structured_data = offset_extended_data + st.extended_data.len();
    let offset_nodes = offset_structured_data + st.structured_data.len();

    let mut out = Vec::with_capacity(offset_nodes + st.out.len());
    append_u32s(
        &mut out,
        &[
            metadata,
            hash.lo as u32,
            (hash.lo >> 32) as u32,
            hash.hi as u32,
            (hash.hi >> 32) as u32,
            parse_opts,
            offset_string_table_offsets as u32,
            offset_string_table_data as u32,
            offset_extended_data as u32,
            offset_structured_data as u32,
            offset_nodes as u32,
            0,
            0, // source file ID
            0,
            0, // source file lease ID
            0, // binder data offset
        ],
    );
    out.extend_from_slice(&st.strs.encode(nodes));
    out.extend_from_slice(&st.extended_data);
    out.extend_from_slice(&st.structured_data);
    out.extend_from_slice(&st.out);

    (out, NodeIndexTable::new(st.node_table))
}

fn append_u32s(buf: &mut Vec<u8>, values: &[u32]) {
    for &value in values {
        buf.extend_from_slice(&value.to_le_bytes());
    }
}

/// `hasModifiers` returns true if the modifier list is non-nil and has at
/// least one modifier.
pub(crate) fn has_modifiers(modifiers: Option<&ModifierList>) -> bool {
    modifiers.is_some_and(|m| !m.nodes.is_empty())
}

/// `encodeFileReferences` encodes a slice of `FileReference`s as a msgpack
/// array of tuples into the structured data buffer. Returns the byte offset
/// into the buffer, or `NO_STRUCTURED_DATA` if the slice is empty.
fn encode_file_references(
    refs: &[FileReference],
    position_map: &PositionMap,
    buf: &mut Vec<u8>,
) -> u32 {
    if refs.is_empty() {
        return NO_STRUCTURED_DATA;
    }
    let offset = buf.len() as u32;
    msgpack_write_array_header(buf, refs.len());
    for r in refs {
        // Each entry is a 5-element tuple: [pos, end, fileName, resolutionMode, preserve]
        msgpack_write_array_header(buf, 5);
        msgpack_write_uint(buf, utf16(position_map, r.text_range.pos()));
        msgpack_write_uint(buf, utf16(position_map, r.text_range.end()));
        msgpack_write_string(buf, &r.file_name);
        msgpack_write_uint(buf, r.resolution_mode as u32);
        msgpack_write_bool(buf, r.preserve);
    }
    offset
}

/// `encodeNodeIndexArray`/`encodeModuleAugmentations` — a msgpack array of
/// uint node indices. Returns the byte offset into the buffer, or
/// `NO_STRUCTURED_DATA` if the slice is empty.
fn encode_node_index_array(
    nodes: &[NodeId],
    index_map: Option<&FxHashMap<NodeId, u32>>,
    buf: &mut Vec<u8>,
) -> u32 {
    if nodes.is_empty() {
        return NO_STRUCTURED_DATA;
    }
    let offset = buf.len() as u32;
    msgpack_write_array_header(buf, nodes.len());
    for &node in nodes {
        msgpack_write_uint(
            buf,
            index_map.and_then(|m| m.get(&node).copied()).unwrap_or(0),
        );
    }
    offset
}

/// `encodeStringArray` encodes a slice of strings as a msgpack array of
/// strings. Returns the byte offset into the buffer, or `NO_STRUCTURED_DATA`
/// if the slice is empty.
fn encode_string_array(strs: &[String], buf: &mut Vec<u8>) -> u32 {
    if strs.is_empty() {
        return NO_STRUCTURED_DATA;
    }
    let offset = buf.len() as u32;
    msgpack_write_array_header(buf, strs.len());
    for s in strs {
        msgpack_write_string(buf, s);
    }
    offset
}

/// `encodeSpanMap`
fn encode_span_map(
    m: &SpanMap,
    virtual_positions: &PositionMap,
    original_positions: &PositionMap,
    buf: &mut Vec<u8>,
) -> u32 {
    let segments = SpanMap::segments(Some(m));
    let offset = buf.len() as u32;
    msgpack_write_array_header(buf, segments.len());
    for segment in &segments {
        let tuple_length = if segment.features != Feature::All {
            6
        } else {
            5
        };
        msgpack_write_array_header(buf, tuple_length);
        let virtual_start = virtual_positions.utf8_to_utf16(segment.virtual_start as usize);
        let virtual_end = virtual_positions.utf8_to_utf16(segment.virtual_end as usize);
        let original_start = original_positions.utf8_to_utf16(segment.original_start as usize);
        let original_end = original_positions.utf8_to_utf16(segment.original_end as usize);
        msgpack_write_uint(buf, virtual_start as u32);
        msgpack_write_uint(buf, (virtual_end - virtual_start) as u32);
        msgpack_write_uint(buf, original_start as u32);
        msgpack_write_uint(buf, (original_end - original_start) as u32);
        msgpack_write_uint(buf, segment.kind.0 as u32);
        if tuple_length == 6 {
            msgpack_write_uint(buf, segment.features.0 as u32);
        }
    }
    offset
}

/// `encodeDiagnosticDirectives`
fn encode_diagnostic_directives(
    directives: &[MappedDiagnosticDirective],
    virtual_positions: &PositionMap,
    original_positions: &PositionMap,
    buf: &mut Vec<u8>,
) -> u32 {
    if directives.is_empty() {
        return NO_STRUCTURED_DATA;
    }
    let offset = buf.len() as u32;
    msgpack_write_array_header(buf, directives.len());
    for directive in directives {
        msgpack_write_array_header(buf, 6);
        let original_start =
            original_positions.utf8_to_utf16(directive.original_range.pos() as usize);
        let original_end =
            original_positions.utf8_to_utf16(directive.original_range.end() as usize);
        let virtual_start = virtual_positions.utf8_to_utf16(directive.virtual_range.pos() as usize);
        let virtual_end = virtual_positions.utf8_to_utf16(directive.virtual_range.end() as usize);
        msgpack_write_uint(buf, original_start as u32);
        msgpack_write_uint(buf, (original_end - original_start) as u32);
        msgpack_write_uint(buf, virtual_start as u32);
        msgpack_write_uint(buf, (virtual_end - virtual_start) as u32);
        msgpack_write_uint(buf, directive.policy as u32);
        msgpack_write_uint(buf, directive.unused_code as u32);
    }
    offset
}

// Minimal msgpack writers for the structured data section.

fn msgpack_write_array_header(buf: &mut Vec<u8>, length: usize) {
    if length <= 0x0f {
        buf.push(0x90 | length as u8);
    } else if length <= 0xffff {
        buf.extend_from_slice(&[0xdc, (length >> 8) as u8, length as u8]);
    } else {
        buf.extend_from_slice(&[
            0xdd,
            (length >> 24) as u8,
            (length >> 16) as u8,
            (length >> 8) as u8,
            length as u8,
        ]);
    }
}

fn msgpack_write_uint(buf: &mut Vec<u8>, value: u32) {
    if value <= 0x7f {
        buf.push(value as u8);
    } else if value <= 0xff {
        buf.extend_from_slice(&[0xcc, value as u8]);
    } else if value <= 0xffff {
        buf.extend_from_slice(&[0xcd, (value >> 8) as u8, value as u8]);
    } else {
        buf.extend_from_slice(&[
            0xce,
            (value >> 24) as u8,
            (value >> 16) as u8,
            (value >> 8) as u8,
            value as u8,
        ]);
    }
}

fn msgpack_write_string(buf: &mut Vec<u8>, s: &str) {
    let n = s.len();
    if n <= 0x1f {
        buf.push(0xa0 | n as u8);
    } else if n <= 0xff {
        buf.extend_from_slice(&[0xd9, n as u8]);
    } else if n <= 0xffff {
        buf.extend_from_slice(&[0xda, (n >> 8) as u8, n as u8]);
    } else {
        buf.extend_from_slice(&[
            0xdb,
            (n >> 24) as u8,
            (n >> 16) as u8,
            (n >> 8) as u8,
            n as u8,
        ]);
    }
    buf.extend_from_slice(s.as_bytes());
}

fn msgpack_write_bool(buf: &mut Vec<u8>, value: bool) {
    buf.push(if value { 0xc3 } else { 0xc2 });
}

// Hand-written commonData encoding functions for nodes whose non-bool data
// members cannot be automatically encoded by the generator.

/// `getNodeCommonData_SyntheticExpression`
///
/// SyntheticExpression is an internal compiler node that is never part of a
/// parsed AST. It should never be encoded.
pub(crate) fn get_node_common_data_synthetic_expression(_node: &Node) -> u32 {
    panic!("SyntheticExpression should never be encoded")
}

// Hand-written extended data encoding functions for literal nodes that were
// previously string-type but whose TokenFlags/TemplateFlags cannot fit in 6
// bits.

/// `recordExtendedData_StringLiteral`
pub(crate) fn record_extended_data_string_literal(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let n = &node
        .as_string_literal()
        .literal_expression_base
        .literal_like_node_base;
    let text_index = st
        .strs
        .add(nodes, n.text.as_bytes(), node.kind, node.pos(), node.end());
    append_u32s(&mut st.extended_data, &[text_index, n.token_flags.0]);
}

/// `recordExtendedData_NumericLiteral`
pub(crate) fn record_extended_data_numeric_literal(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let n = &node
        .as_numeric_literal()
        .literal_expression_base
        .literal_like_node_base;
    let text_index = st
        .strs
        .add(nodes, n.text.as_bytes(), node.kind, node.pos(), node.end());
    append_u32s(&mut st.extended_data, &[text_index, n.token_flags.0]);
}

/// `recordExtendedData_BigIntLiteral`
pub(crate) fn record_extended_data_big_int_literal(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let n = &node
        .as_big_int_literal()
        .literal_expression_base
        .literal_like_node_base;
    let text_index = st
        .strs
        .add(nodes, n.text.as_bytes(), node.kind, node.pos(), node.end());
    append_u32s(&mut st.extended_data, &[text_index, n.token_flags.0]);
}

/// `recordExtendedData_RegularExpressionLiteral`
pub(crate) fn record_extended_data_regular_expression_literal(
    node: &Node,
    st: &mut EncSt,
    nodes: &[Node],
) {
    let n = &node
        .as_regular_expression_literal()
        .literal_expression_base
        .literal_like_node_base;
    let text_index = st
        .strs
        .add(nodes, n.text.as_bytes(), node.kind, node.pos(), node.end());
    append_u32s(&mut st.extended_data, &[text_index, n.token_flags.0]);
}

/// `recordExtendedData_NoSubstitutionTemplateLiteral`
pub(crate) fn record_extended_data_no_substitution_template_literal(
    node: &Node,
    st: &mut EncSt,
    nodes: &[Node],
) {
    let n = &node
        .as_no_substitution_template_literal()
        .template_literal_like_node_base;
    let text_index = st.strs.add(
        nodes,
        n.literal_like_node_base.text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    append_u32s(&mut st.extended_data, &[text_index, n.template_flags.0]);
}

/// `recordExtendedData_TemplateHead`
pub(crate) fn record_extended_data_template_head(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let n = &node.as_template_head().template_literal_like_node_base;
    let text_index = st.strs.add(
        nodes,
        n.literal_like_node_base.text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    let raw_text_index = st.strs.add(
        nodes,
        n.raw_text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    append_u32s(
        &mut st.extended_data,
        &[text_index, raw_text_index, n.template_flags.0],
    );
}

/// `recordExtendedData_TemplateMiddle`
pub(crate) fn record_extended_data_template_middle(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let n = &node.as_template_middle().template_literal_like_node_base;
    let text_index = st.strs.add(
        nodes,
        n.literal_like_node_base.text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    let raw_text_index = st.strs.add(
        nodes,
        n.raw_text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    append_u32s(
        &mut st.extended_data,
        &[text_index, raw_text_index, n.template_flags.0],
    );
}

/// `recordExtendedData_TemplateTail`
pub(crate) fn record_extended_data_template_tail(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let n = &node.as_template_tail().template_literal_like_node_base;
    let text_index = st.strs.add(
        nodes,
        n.literal_like_node_base.text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    let raw_text_index = st.strs.add(
        nodes,
        n.raw_text.as_bytes(),
        node.kind,
        node.pos(),
        node.end(),
    );
    append_u32s(
        &mut st.extended_data,
        &[text_index, raw_text_index, n.template_flags.0],
    );
}

/// `recordExtendedData_SourceFile`
pub(crate) fn record_extended_data_source_file(node: &Node, st: &mut EncSt, nodes: &[Node]) {
    let sf = node.as_source_file();
    let text_index = st.strs.add(
        nodes,
        sf.text().as_bytes(),
        Kind::SourceFile,
        node.pos(),
        node.end(),
    );
    let mut original_text_index = text_index;
    if sf.original_text() != sf.text() {
        original_text_index =
            st.strs
                .add(nodes, sf.original_text().as_bytes(), Kind::Unknown, 0, 0);
    }
    let file_name_index = st.strs.add(
        nodes,
        sf.file_name().as_string().as_bytes(),
        Kind::Unknown,
        0,
        0,
    );
    let path_index = st.strs.add(
        nodes,
        sf.path_key().as_string().as_bytes(),
        Kind::Unknown,
        0,
        0,
    );
    let referenced_files_offset = encode_file_references(
        &sf.referenced_files,
        &st.position_map,
        &mut st.structured_data,
    );
    let type_ref_directives_offset = encode_file_references(
        &sf.type_reference_directives,
        &st.position_map,
        &mut st.structured_data,
    );
    let lib_ref_directives_offset = encode_file_references(
        &sf.lib_reference_directives,
        &st.position_map,
        &mut st.structured_data,
    );
    let span_map_offset = match sf.span_map() {
        Some(span_map) => encode_span_map(
            &span_map,
            &st.position_map,
            &compute_position_map(sf.original_text().as_bytes()),
            &mut st.structured_data,
        ),
        None => NO_STRUCTURED_DATA,
    };
    let supplemental_file_names: Vec<String> = sf
        .supplemental_source_files()
        .iter()
        .map(|&file| {
            nodes[file]
                .as_source_file()
                .file_name()
                .as_string()
                .to_string()
        })
        .collect();
    let supplemental_file_names_offset =
        encode_string_array(&supplemental_file_names, &mut st.structured_data);
    let mut canonical_file_name_index = NO_STRUCTURED_DATA;
    if let Some(canonical) = sf.canonical_source_file() {
        canonical_file_name_index = st.strs.add(
            nodes,
            nodes[canonical]
                .as_source_file()
                .file_name()
                .as_string()
                .as_bytes(),
            Kind::Unknown,
            0,
            0,
        );
    }
    let mut content_mapper_index = NO_STRUCTURED_DATA;
    if !sf.content_mapper().is_empty() {
        content_mapper_index =
            st.strs
                .add(nodes, sf.content_mapper().as_bytes(), Kind::Unknown, 0, 0);
    }
    let mut virtual_file_name_index = NO_STRUCTURED_DATA;
    let virtual_file_name = sf.virtual_file_name();
    if !virtual_file_name.as_string().is_empty() {
        virtual_file_name_index = st.strs.add(
            nodes,
            virtual_file_name.as_string().as_bytes(),
            Kind::Unknown,
            0,
            0,
        );
    }
    let diagnostic_directives_offset = encode_diagnostic_directives(
        sf.diagnostic_directives(),
        &st.position_map,
        &compute_position_map(sf.original_text().as_bytes()),
        &mut st.structured_data,
    );
    // imports, moduleAugmentations, ambientModuleNames offsets are
    // placeholders; they will be patched after the tree walk when node
    // indices are known.
    append_u32s(
        &mut st.extended_data,
        &[
            text_index,
            file_name_index,
            path_index,
            sf.language_variant as u32,
            sf.script_kind as u32,
            referenced_files_offset,
            type_ref_directives_offset,
            lib_ref_directives_offset,
            NO_STRUCTURED_DATA,
            NO_STRUCTURED_DATA,
            NO_STRUCTURED_DATA,
            0,
            original_text_index,
            span_map_offset,
            supplemental_file_names_offset,
            canonical_file_name_index,
            content_mapper_index,
            virtual_file_name_index,
            diagnostic_directives_offset,
        ],
    );
}
