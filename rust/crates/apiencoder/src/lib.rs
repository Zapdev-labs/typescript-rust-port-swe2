//! Ported from tsc/internal/api/encoder @ ec47d33c23e464a17cdf2475632cba629bee8763
//!
//! Binary encoder/decoder for TypeScript ASTs used by the VS Code IPC
//! protocol. See `encoder.rs` for the on-disk format description.

mod decoder;
mod decoder_generated;
mod encoder;
mod encoder_generated;
mod stringtable;

#[cfg(test)]
mod decoder_test;
#[cfg(test)]
mod encoder_test;

pub use decoder::{DecodeError, decode_nodes, decode_source_file};
pub use encoder::{
    HEADER_OFFSET_BINDER_DATA, HEADER_OFFSET_EXTENDED_DATA, HEADER_OFFSET_HASH_HI0,
    HEADER_OFFSET_HASH_HI1, HEADER_OFFSET_HASH_LO0, HEADER_OFFSET_HASH_LO1, HEADER_OFFSET_METADATA,
    HEADER_OFFSET_NODES, HEADER_OFFSET_PARSE_OPTIONS, HEADER_OFFSET_SOURCE_FILE_ID,
    HEADER_OFFSET_SOURCE_FILE_LEASE, HEADER_OFFSET_STRING_DATA, HEADER_OFFSET_STRING_OFFSETS,
    HEADER_OFFSET_STRUCTURED_DATA, HEADER_SIZE, NODE_DATA_CHILD_MASK, NODE_DATA_STRING_INDEX_MASK,
    NODE_DATA_TYPE_CHILDREN, NODE_DATA_TYPE_EXTENDED_DATA, NODE_DATA_TYPE_MASK,
    NODE_DATA_TYPE_STRING, NODE_OFFSET_DATA, NODE_OFFSET_END, NODE_OFFSET_FLAGS, NODE_OFFSET_KIND,
    NODE_OFFSET_NEXT, NODE_OFFSET_PARENT, NODE_OFFSET_POS, NODE_SIZE, NodeIndexTable,
    PROTOCOL_VERSION, SYNTAX_KIND_NODE_LIST, build_node_index_table, encode_node,
    encode_source_file, get_node_index_table, set_source_file_id, set_source_file_lease,
    source_file_hash, source_hash,
};
