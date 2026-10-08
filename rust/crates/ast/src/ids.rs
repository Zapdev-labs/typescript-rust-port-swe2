// Strongly-typed arena ids for the AST.
//
// `NodeId` replaces the Go `*ast.Node` pointer. It packs a file index into the
// top 20 bits and a file-local node index into the bottom 44 bits, mirroring
// the layout described in SPEC.md §5.1. A `NodeId` indexes into the
// `Vec<Node>` owned by a `SourceFile`.

use core::fmt;

/// An id identifying a `Node` within a `Vec<Node>`, packed as
/// `file:20 | local:44`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct NodeId(pub u64);

impl NodeId {
    /// The absent value, mirroring Go `nil` `*Node` where a bare `NodeId` is
    /// required (e.g. `Node::parent`). Prefer `Option<NodeId>` elsewhere.
    pub const NONE: NodeId = NodeId(u64::MAX);

    const FILE_SHIFT: u64 = 44;
    const LOCAL_MASK: u64 = (1 << Self::FILE_SHIFT) - 1;
    #[allow(dead_code)]
    const FILE_MASK: u64 = !Self::LOCAL_MASK;

    /// The maximum file index representable in a `NodeId`.
    pub const MAX_FILE_INDEX: u32 = (1 << 20) - 1;

    /// The maximum file-local node index representable in a `NodeId`.
    pub const MAX_LOCAL_INDEX: u64 = Self::LOCAL_MASK;

    /// Builds a `NodeId` from a file index and a file-local index.
    ///
    /// Panics if `file_index` exceeds 20 bits or `local_index` exceeds 44 bits.
    #[inline]
    pub fn new(file_index: u32, local_index: u64) -> NodeId {
        debug_assert!(
            file_index <= Self::MAX_FILE_INDEX,
            "file index out of range"
        );
        debug_assert!(
            local_index <= Self::MAX_LOCAL_INDEX,
            "local node index out of range"
        );
        NodeId(((file_index as u64) << Self::FILE_SHIFT) | local_index)
    }

    /// The file index packed into this id.
    #[inline]
    pub const fn file_index(self) -> u32 {
        (self.0 >> Self::FILE_SHIFT) as u32
    }

    /// The file-local node index packed into this id.
    #[inline]
    pub const fn local_index(self) -> u64 {
        self.0 & Self::LOCAL_MASK
    }

    /// Whether this id is `NodeId::NONE`.
    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    /// Whether this id is not `NodeId::NONE`.
    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }
}

impl Default for NodeId {
    /// Defaults to `NodeId::NONE`, matching Go's zero-value `nil` `*Node`.
    #[inline]
    fn default() -> NodeId {
        NodeId::NONE
    }
}

impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_none() {
            return write!(f, "NodeId::NONE");
        }
        write!(f, "NodeId({}#{})", self.file_index(), self.local_index())
    }
}

/// Indexes into the `Vec<Symbol>` owned by a binder scope table.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const NONE: SymbolId = SymbolId(u32::MAX);

    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }

    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for SymbolId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SymbolId({})", self.0)
    }
}

/// Indexes into a `Vec<FlowNode>` (flow graph nodes are allocated separately
/// from AST nodes, mirroring flow.go's separate FlowNode allocation).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct FlowNodeId(pub u32);

impl FlowNodeId {
    pub const NONE: FlowNodeId = FlowNodeId(u32::MAX);

    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }

    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for FlowNodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FlowNodeId({})", self.0)
    }
}

/// Indexes into a `Vec<FlowList>` (linked list cells of flow antecedents).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct FlowListId(pub u32);

impl FlowListId {
    pub const NONE: FlowListId = FlowListId(u32::MAX);

    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }

    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for FlowListId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FlowListId({})", self.0)
    }
}
