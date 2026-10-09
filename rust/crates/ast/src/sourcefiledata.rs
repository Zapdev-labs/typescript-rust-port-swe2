// Ported from the `SourceFileDataKey` registry in
// tsc/internal/ast/ast.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `SourceFileDataKey[T]` is a typed key identifying lazily-computed data that
// packages outside `ast` attach to a `SourceFile` (e.g. the encoder's node
// index table, the session's symbol index). The `SourceFile.data` field is
// `SourceFileData`, the `map[sourceFileDataKey]any` of per-key once-cells.

use std::any::Any;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_hash::FxHashMap;

use crate::ast::Node;
use crate::ids::NodeId;

/// `type SourceFileDataKey[T any] struct` — a typed key for lazily-computed
/// data attached to a `SourceFile` by another package. Prefer regular
/// `SourceFile` fields for ast-owned data.
///
/// PORT: `PhantomData<fn() -> T>` plays the role of Go's `_ [0]T` — it ties
/// the key to `T` without constraining the key's variance or auto-traits.
pub struct SourceFileDataKey<T> {
    key: u64,
    _phantom: PhantomData<fn() -> T>,
}

/// `sourceFileDataKeyCounter atomic.Uint64` — the counter also mints keys for
/// the nil/zero check below (key 0 is never handed out).
static SOURCE_FILE_DATA_KEY_COUNTER: AtomicU64 = AtomicU64::new(0);

/// `NewSourceFileDataKey[T]()`.
pub fn new_source_file_data_key<T: 'static>() -> SourceFileDataKey<T> {
    SourceFileDataKey {
        // `Add(1)` returns the new value, so the first key is 1.
        key: SOURCE_FILE_DATA_KEY_COUNTER.fetch_add(1, Ordering::Relaxed) + 1,
        _phantom: PhantomData,
    }
}

/// `file.data` — `map[sourceFileDataKey]any` holding one
/// `*sourceFileDataCell[T]` (`once sync.Once` + `value T`) per key.
///
/// PORT: `dataMu` and the cells' `sync.Once` collapse into entry presence —
/// the map is only touched under `&mut Vec<Node>` (exclusive arena access),
/// which replaces Go's mutex. Values are `Send + Sync` so `Vec<Node>` keeps
/// the auto-traits a Go `SourceFile` gets from its mutex-guarded fields.
#[derive(Default)]
pub struct SourceFileData {
    cells: FxHashMap<u64, Box<dyn Any + Send + Sync>>,
}

impl SourceFileData {
    /// The read half of `getDataCell`. A downcast failure means two
    /// `SourceFileDataKey` types collided, which `new_source_file_data_key`
    /// makes impossible — the panic mirrors Go's failing
    /// `cell.(*sourceFileDataCell[T])` assertion.
    pub fn get<T: Send + Sync + 'static>(&self, key: &SourceFileDataKey<T>) -> Option<&T> {
        self.cells.get(&key.key).map(|cell| {
            cell.downcast_ref::<T>()
                .expect("SourceFileData cell type mismatch")
        })
    }

    /// The write half of `getDataCell` — stores the computed cell value.
    pub fn insert<T: Send + Sync + 'static>(&mut self, key: &SourceFileDataKey<T>, value: T) {
        self.cells.insert(key.key, Box::new(value));
    }

    /// Mutable access to a stored cell — used by `bind_result_mut` so the
    /// checker can append synthetic `FlowNode`s (Go heap-allocates
    /// `&ast.FlowNode{}` freely).
    pub fn get_mut<T: Send + Sync + 'static>(
        &mut self,
        key: &SourceFileDataKey<T>,
    ) -> Option<&mut T> {
        self.cells.get_mut(&key.key).map(|cell| {
            cell.downcast_mut::<T>()
                .expect("SourceFileData cell type mismatch")
        })
    }
}

/// `(file *SourceFile) GetOrComputeData(key, compute)` — returns the cached
/// value for `key`, computing and storing it on first use.
///
/// PORT: `compute` takes `(nodes, file)` — the arena plus the file's `NodeId`
/// — instead of `*SourceFile`; a `&SourceFile` alone cannot resolve its
/// children out of the arena. The value is returned by (cloned) value like
/// Go's `cell.value`. Reentering `get_or_compute_data` for the *same* key
/// from `compute` recurses where Go would deadlock on `sync.Once`.
pub fn get_or_compute_data<T, F>(
    nodes: &mut Vec<Node>,
    file: NodeId,
    key: &SourceFileDataKey<T>,
    compute: F,
) -> T
where
    T: Clone + Send + Sync + 'static,
    F: FnOnce(&mut Vec<Node>, NodeId) -> T,
{
    // Go also panics on a nil key — impossible for a Rust `&` receiver.
    if key.key == 0 {
        panic!("invalid SourceFileDataKey; use new_source_file_data_key");
    }
    if let Some(value) = nodes[file].as_source_file().data.get(key) {
        return value.clone();
    }
    let value = compute(nodes, file);
    nodes[file]
        .as_source_file_mut()
        .data
        .insert(key, value.clone());
    value
}
