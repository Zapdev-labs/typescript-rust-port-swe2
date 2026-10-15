// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go's `*ast.Symbol` is a stable heap pointer; in this port symbols are
//   `(SymbolArena, SymbolId)` pairs in program-global chunked arenas.
//   `SymbolPtr` recovers the pointer, so a client `SymbolID` is the
//   symbol's arena address — the same process-unique, pointer-stable
//   handle Go's `ast.GetSymbolId` produces (and the key
//   `getSourceFileSymbolIndex` shares). Types and signatures keep their
//   per-checker sequential ids (`Type::id`/`Signature::id`) because the
//   registries are per-project and a project's API queries all run on the
//   `CheckerLifetimeAPI` checker — same as Go.
// - `snapshotData` registries store `(arena, id)` entries rather than
//   pointers; arena clones keep elements alive while the snapshotData is
//   retained, mirroring Go's GC keepalive via the snapshot's programs.
// - `Session` is `unsafe impl Send + Sync`: arena handles (`SymbolArena`,
//   `TypeArena`, `SignatureArena`, `Rc<NodeArenaBuf>`) are `!Send`,
//   matching Go's goroutine-shared session under the same lock regime
//   (`tsc_project::session::Session`'s `SendShared` sets the precedent).
// - `refCount` bookkeeping stays on `snapshotData`; `releaseSnapshot`
//   derefs the `project::snapshot::Snapshot` only after the data leaves the map.

use std::cell::Cell;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, RwLock};

use rustc_hash::FxHashMap;
use tsc_apiencoder as encoder;
use tsc_ast as ast;
use tsc_astnav as astnav;
use tsc_checker::exports as checker_exports;
use tsc_checker::types as checker;
use tsc_checker::checker_core::Checker;
use tsc_collections as collections;
use tsc_compiler as compiler;
use tsc_core as core_;
use tsc_execute::build;
use tsc_ipc as ipc;
use tsc_json as json;
use tsc_ls as ls;
use tsc_lsproto as lsproto;
use tsc_module as module;
use tsc_pprof as pprof;
use tsc_project as project;
use tsc_tspath as tspath;
use tsc_vfs as vfs;

use crate::proto::*;

/// `sessionIDCounter`.
static SESSION_ID_COUNTER: AtomicU64 = AtomicU64::new(0);

/// `sourceFileSymbolIndexKey` — lazily computed per-file map from the
/// API `SymbolID` (symbol pointer address) to the file's `SymbolId`s.
/// Go caches `map[SymbolID]*ast.Symbol` on the `*ast.SourceFile`; the
/// value type changes but the lifetime is identical.
static SOURCE_FILE_SYMBOL_INDEX_KEY: LazyLock<
    ast::SourceFileDataKey<FxHashMap<u64, ast::SymbolId>>,
> = LazyLock::new(ast::new_source_file_data_key);

/// `SymbolHandle` — the client-facing `SymbolID` for a symbol.
///
/// Go returns `SymbolID(ast.GetSymbolId(symbol))`: a process-unique id
/// assigned per `*ast.Symbol` pointer. Arena-resident `Symbol`s have a
/// stable heap address via `SymbolPtr`, so the address serves the same
/// purpose — unique for the arena's lifetime (which a retained snapshot
/// or source-file lease covers).
pub(crate) fn symbol_handle(symbol: ast::SymbolPtr) -> SymbolId {
    &*symbol as *const ast::Symbol as usize as u64
}

/// `TypeHandle` — `TypeID(t.Id())`; the checker's own sequential id.
pub(crate) fn type_handle(t: &checker::Type) -> TypeId {
    t.id().0
}

/// `SignatureHandle` — `SignatureID(sig.Id())`.
pub(crate) fn signature_handle(sig: &checker::Signature) -> SignatureId {
    sig.id().0 as u64
}

/// `typeHandles` — `[]TypeID` of a `[]*checker.Type` slice.
pub(crate) fn type_handles(
    arena: &checker::TypeArena,
    types: &[checker::TypeId],
) -> Vec<TypeId> {
    types.iter().map(|&t| type_handle(arena.get_ref(t))).collect()
}

/// A registry entry standing in for Go's `*ast.Symbol`: the binding
/// arena plus the `SymbolId` that indexes it.
#[derive(Clone)]
pub(crate) struct SymbolEntry {
    pub arena: ast::SymbolArena,
    pub symbol: ast::SymbolId,
}

impl SymbolEntry {
    pub fn ptr(&self) -> ast::SymbolPtr {
        self.arena.get(self.symbol)
    }

    pub fn handle(&self) -> SymbolId {
        symbol_handle(self.ptr())
    }
}

/// A registry entry standing in for Go's `*checker.Type`.
#[derive(Clone)]
pub(crate) struct TypeEntry {
    pub arena: checker::TypeArena,
    pub ty: checker::TypeId,
}

impl TypeEntry {
    pub fn ptr(&self) -> checker::TypePtr {
        self.arena.get(self.ty)
    }
}

/// A registry entry standing in for Go's `*checker.Signature`.
#[derive(Clone)]
pub(crate) struct SignatureEntry {
    pub arena: checker::SignatureArena,
    pub signature: checker::SignatureId,
}

impl SignatureEntry {
    pub fn get(&self) -> &checker::Signature {
        self.arena.get(self.signature)
    }
}

/// `ast.GetSourceFileOfSymbol` — walks `symbol.Declarations[0]` (with the
/// implicit-prototype fallback) to its `SourceFile` ancestor.
///
/// PORT: lives here because `ast` has no direct port of the helper yet.
/// Returns `None` for transient symbols and symbols with no declaration.
pub(crate) fn get_source_file_of_symbol(
    nodes: &[ast::Node],
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> Option<ast::NodeId> {
    let mut sym = symbol;
    {
        let s = arena.get_ref(sym);
        if s.flags.intersects(ast::SymbolFlags::TRANSIENT) {
            return None;
        }
        if s.declarations.is_empty() {
            // A class's implicit prototype has no declaration of its own.
            sym = s.parent?;
        }
    }
    let declaration = arena.get_ref(sym).declarations.first().copied()?;
    ast::get_source_file_of_node(Some(declaration), nodes)
}

/// `symbolOwnerFile` returns the source file that owns a symbol's client
/// identity, or `None` when the symbol is owned by its snapshot.
/// Content-mapped outputs live in a cache that cannot yet be addressed by
/// file key, so their binder symbols remain snapshot-owned.
///
/// PORT: returns the file `NodeId`; the caller supplies the node arena.
pub(crate) fn symbol_owner_file(
    nodes: &[ast::Node],
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> Option<ast::NodeId> {
    if arena.get_ref(symbol).flags.intersects(ast::SymbolFlags::TRANSIENT) {
        return None;
    }
    let file = get_source_file_of_symbol(nodes, arena, symbol)?;
    if nodes[file].as_source_file().is_content_mapped() {
        return None;
    }
    Some(file)
}

/// `getSourceFileSymbolIndex` — index of a file's symbols by API handle.
///
/// Go builds the index once per `*ast.SourceFile` because symbol ids are
/// process-global. Here `SymbolId`s are arena-scoped, so the caller
/// passes the arena that bound this node arena's file (a program's
/// `SymbolArena`); the index maps each symbol's pointer address — the
/// API `SymbolID` — back to its arena id. The cached index is keyed on
/// the `(nodes, file)` pair, which only ever binds under one arena.
pub(crate) fn get_source_file_symbol_index(
    arena: &ast::SymbolArena,
    nodes: &mut Vec<ast::Node>,
    file: ast::NodeId,
) -> FxHashMap<u64, ast::SymbolId> {
    ast::get_or_compute_data(nodes, file, &SOURCE_FILE_SYMBOL_INDEX_KEY, |nodes, file| {
        let mut index = FxHashMap::with_capacity_and_hasher(
            nodes[file].as_source_file().symbol_count as usize,
            Default::default(),
        );
        fn add_symbol(
            index: &mut FxHashMap<u64, ast::SymbolId>,
            arena: &ast::SymbolArena,
            nodes: &Vec<ast::Node>,
            file: ast::NodeId,
            symbol: ast::SymbolId,
        ) {
            if symbol.is_none() {
                return;
            }
            let s = arena.get(symbol);
            if s.flags.intersects(ast::SymbolFlags::TRANSIENT) {
                return;
            }
            debug_assert_eq!(get_source_file_of_symbol(nodes, arena, symbol), Some(file));
            let id = symbol_handle(s);
            if index.insert(id, symbol).is_some() {
                debug_assert!(index[&id] == symbol);
            }
            if let Some(parent) = s.parent {
                add_symbol(index, arena, nodes, file, parent);
            }
            if let Some(export) = s.export_symbol {
                add_symbol(index, arena, nodes, file, export);
            }
            for child in s.members.values().chain(s.exports.values()) {
                add_symbol(index, arena, nodes, file, *child);
            }
        }
        let table = encoder::get_node_index_table(nodes, file);
        for node in table.nodes.iter().flatten() {
            let n = &nodes[*node];
            for symbol in n
                .symbol()
                .into_iter()
                .chain(n.local_symbol())
                .chain(n.locals().iter().flat_map(|t| t.values().copied()))
            {
                add_symbol(&mut index, arena, nodes, file, symbol);
            }
        }
        for symbol in nodes[file]
            .as_source_file()
            .global_exports
            .values()
        {
            add_symbol(&mut index, arena, nodes, file, *symbol);
        }
        for module in nodes[file]
            .as_source_file()
            .pattern_ambient_modules
            .iter()
        {
            if let Some(symbol) = module.symbol {
                add_symbol(&mut index, arena, nodes, file, symbol);
            }
        }
        index
    })
}

/// `nodeHandleFrom` — `"index.kind.pathKey"` for a node.
///
/// PORT: `file` — the node's `SourceFile` — is explicit because the
/// `NodeIndexTable` is computed per `(nodes, file)` pair.
pub(crate) fn node_handle_from(
    nodes: &mut Vec<ast::Node>,
    file: ast::NodeId,
    node: ast::NodeId,
) -> NodeHandle {
    let table = encoder::get_node_index_table(nodes, file);
    let idx = table.get_index(node);
    NodeHandle(std::borrow::Cow::Owned(format!(
        "{}.{}.{}",
        idx,
        nodes[node].kind as u32,
        nodes[file].as_source_file().path_key().as_string()
    )))
}

/// `symbolNodeHandleFrom` — `nodeHandleFrom` with Go's owner assertion.
pub(crate) fn symbol_node_handle_from(
    nodes: &mut Vec<ast::Node>,
    node: ast::NodeId,
    owner: Option<ast::NodeId>,
) -> NodeHandle {
    let file = ast::get_source_file_of_node(Some(node), nodes).expect("node has no source file");
    if owner.is_some() {
        debug_assert_eq!(file, owner.unwrap());
    }
    node_handle_from(nodes, file, node)
}

/// `newSourceFileDescriptor`.
pub(crate) fn new_source_file_descriptor(
    nodes: &[ast::Node],
    file: ast::NodeId,
) -> SourceFileDescriptor {
    let source_file = nodes[file].as_source_file();
    let parse_options = source_file.parse_options();
    let mut parse_options_key = 0u32;
    if parse_options.external_module_indicator_options.jsx {
        parse_options_key |= 1;
    }
    if parse_options.external_module_indicator_options.force {
        parse_options_key |= 2;
    }
    SourceFileDescriptor {
        file_name: parse_options.file_name.clone(),
        path: parse_options.path_key.clone(),
        content_hash: encoder::source_file_hash(source_file),
        parse_options_key: parse_options_key.to_string(),
        script_kind: source_file.script_kind,
        node_id: source_file_node_id(file).to_string(),
    }
}

/// `sourceFileNodeID` is stable for one AST and changes when an equal
/// parse-cache key is recreated, making it suitable for validating remote
/// references without introducing another source-file identity or
/// ownership registry.
///
/// PORT: `ast.GetNodeId(node)` — `NodeId`'s packed file:20|local:44 value
/// serves the same purpose.
pub(crate) fn source_file_node_id(file: ast::NodeId) -> u64 {
    file.0
}

/// `isValidCreateSourceFileScriptKind`.
pub(crate) fn is_valid_create_source_file_script_kind(
    script_kind: core_::scriptkind::ScriptKind,
) -> bool {
    matches!(
        script_kind,
        core_::scriptkind::ScriptKind::Js
            | core_::scriptkind::ScriptKind::Jsx
            | core_::scriptkind::ScriptKind::Ts
            | core_::scriptkind::ScriptKind::Tsx
            | core_::scriptkind::ScriptKind::Json
    )
}

/// A session-side bound clone of a leased parse-cache file — the Rust
/// equivalent of Go's eagerly-bound cached `*ast.SourceFile`.
pub(crate) struct BoundSourceFile {
    /// The clone's node arena — distinct from the shared cache arena so
    /// binding a lease never marks the canonical copy bound.
    pub nodes: Rc<ast::NodeArenaBuf>,
    /// `file` indexes `nodes`.
    pub file: ast::NodeId,
    /// The arena the clone was bound into; `SymbolId`s in `nodes` index
    /// this arena.
    pub symbols: ast::SymbolArena,
    /// `getSourceFileSymbolIndex` for the bound clone.
    pub symbol_index: FxHashMap<u64, ast::SymbolId>,
}

impl SourceFileDescriptor {
    /// `(d SourceFileDescriptor) parseCacheKey`.
    pub(crate) fn parse_cache_key(&self) -> Result<project::parsecache::ParseCacheKey, String> {
        if self.content_hash.len() != 32 {
            return Err("content hash must contain 32 hexadecimal digits".to_string());
        }
        let hi = u64::from_str_radix(&self.content_hash[..16], 16)
            .map_err(|e| format!("invalid content hash: {e}"))?;
        let lo = u64::from_str_radix(&self.content_hash[16..], 16)
            .map_err(|e| format!("invalid content hash: {e}"))?;
        let parse_options_key: u64 = self
            .parse_options_key
            .parse()
            .map_err(|_| format!("invalid parse options key {:?}", self.parse_options_key))?;
        if parse_options_key & !3 != 0 || parse_options_key > u32::MAX as u64 {
            return Err(format!(
                "invalid parse options key {:?}",
                self.parse_options_key
            ));
        }
        if !is_valid_create_source_file_script_kind(self.script_kind) {
            return Err(format!("invalid script kind {}", self.script_kind as i32));
        }
        Ok(project::parsecache::new_parse_cache_key(
            ast::parseoptions::SourceFileParseOptions {
                file_name: self.file_name.clone(),
                path_key: self.path.clone(),
                external_module_indicator_options:
                    ast::parseoptions::ExternalModuleIndicatorOptions {
                        jsx: parse_options_key & 1 != 0,
                        force: parse_options_key & 2 != 0,
                    },
            },
            ast::Uint128 { hi, lo },
            self.script_kind,
        ))
    }
}

/// `resolveNodeHandle` — parses `index.kind.pathKey` and resolves the
/// node in the program. `kind` is informational only.
pub(crate) fn resolve_node_handle(
    program: &compiler::program::Program,
    handle: &NodeHandle,
) -> Result<ast::NodeId, String> {
    let s = handle.as_str();
    // Format: "index.kind.path" — we need index and path, kind is
    // informational only.
    let Some(first_dot) = s.find('.') else {
        return Err(format!(
            "{}: invalid node handle {:?}",
            ERR_CLIENT_ERROR,
            s
        ));
    };
    let Some(second_dot) = s[first_dot + 1..].find('.') else {
        return Err(format!(
            "{}: invalid node handle {:?}",
            ERR_CLIENT_ERROR,
            s
        ));
    };
    let second_dot = second_dot + first_dot + 1; // absolute index

    let idx: usize = s[..first_dot].parse().map_err(|e| {
        format!(
            "{}: invalid node handle {:?}: {}",
            ERR_CLIENT_ERROR,
            s,
            e
        )
    })?;
    let Some(path) = tspath::try_path_key_from_canonical(&s[second_dot + 1..]) else {
        return Err(format!(
            "{}: invalid node handle {:?}",
            ERR_CLIENT_ERROR,
            s
        ));
    };

    let Some(file) = program.get_source_file_by_path(&path) else {
        return Err(format!(
            "{}: node handle {:?} could not be resolved (file may not be loaded or handle may be stale)",
            ERR_CLIENT_ERROR,
            s
        ));
    };
    let nodes = program.arena_of(file);
    let table = encoder::get_node_index_table(nodes.get_mut(), file);

    if idx < table.nodes.len() {
        if let Some(node) = table.nodes[idx] {
            return Ok(node);
        }
    }
    Err(format!(
        "{}: node handle {:?} could not be resolved (file may not be loaded or handle may be stale)",
        ERR_CLIENT_ERROR,
        s
    ))
}

/// `snapshotData` holds the per-snapshot state including the snapshot
/// itself and symbol/type registries scoped to this snapshot. Multiple
/// clients may hold references to the same snapshot via ref counting; the
/// registries are cleaned up when refCount reaches zero.
pub(crate) struct SnapshotData {
    pub handle: SnapshotId,
    pub snapshot: Arc<project::snapshot::Snapshot>,
    pub file_system: Arc<dyn vfs::Vfs>,
    pub ref_count: Cell<i32>,

    pub open_projects: collections::Set<tspath::PathKey>,
    pub open_files: collections::Set<tspath::PathKey>,

    /// `symbolRegistry`/`symbolCanonicalProjects` — one `RwLock` each,
    /// mirroring `symbolRegistryMu`.
    symbol_registry: RwLock<FxHashMap<u64, SymbolEntry>>,
    symbol_canonical_projects: RwLock<FxHashMap<u64, project::project::Id>>,

    project_registries: RwLock<FxHashMap<project::project::Id, Rc<ProjectRegistryData>>>,
}

/// `projectRegistryData` holds per-project type and signature registries.
/// Types and signatures use per-checker sequential IDs, so the same local
/// ID can appear in multiple projects. Separate maps per project prevent
/// collisions and allow clean teardown when a project is removed.
#[derive(Default)]
pub(crate) struct ProjectRegistryData {
    pub types: RwLock<FxHashMap<u32, TypeEntry>>,
    pub signatures: RwLock<FxHashMap<u64, SignatureEntry>>,
}

impl SnapshotData {
    fn new(
        handle: SnapshotId,
        snapshot: Arc<project::snapshot::Snapshot>,
        file_system: Arc<dyn vfs::Vfs>,
    ) -> SnapshotData {
        SnapshotData {
            handle,
            snapshot,
            file_system,
            ref_count: Cell::new(1),
            open_projects: Default::default(),
            open_files: Default::default(),
            symbol_registry: Default::default(),
            symbol_canonical_projects: Default::default(),
            project_registries: Default::default(),
        }
    }

    /// `(sd *snapshotData) getProgram`.
    pub fn get_program(
        &self,
        project_handle: &project::project::Id,
    ) -> Result<Rc<compiler::program::Program>, String> {
        let proj = self.get_project(project_handle)?;
        match proj.get_program().cloned() {
            Some(p) => Ok(p),
            None => Err(format!("{}: project has no program", ERR_CLIENT_ERROR)),
        }
    }

    /// `(sd *snapshotData) getProject`.
    pub fn get_project(
        &self,
        project_handle: &project::project::Id,
    ) -> Result<Rc<project::project::Project>, String> {
        match self.snapshot.project_collection.get_project(project_handle) {
            Some(p) => Ok(p.clone()),
            None => Err(format!(
                "{}: project {} not found",
                ERR_CLIENT_ERROR,
                project_handle
            )),
        }
    }

    /// `(sd *snapshotData) nodeHandleFrom`.
    pub fn node_handle_from(
        &self,
        nodes: &mut Vec<ast::Node>,
        file: ast::NodeId,
        node: ast::NodeId,
    ) -> NodeHandle {
        node_handle_from(nodes, file, node)
    }

    /// `(sd *snapshotData) getOrCreateProjectRegistry`.
    pub fn get_or_create_project_registry(
        &self,
        project_id: &project::project::Id,
    ) -> Rc<ProjectRegistryData> {
        assert!(
            !project_id.0.is_empty(),
            "getOrCreateProjectRegistry: empty project ID"
        );
        // Fast path: registry already exists — read lock only.
        if let Some(reg) = self.project_registries.read().unwrap().get(project_id) {
            return reg.clone();
        }
        // Slow path: create under write lock.
        self.project_registries
            .write()
            .unwrap()
            .entry(project_id.clone())
            .or_insert_with(|| Rc::new(ProjectRegistryData::default()))
            .clone()
    }

    /// `newSymbolResponse` classifies a symbol's ownership before exposing
    /// its identity to a client. Only snapshot-owned symbols are
    /// registered in the snapshot; file-owned symbols are resolved
    /// through their source file.
    ///
    /// PORT: the caller passes the node arena containing the symbol's
    /// owning file (`symbolOwnerFile` must inspect it).
    pub fn new_symbol_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        arena: &ast::SymbolArena,
        symbol: ast::SymbolId,
        canonical_project: &project::project::Id,
    ) -> Option<SymbolResponse> {
        if symbol.is_none() {
            return None;
        }
        if symbol_owner_file(nodes, arena, symbol).is_some() {
            return Some(new_file_symbol_response(nodes, arena, symbol));
        }
        let (id, project) = self.register_symbol(arena, symbol, canonical_project);
        let reference = SymbolReference {
            owner: SymbolOwner {
                kind: SYMBOL_OWNER_KIND_SNAPSHOT,
                file: None,
                snapshot: self.handle,
                project: project.clone(),
            },
            id,
        };
        Some(build_symbol_response(nodes, arena, symbol, reference, None))
    }

    /// `(sd *snapshotData) registerSymbol` — registers a symbol in the
    /// snapshot's registry and returns its handle along with its
    /// canonical project (first writer wins; always non-empty so
    /// project-scoped follow-up lookups have a default context).
    pub fn register_symbol(
        &self,
        arena: &ast::SymbolArena,
        symbol: ast::SymbolId,
        canonical_project: &project::project::Id,
    ) -> (SymbolId, project::project::Id) {
        if symbol.is_none() {
            return (0, project::project::Id(String::new()));
        }
        assert!(
            !canonical_project.0.is_empty(),
            "registerSymbol requires a non-empty canonical project"
        );
        let entry = SymbolEntry {
            arena: arena.clone(),
            symbol,
        };
        let id = entry.handle();
        {
            let mut registry = self.symbol_registry.write().unwrap();
            if let Some(existing) = registry.get(&id) {
                if !ast::SymbolPtr::ptr_eq(existing.ptr(), entry.ptr()) {
                    panic!("duplicate symbol");
                }
            } else {
                registry.insert(id, entry);
            }
        }
        let project = self
            .symbol_canonical_projects
            .write()
            .unwrap()
            .entry(id)
            .or_insert_with(|| canonical_project.clone())
            .clone();
        (id, project)
    }

    /// `(sd *snapshotData) newTypeResponse` — registers the type and
    /// returns the response.
    ///
    /// PORT: `c` is `&mut` because Go's `mapped.ResolveComponents(c, t)`
    /// mutates the checker (memoized component types).
    pub fn new_type_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        c: &mut Checker,
        project_id: &project::project::Id,
        ty: checker::TypeId,
    ) -> Option<TypeResponse> {
        if ty.is_none() {
            return None;
        }
        let mut resp = crate::proto::new_type_response(
            &c.types,
            ty,
            self.register_type(&c.types, project_id, ty),
        );
        {
            let t = c.types.get(ty);
            if let Some(sym) = t.symbol {
                resp.symbol = new_symbol_reference(nodes, &c.symbol_arena, sym);
            }
            if let Some(alias) = &t.alias {
                resp.alias_symbol = alias
                    .symbol
                    .and_then(|s| new_symbol_reference(nodes, &c.symbol_arena, s));
            }
        }
        if c.types.get(ty).object_flags.intersects(checker::ObjectFlags::MAPPED) {
            // `mapped.ResolveComponents(c, t)` — memoizes into the arena.
            c.resolve_mapped_type_components(ty);
            let t = c.types.get(ty);
            let mapped = t.as_mapped_type();
            for (slot, value) in [
                (&mut resp.type_parameter, mapped.type_parameter()),
                (&mut resp.constraint_type, mapped.constraint_type()),
                (&mut resp.name_type, mapped.name_type()),
                (&mut resp.template_type, mapped.template_type()),
            ] {
                *slot = match value {
                    Some(v) => self.register_type(&c.types, project_id, v),
                    None => 0,
                };
            }
        }
        if checker_exports::is_tuple_type_target(&c.types, ty) {
            let t = c.types.get(ty);
            let element_infos = t.as_tuple_type().element_infos();
            for (i, info) in element_infos.iter().enumerate() {
                if let Some(declaration) = info.labeled_declaration() {
                    if resp.labeled_element_declarations.is_empty() {
                        resp.labeled_element_declarations =
                            vec![NodeHandle::default(); element_infos.len()];
                    }
                    resp.labeled_element_declarations[i] = self.node_handle_from(
                        nodes,
                        ast::get_source_file_of_node(Some(declaration), nodes).unwrap(),
                        declaration,
                    );
                }
            }
        }
        Some(resp)
    }

    /// `(sd *snapshotData) registerType`.
    pub fn register_type(
        &self,
        arena: &checker::TypeArena,
        project_id: &project::project::Id,
        ty: checker::TypeId,
    ) -> TypeId {
        if ty.is_none() {
            return 0;
        }
        let entry = TypeEntry {
            arena: arena.clone(),
            ty,
        };
        let id = type_handle(arena.get_ref(ty));
        let reg = self.get_or_create_project_registry(project_id);
        let mut registry = reg.types.write().unwrap();
        if let Some(existing) = registry.get(&id) {
            if !checker::TypePtr::ptr_eq(existing.ptr(), entry.ptr()) {
                panic!("duplicate type");
            }
            return id;
        }
        registry.insert(id, entry);
        id
    }

    /// `(sd *snapshotData) newSignatureResponse` — registers the
    /// signature in the project's registry and returns the response.
    pub fn new_signature_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        c: &Checker,
        project_id: &project::project::Id,
        signature: checker::SignatureId,
    ) -> Option<SignatureResponse> {
        if signature.is_none() {
            return None;
        }
        let sig = c.signature_arena.get(signature);
        let mut resp = SignatureResponse {
            id: self.register_signature(&c.signature_arena, project_id, signature),
            flags: sig.flags().0,
            ..Default::default()
        };
        if let Some(declaration) = sig.declaration() {
            resp.declaration = self.node_handle_from(
                nodes,
                ast::get_source_file_of_node(Some(declaration), nodes).unwrap(),
                declaration,
            );
        }
        if !sig.type_parameters().is_empty() {
            resp.type_parameters = type_handles(&c.types, sig.type_parameters());
        }
        if !sig.parameters().is_empty() {
            resp.parameters = sig
                .parameters()
                .iter()
                .map(|&p| {
                    new_symbol_reference(nodes, &c.symbol_arena, p).unwrap_or_default()
                })
                .collect();
        }
        if let Some(this) = sig.this_parameter() {
            resp.this_parameter = new_symbol_reference(nodes, &c.symbol_arena, this);
        }
        if let Some(target) = sig.target() {
            resp.target = signature_handle(c.signature_arena.get(target));
        }
        Some(resp)
    }

    /// `(sd *snapshotData) registerSignature`.
    pub fn register_signature(
        &self,
        arena: &checker::SignatureArena,
        project_id: &project::project::Id,
        signature: checker::SignatureId,
    ) -> SignatureId {
        if signature.is_none() {
            return 0;
        }
        let id = signature_handle(arena.get(signature));
        let reg = self.get_or_create_project_registry(project_id);
        let mut registry = reg.signatures.write().unwrap();
        if let Some(existing) = registry.get(&id) {
            if existing.signature != signature {
                panic!("duplicate signature");
            }
            return id;
        }
        registry.insert(
            id,
            SignatureEntry {
                arena: arena.clone(),
                signature,
            },
        );
        id
    }

    /// `(sd *snapshotData) resolveSymbolHandle` — resolves a
    /// snapshot-owned symbol handle within the snapshot's registry.
    pub fn resolve_symbol_handle(&self, handle: SymbolId) -> Result<SymbolEntry, String> {
        if handle == 0 {
            return Err(format!("{}: empty symbol handle", ERR_CLIENT_ERROR));
        }
        match self.symbol_registry.read().unwrap().get(&handle) {
            Some(entry) => Ok(entry.clone()),
            None => Err(format!(
                "{}: symbol handle {} not found in snapshot registry",
                ERR_CLIENT_ERROR,
                handle
            )),
        }
    }

    /// `(sd *snapshotData) resolveTypeHandle` — resolves a type handle
    /// within the project's registry.
    pub fn resolve_type_handle(
        &self,
        project_id: &project::project::Id,
        handle: TypeId,
    ) -> Result<TypeEntry, String> {
        if handle == 0 {
            return Err(format!("{}: empty type handle", ERR_CLIENT_ERROR));
        }
        if project_id.0.is_empty() {
            return Err(format!(
                "{}: empty project ID for type handle {}",
                ERR_CLIENT_ERROR,
                handle
            ));
        }
        let reg = self.project_registries.read().unwrap().get(project_id).cloned();
        let Some(reg) = reg else {
            return Err(format!(
                "{}: type handle {} not found (no registry for project {})",
                ERR_CLIENT_ERROR,
                handle,
                project_id
            ));
        };
        match reg.types.read().unwrap().get(&handle) {
            Some(entry) => Ok(entry.clone()),
            None => Err(format!(
                "{}: type handle {} not found in project registry",
                ERR_CLIENT_ERROR,
                handle
            )),
        }
    }

    /// `(sd *snapshotData) resolveSignatureHandle` — resolves a signature
    /// handle within the project's registry.
    pub fn resolve_signature_handle(
        &self,
        project_id: &project::project::Id,
        handle: SignatureId,
    ) -> Result<SignatureEntry, String> {
        if handle == 0 {
            return Err(format!("{}: empty signature handle", ERR_CLIENT_ERROR));
        }
        if project_id.0.is_empty() {
            return Err(format!(
                "{}: empty project ID for signature handle {}",
                ERR_CLIENT_ERROR,
                handle
            ));
        }
        let reg = self.project_registries.read().unwrap().get(project_id).cloned();
        let Some(reg) = reg else {
            return Err(format!(
                "{}: signature handle {} not found (no registry for project {})",
                ERR_CLIENT_ERROR,
                handle,
                project_id
            ));
        };
        match reg.signatures.read().unwrap().get(&handle) {
            Some(entry) => Ok(entry.clone()),
            None => Err(format!(
                "{}: signature handle {} not found in project registry",
                ERR_CLIENT_ERROR,
                handle
            )),
        }
    }

    /// `(sd *snapshotData) resolveNodeHandle`.
    pub fn resolve_node_handle(
        &self,
        program: &compiler::program::Program,
        handle: &NodeHandle,
    ) -> Result<ast::NodeId, String> {
        resolve_node_handle(program, handle)
    }
}

/// `newFileSymbolResponse`.
///
/// PORT: the owning `SourceFile` `NodeId` in `nodes` is discovered via
/// `symbolOwnerFile`.
pub(crate) fn new_file_symbol_response(
    nodes: &mut Vec<ast::Node>,
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> SymbolResponse {
    let file = symbol_owner_file(nodes, arena, symbol)
        .expect("newFileSymbolResponse: expected a file-owned symbol");
    let descriptor = new_source_file_descriptor(nodes, file);
    let reference = SymbolReference {
        owner: SymbolOwner {
            kind: SYMBOL_OWNER_KIND_FILE,
            file: Some(descriptor),
            snapshot: 0,
            project: project::project::Id(String::new()),
        },
        id: symbol_handle(arena.get(symbol)),
    };
    build_symbol_response(nodes, arena, symbol, reference, Some(file))
}

/// `buildSymbolResponse`.
///
/// PORT: `owner` is the owning file `NodeId` (Go `*ast.SourceFile`), used
/// only for the assertions Go performs.
pub(crate) fn build_symbol_response(
    nodes: &mut Vec<ast::Node>,
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
    reference: SymbolReference,
    owner: Option<ast::NodeId>,
) -> SymbolResponse {
    let s = arena.get(symbol);
    let mut resp = SymbolResponse {
        reference,
        name: ast::escape_symbol_name(s.name.as_ref()).into_owned(),
        flags: s.flags.0,
        check_flags: s.check_flags.0,
        parent: s
            .parent
            .and_then(|p| new_symbol_reference(nodes, arena, p)),
        export_symbol: s
            .export_symbol
            .and_then(|e| new_symbol_reference(nodes, arena, e)),
        ..Default::default()
    };
    if owner.is_some() {
        // A client resolves a file-owned symbol's relationships through
        // its own source file.
        if let Some(parent) = s.parent {
            debug_assert_eq!(symbol_owner_file(nodes, arena, parent), owner);
        }
        if let Some(export) = s.export_symbol {
            debug_assert_eq!(symbol_owner_file(nodes, arena, export), owner);
        }
    }
    if !s.declarations.is_empty() {
        resp.declarations = s
            .declarations
            .iter()
            .map(|&decl| symbol_node_handle_from(nodes, decl, owner))
            .collect();
    }
    if let Some(value_declaration) = s.value_declaration {
        resp.value_declaration = symbol_node_handle_from(nodes, value_declaration, owner);
    }
    resp
}

/// `newSymbolReference` creates a compact reference to a symbol without
/// registering it. Clients resolve it from their caches or fetch the full
/// response through the corresponding property method.
///
/// PORT: takes `nodes` so file-owned symbols get their `File` key (the
/// `sourceFileNodeID` decimal string).
pub(crate) fn new_symbol_reference(
    nodes: &mut Vec<ast::Node>,
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> Option<CompactSymbolReference> {
    if symbol.is_none() {
        return None;
    }
    let mut reference = CompactSymbolReference {
        id: symbol_handle(arena.get(symbol)),
        file: String::new(),
    };
    if let Some(file) = symbol_owner_file(nodes, arena, symbol) {
        reference.file = source_file_node_id(file).to_string();
    }
    Some(reference)
}

/// `moduleResolverRegistration`.
pub(crate) struct ModuleResolverRegistration {
    pub id: ModuleResolverId,
    pub compiler_options: Arc<core_::options_generated::CompilerOptions>,
    pub resolutions: Option<Arc<module::StaticResolutions>>,
    pub resolve_module_name_callback: String,
}

/// `programResolutionContext` — resolver cache shared across the module
/// resolvers used by one in-progress program build.
///
/// PORT: lives in `module_resolution.rs` in Go — kept next to the session
/// state it protects, like Go's same-package layout.
pub(crate) struct ProgramResolutionContext {
    pub options: Mutex<module::ResolverOptions>,
    pub resolvers: Mutex<FxHashMap<ModuleResolverId, Arc<dyn module::Resolver>>>,
}

/// `batchResponsePage`.
pub(crate) struct BatchResponsePage {
    pub encoded_responses: Vec<json::Value>,
}

/// `SessionOptions` configures an API session.
#[derive(Default)]
pub struct SessionOptions {
    /// `UseBinaryResponses` enables binary responses for msgpack protocol.
    pub use_binary_responses: bool,
}

/// `DefaultMaxResponseBytesPerPage` leaves room for base64 expansion
/// beneath V8's maximum string length while rounding down to an even
/// decimal value.
pub const DEFAULT_MAX_RESPONSE_BYTES_PER_PAGE: usize = 300_000_000;

/// `Session` represents an API session that provides programmatic access
/// to TypeScript language services. It implements the `ipc::Handler`
/// interface to process incoming API requests.
///
/// The session supports multiple active snapshots, each with their own
/// symbol and type registries for maintaining object identity.
pub struct Session {
    id: String,
    snapshot_host: Arc<project::snapshothost::SnapshotHost>,
    owns_snapshot_host: bool,
    with_locale: Option<Arc<dyn Fn(core_::context::Context) -> core_::context::Context + Send + Sync>>,
    project_session: Option<Arc<project::session::Session>>,

    close_once: Mutex<bool>,

    /// Set to true when using `MessagePackProtocol`.
    use_binary_responses: bool,
    batch_response_pages: Mutex<FxHashMap<u64, BatchResponsePage>>,
    next_batch_response_page_id: AtomicU64,

    /// `snapshots` maps snapshot handles to their data. Each snapshot has
    /// its own symbol/type registries.
    ///
    /// `snapshots_mu` is held only for short, map-bounded critical
    /// sections, never across slow work like a project snapshot update or
    /// checker queries — same as Go.
    snapshots: RwLock<FxHashMap<u64, Arc<SnapshotData>>>,

    /// `openProjects`, `openFiles`, and `createdPrograms` are the
    /// canonical LSP-state resources owned by this API client. Guarded by
    /// `language_server_update_mu`.
    language_server_state: Mutex<LanguageServerState>,

    build_orchestrators: Mutex<FxHashMap<u64, Arc<build::Orchestrator>>>,

    next_module_resolver_id: AtomicU64,
    pub(crate) module_resolvers: RwLock<FxHashMap<u64, Rc<ModuleResolverRegistration>>>,
    pub(crate) next_program_resolution_context_id: AtomicU64,
    pub(crate) program_resolution_contexts:
        RwLock<FxHashMap<u64, Rc<ProgramResolutionContext>>>,
    pub(crate) source_file_leases: Mutex<FxHashMap<u64, Rc<project::snapshothost::SourceFileLease>>>,
    next_source_file_lease_id: AtomicU64,

    /// Session-side bound clones of leased parse-cache files, keyed on
    /// the shared `Arc<ParsedSourceFile>` pointer. Go binds cached files
    /// eagerly into the shared heap; Rust programs bind their own arena
    /// copies, so leases get a private bound clone for symbol queries.
    bound_source_files: Mutex<FxHashMap<usize, Rc<BoundSourceFile>>>,

    pub(crate) conn: Mutex<Option<Arc<dyn ipc::Conn>>>,

    cpu_profiler: pprof::CpuProfiler,
}

// Go's `*Session` is shared across request-serving goroutines; every
// non-Send member (arena handles in registries, `Rc` program/lease
// handles) is guarded by the same mutex regime as Go's fields. This is
// the same contract `tsc_project::session::Session` exposes via
// `SendShared`.
#[allow(unsafe_code)]
unsafe impl Send for Session {}
#[allow(unsafe_code)]
unsafe impl Sync for Session {}

/// `languageServerUpdateMu`-guarded LSP-state resources owned by this API
/// client.
#[derive(Default)]
pub(crate) struct LanguageServerState {
    pub open_projects: collections::Set<tspath::PathKey>,
    pub open_files: collections::Set<tspath::PathKey>,
    pub created_programs: collections::Set<project::project::SyntheticProjectId>,
}

/// `NewLSPSession` creates a new API session with the given project
/// session.
pub fn new_lsp_session(
    project_session: &Arc<project::session::Session>,
    options: Option<&SessionOptions>,
) -> Arc<Session> {
    let ps = project_session.clone();
    new_session(
        project_session.snapshot_host(),
        Some(Arc::new(move |ctx| ps.with_current_locale(ctx))),
        options,
        false,
        Some(project_session.clone()),
    )
}

/// `NewStandaloneSession` creates an API session with an independently
/// owned snapshot host.
pub fn new_standalone_session(
    init: &project::session::SessionInit,
    options: Option<&SessionOptions>,
) -> Arc<Session> {
    let snapshot_host = project::snapshothost::new_snapshot_host(init);
    new_session(snapshot_host, None, options, true, None)
}

/// `newSession`.
fn new_session(
    snapshot_host: Arc<project::snapshothost::SnapshotHost>,
    with_locale: Option<Arc<dyn Fn(core_::context::Context) -> core_::context::Context + Send + Sync>>,
    options: Option<&SessionOptions>,
    owns_snapshot_host: bool,
    project_session: Option<Arc<project::session::Session>>,
) -> Arc<Session> {
    let id = SESSION_ID_COUNTER.fetch_add(1, Ordering::Relaxed) + 1;
    Arc::new(Session {
        id: format_session_id(id),
        snapshot_host,
        owns_snapshot_host,
        with_locale: with_locale
            .or_else(|| Some(Arc::new(|ctx: core_::context::Context| ctx))),
        project_session,
        close_once: Mutex::new(false),
        use_binary_responses: options.is_some_and(|o| o.use_binary_responses),
        batch_response_pages: Default::default(),
        next_batch_response_page_id: AtomicU64::new(0),
        snapshots: Default::default(),
        language_server_state: Default::default(),
        build_orchestrators: Default::default(),
        next_module_resolver_id: AtomicU64::new(0),
        module_resolvers: Default::default(),
        next_program_resolution_context_id: AtomicU64::new(0),
        program_resolution_contexts: Default::default(),
        source_file_leases: Default::default(),
        next_source_file_lease_id: AtomicU64::new(0),
        bound_source_files: Default::default(),
        conn: Mutex::new(None),
        cpu_profiler: Default::default(),
    })
}

/// `formatSessionID`.
fn format_session_id(id: u64) -> String {
    format!("session-{id}")
}

impl Session {
    /// `s.ID` returns the unique identifier for this session.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// `s.SetConnection`.
    pub fn set_connection(&self, conn: Arc<dyn ipc::Conn>) {
        *self.conn.lock().unwrap() = Some(conn);
    }

    /// `s.GetCurrentDirectory`.
    pub fn get_current_directory(&self) -> tspath::RootedDirectoryPath {
        self.snapshot_host.get_current_directory()
    }

    /// `s.currentDirectory`.
    pub(crate) fn current_directory(&self) -> tspath::RootedDirectoryPath {
        self.get_current_directory()
    }

    /// `s.FS`.
    pub fn fs(&self) -> Arc<dyn vfs::Vfs> {
        if let Some(session) = &self.project_session {
            let fs: Arc<dyn vfs::Vfs> = session.fs().clone();
            return fs;
        }
        self.snapshot_host.fs().clone()
    }

    /// `s.DefaultLibraryPath`.
    pub fn default_library_path(&self) -> tspath::RootedDirectoryPath {
        if let Some(session) = &self.project_session {
            return session.default_library_path();
        }
        self.snapshot_host.default_library_path()
    }

    /// `s.caseSensitivity`.
    pub(crate) fn case_sensitivity(&self) -> tspath::CaseSensitivity {
        self.snapshot_host.fs().case_sensitivity()
    }

    /// `s.useBinaryResponses`.
    pub(crate) fn use_binary_responses(&self) -> bool {
        self.use_binary_responses
    }

    /// `snapshotHandle` creates a snapshot handle from a snapshot's ID.
    pub(crate) fn snapshot_handle(snapshot: &project::snapshot::Snapshot) -> SnapshotId {
        snapshot.id()
    }

    /// `s.getSnapshotData` looks up snapshot data by handle.
    pub(crate) fn get_snapshot_data(
        &self,
        handle: SnapshotId,
    ) -> Result<Arc<SnapshotData>, String> {
        match self.snapshots.read().unwrap().get(&handle) {
            Some(sd) => Ok(sd.clone()),
            None => Err(format!(
                "{}: snapshot {} not found",
                ERR_CLIENT_ERROR,
                handle
            )),
        }
    }

    /// `s.retainSnapshotData` pins snapshot data while an operation
    /// builds a derived snapshot.
    pub(crate) fn retain_snapshot_data(
        &self,
        handle: SnapshotId,
    ) -> Result<Arc<SnapshotData>, String> {
        let mut snapshots = self.snapshots.write().unwrap();
        match snapshots.get(&handle) {
            Some(sd) => {
                sd.ref_count.set(sd.ref_count.get() + 1);
                Ok(sd.clone())
            }
            None => Err(format!(
                "{}: snapshot {} not found",
                ERR_CLIENT_ERROR,
                handle
            )),
        }
    }

    /// `s.releaseSnapshot`.
    pub(crate) fn release_snapshot(&self, handle: SnapshotId) -> Result<(), String> {
        let sd = {
            let mut snapshots = self.snapshots.write().unwrap();
            match snapshots.get(&handle) {
                Some(sd) => {
                    sd.ref_count.set(sd.ref_count.get() - 1);
                    if sd.ref_count.get() <= 0 {
                        snapshots.remove(&handle)
                    } else {
                        return Ok(());
                    }
                }
                None => {
                    return Err(format!(
                        "{}: snapshot {} not found",
                        ERR_CLIENT_ERROR,
                        handle
                    ));
                }
            }
        };
        if let Some(sd) = sd {
            sd.snapshot.deref();
        }
        Ok(())
    }

    /// `s.setupChecker` resolves snapshot, program, and type checker for
    /// a project. Callers must invoke `setup.done` to release the
    /// checker.
    pub(crate) fn setup_checker(
        &self,
        ctx: &core_::context::Context,
        snapshot: SnapshotId,
        project_handle: &project::project::Id,
    ) -> Result<CheckerSetup, String> {
        let sd = self.get_snapshot_data(snapshot)?;
        let program = sd.get_program(project_handle)?;
        let (c, done) = program.get_type_checker(core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Api,
        ));
        Ok(CheckerSetup {
            sd,
            snapshot,
            program,
            checker: c,
            done: Some(done),
            project_id: project_handle.clone(),
        })
    }

    /// `s.setupLanguageService` creates a LanguageService for the given
    /// snapshot/project. Unlike `setupChecker`, this does NOT acquire a
    /// checker from the pool — see the Go comment on
    /// `setupLanguageService` for the lifetime contract.
    pub(crate) fn setup_language_service<'h>(
        &self,
        snapshot: &'h project::snapshot::Snapshot,
        program: &Rc<compiler::program::Program>,
        project_handle: &project::project::Id,
        active_file: &str,
    ) -> Result<ls::languageservice::LanguageService<'h>, String> {
        let Some(proj) = snapshot.project_collection.get_project(project_handle) else {
            return Err(format!(
                "{}: project {} not found",
                ERR_CLIENT_ERROR,
                project_handle
            ));
        };
        Ok(ls::languageservice::new_language_service(
            ls::autoimport::registry::ProjectId(Rc::from(proj.id().as_str())),
            program.clone(),
            snapshot,
            active_file,
        ))
    }

    /// `s.resolveSymbolReference` resolves a symbol without a semantic
    /// context. A file reference holds the exact cached AST until the
    /// returned lease guard is dropped; a snapshot reference also returns
    /// the snapshot and canonical project that own the symbol.
    ///
    /// PORT: the Go `func()` release becomes `ResolveSymbolGuard`.
    pub(crate) fn resolve_symbol_reference(
        &self,
        ref_: &SymbolReference,
    ) -> Result<ResolvedSymbol, String> {
        match ref_.owner.kind {
            SYMBOL_OWNER_KIND_FILE => {
                if ref_.owner.file.is_none() || ref_.owner.snapshot != 0 || !ref_.owner.project.0.is_empty() {
                    return Err(format!(
                        "{}: invalid file symbol reference",
                        ERR_CLIENT_ERROR
                    ));
                }
                let lease = self.acquire_cached_source_file(ref_.owner.file.as_ref().unwrap())?;
                let bound = self.bound_source_file(&lease);
                let Some(&symbol) = bound.symbol_index.get(&ref_.id) else {
                    lease.release();
                    return Err(format!(
                        "{}: symbol {} not found in source file",
                        ERR_CLIENT_ERROR,
                        ref_.id
                    ));
                };
                Ok(ResolvedSymbol {
                    entry: SymbolEntry {
                        arena: bound.symbols.clone(),
                        symbol,
                    },
                    sd: None,
                    canonical_project: project::project::Id(String::new()),
                    lease: Some(lease),
                    bound: Some(bound),
                })
            }
            SYMBOL_OWNER_KIND_SNAPSHOT => {
                if ref_.owner.file.is_some() || ref_.owner.snapshot == 0 || ref_.owner.project.0.is_empty() {
                    return Err(format!(
                        "{}: invalid snapshot symbol reference",
                        ERR_CLIENT_ERROR
                    ));
                }
                let sd = self.get_snapshot_data(ref_.owner.snapshot)?;
                let entry = sd.resolve_symbol_handle(ref_.id)?;
                Ok(ResolvedSymbol {
                    entry,
                    sd: Some(sd),
                    canonical_project: ref_.owner.project.clone(),
                    lease: None,
                    bound: None,
                })
            }
            _ => Err(format!(
                "{}: invalid symbol reference kind {:?}",
                ERR_CLIENT_ERROR,
                ref_.owner.kind
            )),
        }
    }

    /// `s.acquireSourceFile` — wraps the snapshot host's parse-cache
    /// acquire.
    pub(crate) fn acquire_source_file(
        &self,
        options: ast::parseoptions::SourceFileParseOptions,
        source_text: String,
        script_kind: core_::scriptkind::ScriptKind,
    ) -> project::snapshothost::SourceFileLease {
        self.snapshot_host
            .acquire_source_file(options, source_text, script_kind)
    }

    /// `s.acquireCachedSourceFile` — resolves a
    /// `SourceFileDescriptor` into a lease on the parse cache.
    pub(crate) fn acquire_cached_source_file(
        &self,
        descriptor: &SourceFileDescriptor,
    ) -> Result<project::snapshothost::SourceFileLease, String> {
        let key = descriptor
            .parse_cache_key()
            .map_err(|e| format!("{}: invalid source file descriptor: {}", ERR_CLIENT_ERROR, e))?;
        let Some(lease) = self.snapshot_host.acquire_existing_source_file(&key) else {
            return Err(format!("{}: source file is not available", ERR_CLIENT_ERROR));
        };
        // The parse-cache key addresses a live ordinary file, but an equal
        // key can identify a new AST after the original entry is evicted.
        // The node ID verifies that this is the exact AST observed by the
        // client; it is not used to address or retain the file.
        {
            let parsed = lease.source_file();
            let parsed = parsed.lock().unwrap();
            if new_source_file_descriptor(parsed.nodes.get_mut(), parsed.file) != *descriptor {
                drop(parsed);
                lease.release();
                return Err(format!(
                    "{}: source file descriptor no longer identifies the cached source file",
                    ERR_CLIENT_ERROR
                ));
            }
        }
        Ok(lease)
    }

    /// `boundSourceFile` returns the session's privately-bound clone of a
    /// leased source file. Go binds cached files eagerly so their symbols
    /// live on the shared heap; Rust binds program-owned arena copies, so
    /// an unbound cache file gets a session-side bound clone keyed on the
    /// shared `ParsedSourceFile`.
    ///
    /// Symbol `SymbolId`s in the clone index into `symbols`.
    pub(crate) fn bound_source_file(
        &self,
        lease: &project::snapshothost::SourceFileLease,
    ) -> Rc<BoundSourceFile> {
        let key = Arc::as_ptr(lease.source_file()) as usize;
        if let Some(bound) = self.bound_source_files.lock().unwrap().get(&key) {
            return bound.clone();
        }
        let (file, nodes_vec) = {
            let parsed = lease.source_file();
            let parsed = parsed.lock().unwrap();
            (parsed.file, (**parsed.nodes).clone())
        };
        let nodes = Rc::new(ast::NodeArenaBuf::new(nodes_vec));
        let symbols = ast::SymbolArena::default();
        tsc_binder::binder::bind_source_file(nodes.get_mut(), file, &symbols);
        let index = get_source_file_symbol_index(&symbols, nodes.get_mut(), file);
        let bound = Rc::new(BoundSourceFile {
            nodes,
            file,
            symbols,
            symbol_index: index,
        });
        self.bound_source_files
            .lock()
            .unwrap()
            .insert(key, bound.clone());
        bound
    }

    /// `s.pathKey`.
    pub(crate) fn path_key(&self, file_name: &tspath::RootedFilePath) -> tspath::PathKey {
        self.case_sensitivity().path_key(&file_name.as_path())
    }

    /// `s.toFileName`.
    pub(crate) fn to_file_name(&self, document: &DocumentIdentifier) -> tspath::RootedFilePath {
        document.to_file_name(&self.get_current_directory())
    }

    /// `s.toURI`.
    pub(crate) fn to_uri(&self, document: &DocumentIdentifier) -> lsproto::DocumentUri {
        document.to_uri(&self.get_current_directory())
    }

    /// `s.toFileChangeSummary`.
    pub(crate) fn to_file_change_summary(
        &self,
        changes: Option<&FileNotifications>,
    ) -> project::filechange::FileChangeSummary {
        let mut summary = project::filechange::FileChangeSummary::default();
        let Some(changes) = changes else {
            return summary;
        };
        if changes.invalidate_all {
            summary.invalidate_all = true;
            summary.includes_watch_change_outside_node_modules = true;
            return summary;
        }
        let cwd = self.get_current_directory();
        for doc in &changes.changed {
            summary.changed.add(doc.to_uri(&cwd));
        }
        for doc in &changes.created {
            summary.created.add(doc.to_uri(&cwd));
        }
        for doc in &changes.deleted {
            summary.deleted.add(doc.to_uri(&cwd));
        }
        if summary.changed.len() + summary.created.len() + summary.deleted.len() > 0 {
            summary.includes_watch_change_outside_node_modules = true;
        }
        summary
    }

    /// `s.Close`.
    pub fn close(&self) {
        let mut closed = self.close_once.lock().unwrap();
        if *closed {
            return;
        }
        *closed = true;
        // Clear per-snapshot registries and deref retained snapshots.
        let snapshots: Vec<Arc<SnapshotData>> =
            self.snapshots.write().unwrap().drain().map(|(_, v)| v).collect();
        for sd in &snapshots {
            sd.snapshot.deref();
        }
        self.release_language_server_refs();
        self.source_file_leases.lock().unwrap().clear();
        *self.conn.lock().unwrap() = None;
        if self.owns_snapshot_host {
            self.snapshot_host.close();
        }
    }

    /// `s.releaseLanguageServerRefs` releases the canonical LSP-state
    /// resources (open projects/files/programs) against the current
    /// snapshot.
    fn release_language_server_refs(&self) {
        // Go routes through `updateSnapshot`-equivalent teardown; the
        // language-server state is cleared under `languageServerUpdateMu`.
        let mut state = self.language_server_state.lock().unwrap();
        state.open_projects.clear();
        state.open_files.clear();
        state.created_programs.clear();
    }
}

/// `checkerSetup` holds the common context needed by handlers that
/// require a type checker.
pub(crate) struct CheckerSetup {
    pub sd: Arc<SnapshotData>,
    pub snapshot: SnapshotId,
    pub program: Rc<compiler::program::Program>,
    pub checker: Rc<std::cell::RefCell<Checker>>,
    pub done: Option<compiler::checker_pool::DoneFn>,
    pub project_id: project::project::Id,
}

impl CheckerSetup {
    /// `(setup checkerSetup) newSymbolResponse`.
    pub fn new_symbol_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        arena: &ast::SymbolArena,
        symbol: ast::SymbolId,
    ) -> Option<SymbolResponse> {
        self.sd
            .new_symbol_response(nodes, arena, symbol, &self.project_id)
    }

    /// `(setup checkerSetup) newSignatureResponse`.
    pub fn new_signature_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        c: &Checker,
        signature: checker::SignatureId,
    ) -> Option<SignatureResponse> {
        self.sd
            .new_signature_response(nodes, c, &self.project_id, signature)
    }

    /// `(setup checkerSetup) newIndexInfoResponse`.
    pub fn new_index_info_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        c: &mut Checker,
        info: &checker::IndexInfo,
    ) -> Option<IndexInfoResponse> {
        let mut result = IndexInfoResponse {
            key_type: match info.key_type {
                Some(t) => self.sd.new_type_response(nodes, c, &self.project_id, t)?,
                None => return None,
            },
            value_type: match info.value_type {
                Some(t) => self.sd.new_type_response(nodes, c, &self.project_id, t)?,
                None => return None,
            },
            is_readonly: info.is_readonly,
            ..Default::default()
        };
        if let Some(declaration) = info.declaration {
            result.declaration = self.sd.node_handle_from(
                nodes,
                ast::get_source_file_of_node(Some(declaration), nodes).unwrap(),
                declaration,
            );
        }
        Some(result)
    }

    /// `(setup checkerSetup) resolveTypeHandle`.
    pub fn resolve_type_handle(&self, id: TypeId) -> Result<TypeEntry, String> {
        self.sd.resolve_type_handle(&self.project_id, id)
    }

    /// `(setup checkerSetup) resolveSymbolHandle`.
    ///
    /// PORT: `resolveTypeHandle`/`resolveSignatureHandle` return registry
    /// entries carrying their arena; a symbol resolves to `(arena, id)`.
    pub fn resolve_symbol_handle(
        &self,
        ref_: &SymbolReference,
        nodes: &mut Vec<ast::Node>,
    ) -> Result<SymbolEntry, String> {
        match ref_.owner.kind {
            SYMBOL_OWNER_KIND_SNAPSHOT => {
                if ref_.owner.snapshot != self.snapshot || ref_.owner.file.is_some() {
                    return Err(format!(
                        "{}: snapshot symbol reference does not match the requested checker",
                        ERR_CLIENT_ERROR
                    ));
                }
                self.sd.resolve_symbol_handle(ref_.id)
            }
            SYMBOL_OWNER_KIND_FILE => {
                if ref_.owner.file.is_none() || ref_.owner.snapshot != 0 || !ref_.owner.project.0.is_empty() {
                    return Err(format!(
                        "{}: invalid file symbol reference",
                        ERR_CLIENT_ERROR
                    ));
                }
                let descriptor = ref_.owner.file.as_ref().unwrap();
                let path_key = tspath::try_path_key_from_canonical(descriptor.path.as_string())
                    .unwrap_or_else(|| descriptor.path.clone());
                let Some(source_file) = self.program.get_source_file_by_path(&path_key) else {
                    return Err(format!(
                        "{}: source file is not part of the requested program",
                        ERR_CLIENT_ERROR
                    ));
                };
                let file_nodes = self.program.arena_of(source_file);
                if new_source_file_descriptor(&file_nodes, source_file) != *descriptor {
                    return Err(format!(
                        "{}: source file is not part of the requested program",
                        ERR_CLIENT_ERROR
                    ));
                }
                let arena = self.program.symbols.clone();
                let index = get_source_file_symbol_index(
                    &arena,
                    file_nodes.get_mut(),
                    source_file,
                );
                match index.get(&ref_.id) {
                    Some(&symbol) => Ok(SymbolEntry { arena, symbol }),
                    None => Err(format!(
                        "{}: symbol handle {} not found in source file",
                        ERR_CLIENT_ERROR,
                        ref_.id
                    )),
                }
            }
            _ => Err(format!(
                "{}: invalid symbol reference kind {:?}",
                ERR_CLIENT_ERROR,
                ref_.owner.kind
            )),
        }
    }

    /// `(setup checkerSetup) resolveSignatureHandle`.
    pub fn resolve_signature_handle(&self, id: SignatureId) -> Result<SignatureEntry, String> {
        self.sd.resolve_signature_handle(&self.project_id, id)
    }

    /// `(setup checkerSetup) resolveLocation` resolves an optional
    /// location, given either as a node handle or as a file and position.
    /// Returns `None` when neither is provided.
    pub fn resolve_location(
        &self,
        handle: &NodeHandle,
        file: Option<&DocumentIdentifier>,
        position: Option<u32>,
    ) -> Result<Option<ast::NodeId>, String> {
        if !handle.0.is_empty() {
            return self
                .sd
                .resolve_node_handle(&self.program, handle)
                .map(Some);
        }
        if let (Some(file), Some(position)) = (file, position) {
            let file_name = file.to_file_name(&self.program.base_directory());
            let Some(source_file) = self.program.get_source_file(&file_name) else {
                return Err(format!(
                    "{}: source file not found: {}",
                    ERR_CLIENT_ERROR,
                    file
                ));
            };
            let nodes = self.program.arena_of(source_file);
            let position = nodes[source_file]
                .as_source_file()
                .position_map()
                .utf16_to_utf8(position as usize);
            return Ok(astnav::tokens::get_touching_property_name(
                nodes.get_mut(),
                source_file,
                position as core_::text::TextPos,
            ));
        }
        Ok(None)
    }
}

impl Drop for CheckerSetup {
    fn drop(&mut self) {
        if let Some(done) = self.done.take() {
            done();
        }
    }
}

/// `ResolvedSymbol` — Go's `(symbol, sd, project, release, err)` tuple.
/// Dropping the guard releases the source-file lease for file-owned
/// references.
pub(crate) struct ResolvedSymbol {
    pub entry: SymbolEntry,
    pub sd: Option<Arc<SnapshotData>>,
    pub canonical_project: project::project::Id,
    /// The held lease for `SYMBOL_OWNER_KIND_FILE` references — Go's
    /// `lease.Release` deferred call.
    pub lease: Option<project::snapshothost::SourceFileLease>,
    /// The session-bound clone the symbol lives in — keeps the node
    /// arena reachable for file-owned symbols.
    pub bound: Option<Rc<BoundSourceFile>>,
}

impl Drop for ResolvedSymbol {
    fn drop(&mut self) {
        if let Some(lease) = self.lease.take() {
            lease.release();
        }
    }
}
