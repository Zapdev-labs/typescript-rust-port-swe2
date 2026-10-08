// Ported from tsc/internal/checker/mapper.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// TypeMapper variants: simple, array, array-to-single, deferred, function,
// merged, composite, and inference mappers.
//
// PORT notes:
//
// - `*TypeMapper` → `TypeMapperId` into `TypeMapperArena`
//   (`Arc<RwLock<Vec<TypeMapper>>>`). The `Arc` lets `Checker::map_type`-style
//   call sites clone the arena handle so the mapper lookup does not hold a
//   borrow on `c` while `Map` implementations call `&mut Checker` methods
//   (Composite → `instantiateType`, Inference → `inferFromIntraExpressionSites`
//   / `getInferredType`). Go's GC handles this aliasing for free.
// - `TypeMapperData` interface → `TypeMapperData` enum; the embedded
//   `TypeMapper`/`TypeMapperBase` chain collapses into the enum + struct.
// - `DeferredTypeMapper.targets []func() *Type` → boxed `Fn(&mut Checker) ->
//   TypeId` closures: Go closures capture `c`; in the port the checker is
//   passed explicitly to avoid a self-referential capture (SPEC §5.4).
// - `FunctionTypeMapper.fn func(*Type) *Type` → `Fn(&mut Checker, TypeId) ->
//   TypeId` for the same reason.
// - `InferenceTypeMapper.n *InferenceContext` → `InferenceContextId` into
//   `Checker::inference_contexts`.
// - `Map(t)` is `TypeMapperArena::map(c, m, t)` — a method on the arena so
//   merged/composite variants can resolve nested `TypeMapperId`s.
// - `MapsThisOnly` needs the type arena (`isThisTypeParameter`), so it takes
//   `&TypeArena` — mirrored `is_this_type_parameter` lives in
//   checker_core.rs pending utilities.go.

use std::sync::{Arc, RwLock};

use tsc_core::core::map as core_map;

use crate::checker_core::{
    self, Checker, InferenceContextId, get_non_distributed_type_parameter,
    is_this_type_parameter,
};
use crate::types::{TypeArena, TypeId};

/// `type TypeMapperKind int32`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum TypeMapperKind {
    /// `TypeMapperKindUnknown`
    #[default]
    Unknown = 0,
    /// `TypeMapperKindSimple`
    Simple = 1,
    /// `TypeMapperKindArray`
    Array = 2,
    /// `TypeMapperKindMerged`
    Merged = 3,
}

/// `type TypeMapperId uint32` — index into `TypeMapperArena`
/// (Go `*TypeMapper`).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct TypeMapperId(pub u32);

impl TypeMapperId {
    /// The absent value — Go's nil `*TypeMapper`.
    pub const NONE: TypeMapperId = TypeMapperId(u32::MAX);

    /// Whether this id is `TypeMapperId::NONE`.
    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    /// Whether this id is not `TypeMapperId::NONE`.
    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }

    /// The arena index of this id.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

// TypeMapper

/// `type TypeMapper struct`.
pub struct TypeMapper {
    /// `data`.
    pub data: TypeMapperData,
}

// TypeMapperData

/// `type TypeMapperData interface`. `Map`/`Kind`/`MapsThisOnly` dispatch on
/// the enum.
pub enum TypeMapperData {
    /// `*SimpleTypeMapper`.
    Simple(SimpleTypeMapper),
    /// `*ArrayTypeMapper`.
    Array(ArrayTypeMapper),
    /// `*ArrayToSingleTypeMapper`.
    ArrayToSingle(ArrayToSingleTypeMapper),
    /// `*DeferredTypeMapper`.
    Deferred(DeferredTypeMapper),
    /// `*FunctionTypeMapper`.
    Function(FunctionTypeMapper),
    /// `*MergedTypeMapper`.
    Merged(MergedTypeMapper),
    /// `*CompositeTypeMapper`.
    Composite(CompositeTypeMapper),
    /// `*InferenceTypeMapper`.
    Inference(InferenceTypeMapper),
}

/// `type TypeMapperArena` — arena of `TypeMapper` elements indexed by
/// `TypeMapperId`. `Arc<RwLock<..>>` so mapper lookups can detach from a
/// `&Checker` borrow before calling `&mut Checker` methods — see header.
#[derive(Clone)]
pub struct TypeMapperArena {
    mappers: Arc<RwLock<Vec<TypeMapper>>>,
}

impl Default for TypeMapperArena {
    fn default() -> Self {
        Self {
            mappers: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

impl TypeMapperArena {
    /// Allocate a mapper, returning its `TypeMapperId` — the role of Go's
    /// `&X{...}` constructor returns.
    pub fn alloc(&self, m: TypeMapper) -> TypeMapperId {
        let mut mappers = self.mappers.write().unwrap();
        let id = TypeMapperId(mappers.len() as u32);
        mappers.push(m);
        id
    }

    /// `len(mappers)`.
    pub fn len(&self) -> usize {
        self.mappers.read().unwrap().len()
    }

    /// `len(mappers) == 0`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// `(m *TypeMapper) Map(t)` — `m.data.Map(t)`.
    ///
    /// PORT: takes `&mut Checker` because Composite/Deferred/Function/
    /// Inference variants reach checker methods (`instantiateType`,
    /// `getInferredType`, closures capturing `c` in Go).
    pub fn map(&self, c: &mut Checker, m: TypeMapperId, t: TypeId) -> TypeId {
        // Read the payload under a short guard so recursive `map` calls and
        // `&mut c` calls aren't holding the arena lock. The kind and the
        // Copy-able fields are copied out; only the Deferred/Function
        // closures are invoked under the guard (they don't re-enter the
        // arena).
        enum Action {
            Passthrough,
            Result(TypeId),
            Merged(TypeMapperId, TypeMapperId),
            Composite(TypeMapperId, TypeMapperId),
            Inference(InferenceContextId, bool),
            DeferredTarget(usize),
            Fn,
        }
        let action;
        {
            let guard = self.mappers.read().unwrap();
            let mapper = &guard[m.index()];
            action = match &mapper.data {
                TypeMapperData::Simple(s) => {
                    if t == s.source {
                        Action::Result(s.target)
                    } else {
                        Action::Passthrough
                    }
                }
                TypeMapperData::Array(s) => {
                    match s.sources.iter().position(|&src| src == t) {
                        Some(i) => Action::Result(s.targets[i]),
                        None => Action::Passthrough,
                    }
                }
                TypeMapperData::ArrayToSingle(s) => {
                    if s.sources.contains(&t) {
                        Action::Result(s.target)
                    } else {
                        Action::Passthrough
                    }
                }
                TypeMapperData::Deferred(s) => {
                    match s.sources.iter().position(|&src| src == t) {
                        Some(i) => Action::DeferredTarget(i),
                        None => Action::Passthrough,
                    }
                }
                TypeMapperData::Function(_) => Action::Fn,
                TypeMapperData::Merged(s) => Action::Merged(s.m1, s.m2),
                TypeMapperData::Composite(s) => Action::Composite(s.m1, s.m2),
                TypeMapperData::Inference(s) => Action::Inference(s.n, s.fixing),
            };
        }
        match action {
            Action::Passthrough => t,
            Action::Result(id) => id,
            Action::Merged(m1, m2) => {
                let t1 = self.map(c, m1, t);
                self.map(c, m2, t1)
            }
            Action::Composite(m1, m2) => {
                // `CompositeTypeMapper.Map`: `t1 := m.m1.Map(t); if t1 != t {
                // return m.c.instantiateType(t1, m.m2) }; return m.m2.Map(t)`
                let t1 = self.map(c, m1, t);
                if t1 != t {
                    return c.instantiate_type(t1, Some(m2));
                }
                self.map(c, m2, t)
            }
            Action::DeferredTarget(i) => {
                // The closure call needs `&mut c`; the arena guard is already
                // dropped? No — we re-enter the guard here to fetch the
                // target closure. Closures can't be cloned, so invoke under
                // a short read guard: the closure receives `&mut Checker`
                // which can safely allocate *types* but must not call back
                // into `type_mappers.map` (RwLock read-reentrancy).
                let guard = self.mappers.read().unwrap();
                let mapper = &guard[m.index()];
                match &mapper.data {
                    TypeMapperData::Deferred(s) => s.targets[i](c),
                    _ => unreachable!(),
                }
            }
            Action::Fn => {
                let guard = self.mappers.read().unwrap();
                let mapper = &guard[m.index()];
                match &mapper.data {
                    TypeMapperData::Function(s) => (s.f)(c, t),
                    _ => unreachable!(),
                }
            }
            Action::Inference(n, fixing) => {
                // `InferenceTypeMapper.Map`.
                let found = {
                    let ctx = &c.inference_contexts[n.index()];
                    ctx.inferences
                        .iter()
                        .position(|inference| inference.type_parameter == Some(t))
                };
                if let Some(i) = found {
                    let needs_fix = fixing && !c.inference_contexts[n.index()].inferences[i].is_fixed;
                    if needs_fix {
                        // Before we commit to a particular inference (and
                        // thus lock out any further inferences), we infer
                        // from any intra-expression inference sites we have
                        // collected.
                        c.infer_from_intra_expression_sites(n);
                        checker_core::clear_cached_inferences(
                            &mut c.inference_contexts[n.index()].inferences,
                        );
                        c.inference_contexts[n.index()].inferences[i].is_fixed = true;
                    }
                    return c.get_inferred_type(n, i);
                }
                t
            }
        }
    }

    /// `(m *TypeMapper) Kind()` — `m.data.Kind()`. Variants without an
    /// override return `TypeMapperKind::Unknown` (the `TypeMapperBase`
    /// default).
    pub fn kind(&self, m: TypeMapperId) -> TypeMapperKind {
        let guard = self.mappers.read().unwrap();
        match &guard[m.index()].data {
            TypeMapperData::Simple(_) => TypeMapperKind::Simple,
            TypeMapperData::Array(_) => TypeMapperKind::Array,
            TypeMapperData::Merged(_) => TypeMapperKind::Merged,
            _ => TypeMapperKind::Unknown,
        }
    }

    /// `(m *TypeMapper) MapsThisOnly()` — `m.data.MapsThisOnly()`.
    /// PORT: `isThisTypeParameter` needs the type arena.
    pub fn maps_this_only(&self, types: &TypeArena, m: TypeMapperId) -> bool {
        let guard = self.mappers.read().unwrap();
        match &guard[m.index()].data {
            TypeMapperData::Simple(s) => is_this_type_parameter(types, s.source),
            TypeMapperData::Array(s) => {
                s.sources.len() == 1 && is_this_type_parameter(types, s.sources[0])
            }
            TypeMapperData::ArrayToSingle(s) => {
                s.sources.len() == 1 && is_this_type_parameter(types, s.sources[0])
            }
            TypeMapperData::Deferred(s) => {
                s.sources.len() == 1 && is_this_type_parameter(types, s.sources[0])
            }
            _ => false,
        }
    }
}

// Factory functions

/// `getMappedType`.
pub fn get_mapped_type(c: &mut Checker, t: TypeId, mapper: TypeMapperId) -> TypeId {
    let non_distributed = get_non_distributed_type_parameter(&c.types, t);
    let mappers = c.type_mappers.clone();
    mappers.map(c, mapper, non_distributed)
}

/// `newTypeMapper`.
pub fn new_type_mapper(c: &mut Checker, sources: Vec<TypeId>, targets: Vec<TypeId>) -> TypeMapperId {
    if sources.len() == 1 {
        return new_simple_type_mapper(c, sources[0], targets[0]);
    }
    new_array_type_mapper(c, sources, targets)
}

impl Checker {
    /// `(c *Checker) combineTypeMappers`.
    pub fn combine_type_mappers(
        &mut self,
        m1: Option<TypeMapperId>,
        m2: TypeMapperId,
    ) -> TypeMapperId {
        if let Some(m1) = m1 {
            return new_composite_type_mapper(self, m1, m2);
        }
        m2
    }

    /// `(c *Checker) mapTypeWithCompositeMapper`.
    pub fn map_type_with_composite_mapper(
        &mut self,
        t: TypeId,
        m1: Option<TypeMapperId>,
        m2: TypeMapperId,
    ) -> TypeId {
        if m1.is_none() {
            return get_mapped_type(self, t, m2);
        }
        let t1 = get_mapped_type(self, t, m1.unwrap());
        if t1 != t {
            return self.instantiate_type(t1, Some(m2));
        }
        get_mapped_type(self, t, m2)
    }

    /// `(c *Checker) newBackreferenceMapper` — maps forward-references to
    /// later type parameters to the empty object type. This is used during
    /// inference when instantiating type parameter defaults.
    pub fn new_backreference_mapper(
        &mut self,
        context: InferenceContextId,
        index: usize,
    ) -> TypeMapperId {
        let type_parameters: Vec<TypeId> = {
            let ctx = &self.inference_contexts[context.index()];
            core_map(&ctx.inferences[index..], |i| i.type_parameter.unwrap())
        };
        new_array_to_single_type_mapper(self, type_parameters, self.unknown_type)
    }

    /// `(c *Checker) newInferenceTypeMapper`.
    pub fn new_inference_type_mapper(
        &mut self,
        n: InferenceContextId,
        fixing: bool,
    ) -> TypeMapperId {
        self.type_mappers.alloc(TypeMapper {
            data: TypeMapperData::Inference(InferenceTypeMapper { n, fixing }),
        })
    }
}

/// `mergeTypeMappers`.
pub fn merge_type_mappers(
    c: &mut Checker,
    m1: Option<TypeMapperId>,
    m2: TypeMapperId,
) -> TypeMapperId {
    if let Some(m1) = m1 {
        return new_merged_type_mapper(c, m1, m2);
    }
    m2
}

/// `prependTypeMapping`.
pub fn prepend_type_mapping(
    c: &mut Checker,
    source: TypeId,
    target: TypeId,
    mapper: Option<TypeMapperId>,
) -> TypeMapperId {
    let source = get_non_distributed_type_parameter(&c.types, source);
    let new_mapper = new_simple_type_mapper(c, source, target);
    match mapper {
        None => new_mapper,
        Some(mapper) => new_merged_type_mapper(c, new_mapper, mapper),
    }
}

/// `appendTypeMapping`.
pub fn append_type_mapping(
    c: &mut Checker,
    mapper: Option<TypeMapperId>,
    source: TypeId,
    target: TypeId,
) -> TypeMapperId {
    let source = get_non_distributed_type_parameter(&c.types, source);
    let new_mapper = new_simple_type_mapper(c, source, target);
    match mapper {
        None => new_mapper,
        Some(mapper) => new_merged_type_mapper(c, mapper, new_mapper),
    }
}

// TypeMapperBase — the Go struct embeds TypeMapper and provides default
// Map/Kind/MapsThisOnly; in the port those defaults live in the enum
// dispatch arms (Unknown kind, pass-through map is unreachable for the
// concrete variants, `false` from maps_this_only).

// SimpleTypeMapper

/// `type SimpleTypeMapper struct`.
pub struct SimpleTypeMapper {
    /// `source`.
    pub source: TypeId,
    /// `target`.
    pub target: TypeId,
}

/// `newSimpleTypeMapper`.
pub fn new_simple_type_mapper(c: &mut Checker, source: TypeId, target: TypeId) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::Simple(SimpleTypeMapper { source, target }),
    })
}

// ArrayTypeMapper

/// `type ArrayTypeMapper struct`.
pub struct ArrayTypeMapper {
    /// `sources`.
    pub sources: Vec<TypeId>,
    /// `targets`.
    pub targets: Vec<TypeId>,
}

/// `newArrayTypeMapper`.
pub fn new_array_type_mapper(
    c: &mut Checker,
    sources: Vec<TypeId>,
    targets: Vec<TypeId>,
) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::Array(ArrayTypeMapper { sources, targets }),
    })
}

// ArrayToSingleTypeMapper

/// `type ArrayToSingleTypeMapper struct`.
pub struct ArrayToSingleTypeMapper {
    /// `sources`.
    pub sources: Vec<TypeId>,
    /// `target`.
    pub target: TypeId,
}

/// `newArrayToSingleTypeMapper`.
pub fn new_array_to_single_type_mapper(
    c: &mut Checker,
    sources: Vec<TypeId>,
    target: TypeId,
) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::ArrayToSingle(ArrayToSingleTypeMapper { sources, target }),
    })
}

// DeferredTypeMapper

/// `type DeferredTypeMapper struct`. `targets []func() *Type` → boxed
/// closures taking the checker explicitly (see file header).
pub struct DeferredTypeMapper {
    /// `sources`.
    pub sources: Vec<TypeId>,
    /// `targets`.
    pub targets: Vec<Box<dyn Fn(&mut Checker) -> TypeId>>,
}

/// `newDeferredTypeMapper`.
pub fn new_deferred_type_mapper(
    c: &mut Checker,
    sources: Vec<TypeId>,
    targets: Vec<Box<dyn Fn(&mut Checker) -> TypeId>>,
) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::Deferred(DeferredTypeMapper { sources, targets }),
    })
}

// FunctionTypeMapper

/// `type FunctionTypeMapper struct`.
pub struct FunctionTypeMapper {
    /// `fn` — `func(*Type) *Type` gains the checker parameter (see header).
    pub f: Box<dyn Fn(&mut Checker, TypeId) -> TypeId>,
}

/// `newFunctionTypeMapper`.
pub fn new_function_type_mapper(
    c: &mut Checker,
    f: impl Fn(&mut Checker, TypeId) -> TypeId + 'static,
) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::Function(FunctionTypeMapper { f: Box::new(f) }),
    })
}

// MergedTypeMapper

/// `type MergedTypeMapper struct`.
pub struct MergedTypeMapper {
    /// `m1`.
    pub m1: TypeMapperId,
    /// `m2`.
    pub m2: TypeMapperId,
}

/// `newMergedTypeMapper`.
pub fn new_merged_type_mapper(
    c: &mut Checker,
    m1: TypeMapperId,
    m2: TypeMapperId,
) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::Merged(MergedTypeMapper { m1, m2 }),
    })
}

// CompositeTypeMapper

/// `type CompositeTypeMapper struct`. PORT: `c *Checker` is implicit — the
/// checker is passed into `TypeMapperArena::map`.
pub struct CompositeTypeMapper {
    /// `m1`.
    pub m1: TypeMapperId,
    /// `m2`.
    pub m2: TypeMapperId,
}

/// `newCompositeTypeMapper`.
pub fn new_composite_type_mapper(
    c: &mut Checker,
    m1: TypeMapperId,
    m2: TypeMapperId,
) -> TypeMapperId {
    c.type_mappers.alloc(TypeMapper {
        data: TypeMapperData::Composite(CompositeTypeMapper { m1, m2 }),
    })
}

// InferenceTypeMapper

/// `type InferenceTypeMapper struct`. PORT: `c *Checker` implicit;
/// `n *InferenceContext` → `InferenceContextId`.
pub struct InferenceTypeMapper {
    /// `n`.
    pub n: InferenceContextId,
    /// `fixing`.
    pub fixing: bool,
}
