// Ported from tsc/internal/pseudochecker/type.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `PseudoType`s are skeletons of types - partially interpreted expressions and type nodes
// composed to represent how you *should* construct a type out of them. They can be trivially
// mapped into actual types by a real `Checker`, or into a tree of `Node`s directly, without
// needing to make any intermediate types, by a `NodeBuilder`. Unlike checker `Type`s, these are
// never normalized, and multiple pseudo-types may refer to the same underlying `Type`.
//
// In strada, these were implicit in the AST nodes constructed in `expressionToTypeNode.ts`, which
// repurposed AST nodes for this purpose, but in so doing, often confused weather or not it had validated
// nested nodes for use at a given use-site. By keeping the mapping deferred like this, we can know we haven't
// done any use-site checks until we're ready to map the `PseudoType` into a `Node`, and can cache
// `PseudoType`s across multiple target positions.

// PORT: Go models `PseudoType` as a struct with a `Kind` field plus a
// `pseudoTypeData` interface payload, referenced via `*PseudoType`. Here it is
// a plain enum; `*PseudoType` becomes `Rc<PseudoType>` (`PseudoTypeRef`) since
// callers share sub-trees (e.g. `PseudoTypeUndefined` and union members).
// `*ast.Node` becomes `NodeId`, `*ast.TypeParameterDeclaration` becomes
// `NodeId` (the type parameter declaration node), and nil-able `*Node` fields
// become `Option<NodeId>`.

use std::rc::Rc;

use tsc_ast::ids::NodeId;

/// `*PseudoType` — a shared handle to a pseudo type.
pub type PseudoTypeRef = Rc<PseudoType>;

/// `type PseudoTypeKind int16`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PseudoTypeKind {
    /// `PseudoTypeKindDirect`.
    Direct,
    /// `PseudoTypeKindInferred`.
    Inferred,
    /// `PseudoTypeKindNoResult`.
    NoResult,
    /// `PseudoTypeKindMaybeConstLocation`.
    MaybeConstLocation,
    /// `PseudoTypeKindUnion`.
    Union,
    /// `PseudoTypeKindUndefined`.
    Undefined,
    /// `PseudoTypeKindNull`.
    Null,
    /// `PseudoTypeKindAny`.
    Any,
    /// `PseudoTypeKindString`.
    String,
    /// `PseudoTypeKindNumber`.
    Number,
    /// `PseudoTypeKindBigInt`.
    BigInt,
    /// `PseudoTypeKindBoolean`.
    Boolean,
    /// `PseudoTypeKindFalse`.
    False,
    /// `PseudoTypeKindTrue`.
    True,
    /// `PseudoTypeKindSingleCallSignature`.
    SingleCallSignature,
    /// `PseudoTypeKindTuple`.
    Tuple,
    /// `PseudoTypeKindObjectLiteral`.
    ObjectLiteral,
    /// `PseudoTypeKindStringLiteral`.
    StringLiteral,
    /// `PseudoTypeKindNumericLiteral`.
    NumericLiteral,
    /// `PseudoTypeKindBigIntLiteral`.
    BigIntLiteral,
}

/// `type PseudoType struct` — the Go struct-with-interface-data becomes a
/// plain enum whose variants carry the payload structs below.
#[derive(Debug)]
pub enum PseudoType {
    /// `PseudoTypeKindDirect` / `PseudoTypeDirect`.
    Direct(PseudoTypeDirect),
    /// `PseudoTypeKindInferred` / `PseudoTypeInferred`.
    Inferred(PseudoTypeInferred),
    /// `PseudoTypeKindNoResult` / `PseudoTypeNoResult`.
    NoResult(PseudoTypeNoResult),
    /// `PseudoTypeKindMaybeConstLocation` / `PseudoTypeMaybeConstLocation`.
    MaybeConstLocation(PseudoTypeMaybeConstLocation),
    /// `PseudoTypeKindUnion` / `PseudoTypeUnion`.
    Union(PseudoTypeUnion),
    /// `PseudoTypeKindUndefined`.
    Undefined,
    /// `PseudoTypeKindNull`.
    Null,
    /// `PseudoTypeKindAny`.
    Any,
    /// `PseudoTypeKindString`.
    String,
    /// `PseudoTypeKindNumber`.
    Number,
    /// `PseudoTypeKindBigInt`.
    BigInt,
    /// `PseudoTypeKindBoolean`.
    Boolean,
    /// `PseudoTypeKindFalse`.
    False,
    /// `PseudoTypeKindTrue`.
    True,
    /// `PseudoTypeKindSingleCallSignature` / `PseudoTypeSingleCallSignature`.
    SingleCallSignature(PseudoTypeSingleCallSignature),
    /// `PseudoTypeKindTuple` / `PseudoTypeTuple`.
    Tuple(PseudoTypeTuple),
    /// `PseudoTypeKindObjectLiteral` / `PseudoTypeObjectLiteral`.
    ObjectLiteral(PseudoTypeObjectLiteral),
    /// `PseudoTypeKindStringLiteral` / `PseudoTypeLiteral`.
    StringLiteral(PseudoTypeLiteral),
    /// `PseudoTypeKindNumericLiteral` / `PseudoTypeLiteral`.
    NumericLiteral(PseudoTypeLiteral),
    /// `PseudoTypeKindBigIntLiteral` / `PseudoTypeLiteral`.
    BigIntLiteral(PseudoTypeLiteral),
}

impl PseudoType {
    /// `t.Kind`.
    pub fn kind(&self) -> PseudoTypeKind {
        match self {
            PseudoType::Direct(_) => PseudoTypeKind::Direct,
            PseudoType::Inferred(_) => PseudoTypeKind::Inferred,
            PseudoType::NoResult(_) => PseudoTypeKind::NoResult,
            PseudoType::MaybeConstLocation(_) => PseudoTypeKind::MaybeConstLocation,
            PseudoType::Union(_) => PseudoTypeKind::Union,
            PseudoType::Undefined => PseudoTypeKind::Undefined,
            PseudoType::Null => PseudoTypeKind::Null,
            PseudoType::Any => PseudoTypeKind::Any,
            PseudoType::String => PseudoTypeKind::String,
            PseudoType::Number => PseudoTypeKind::Number,
            PseudoType::BigInt => PseudoTypeKind::BigInt,
            PseudoType::Boolean => PseudoTypeKind::Boolean,
            PseudoType::False => PseudoTypeKind::False,
            PseudoType::True => PseudoTypeKind::True,
            PseudoType::SingleCallSignature(_) => PseudoTypeKind::SingleCallSignature,
            PseudoType::Tuple(_) => PseudoTypeKind::Tuple,
            PseudoType::ObjectLiteral(_) => PseudoTypeKind::ObjectLiteral,
            PseudoType::StringLiteral(_) => PseudoTypeKind::StringLiteral,
            PseudoType::NumericLiteral(_) => PseudoTypeKind::NumericLiteral,
            PseudoType::BigIntLiteral(_) => PseudoTypeKind::BigIntLiteral,
        }
    }

    // PORT: the `As*` methods mirror Go's `t.data.(*X)` type assertions —
    // they panic on a mismatched kind, just like Go.

    /// `(t *PseudoType).AsPseudoTypeDirect`.
    pub fn as_pseudo_type_direct(&self) -> &PseudoTypeDirect {
        match self {
            PseudoType::Direct(d) => d,
            _ => panic!("as_pseudo_type_direct on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeInferred`.
    pub fn as_pseudo_type_inferred(&self) -> &PseudoTypeInferred {
        match self {
            PseudoType::Inferred(d) => d,
            _ => panic!("as_pseudo_type_inferred on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeNoResult`.
    pub fn as_pseudo_type_no_result(&self) -> &PseudoTypeNoResult {
        match self {
            PseudoType::NoResult(d) => d,
            _ => panic!("as_pseudo_type_no_result on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeMaybeConstLocation`.
    pub fn as_pseudo_type_maybe_const_location(&self) -> &PseudoTypeMaybeConstLocation {
        match self {
            PseudoType::MaybeConstLocation(d) => d,
            _ => panic!("as_pseudo_type_maybe_const_location on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeUnion`.
    pub fn as_pseudo_type_union(&self) -> &PseudoTypeUnion {
        match self {
            PseudoType::Union(d) => d,
            _ => panic!("as_pseudo_type_union on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeSingleCallSignature`.
    pub fn as_pseudo_type_single_call_signature(&self) -> &PseudoTypeSingleCallSignature {
        match self {
            PseudoType::SingleCallSignature(d) => d,
            _ => panic!("as_pseudo_type_single_call_signature on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeTuple`.
    pub fn as_pseudo_type_tuple(&self) -> &PseudoTypeTuple {
        match self {
            PseudoType::Tuple(d) => d,
            _ => panic!("as_pseudo_type_tuple on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeObjectLiteral`.
    pub fn as_pseudo_type_object_literal(&self) -> &PseudoTypeObjectLiteral {
        match self {
            PseudoType::ObjectLiteral(d) => d,
            _ => panic!("as_pseudo_type_object_literal on {:?}", self.kind()),
        }
    }

    /// `(t *PseudoType).AsPseudoTypeLiteral` — covers all three literal
    /// variants (`StringLiteral`, `NumericLiteral`, `BigIntLiteral`), all of
    /// which share `PseudoTypeLiteral` data in Go.
    pub fn as_pseudo_type_literal(&self) -> &PseudoTypeLiteral {
        match self {
            PseudoType::StringLiteral(d)
            | PseudoType::NumericLiteral(d)
            | PseudoType::BigIntLiteral(d) => d,
            _ => panic!("as_pseudo_type_literal on {:?}", self.kind()),
        }
    }
}

// Go's package-level singletons (`PseudoTypeUndefined`, ...). `Rc` is `!Sync`,
// so they live in `thread_local!` storage — Go's process-wide globals also
// rely on the values being immutable after construction.
thread_local! {
    static PSEUDO_TYPE_UNDEFINED: PseudoTypeRef = Rc::new(PseudoType::Undefined);
    static PSEUDO_TYPE_NULL: PseudoTypeRef = Rc::new(PseudoType::Null);
    static PSEUDO_TYPE_ANY: PseudoTypeRef = Rc::new(PseudoType::Any);
    static PSEUDO_TYPE_STRING: PseudoTypeRef = Rc::new(PseudoType::String);
    static PSEUDO_TYPE_NUMBER: PseudoTypeRef = Rc::new(PseudoType::Number);
    static PSEUDO_TYPE_BIG_INT: PseudoTypeRef = Rc::new(PseudoType::BigInt);
    static PSEUDO_TYPE_BOOLEAN: PseudoTypeRef = Rc::new(PseudoType::Boolean);
    static PSEUDO_TYPE_FALSE: PseudoTypeRef = Rc::new(PseudoType::False);
    static PSEUDO_TYPE_TRUE: PseudoTypeRef = Rc::new(PseudoType::True);
}

/// `PseudoTypeUndefined`.
pub fn pseudo_type_undefined() -> PseudoTypeRef {
    PSEUDO_TYPE_UNDEFINED.with(Rc::clone)
}

/// `PseudoTypeNull`.
pub fn pseudo_type_null() -> PseudoTypeRef {
    PSEUDO_TYPE_NULL.with(Rc::clone)
}

/// `PseudoTypeAny`.
pub fn pseudo_type_any() -> PseudoTypeRef {
    PSEUDO_TYPE_ANY.with(Rc::clone)
}

/// `PseudoTypeString`.
pub fn pseudo_type_string() -> PseudoTypeRef {
    PSEUDO_TYPE_STRING.with(Rc::clone)
}

/// `PseudoTypeNumber`.
pub fn pseudo_type_number() -> PseudoTypeRef {
    PSEUDO_TYPE_NUMBER.with(Rc::clone)
}

/// `PseudoTypeBigInt`.
pub fn pseudo_type_big_int() -> PseudoTypeRef {
    PSEUDO_TYPE_BIG_INT.with(Rc::clone)
}

/// `PseudoTypeBoolean`.
pub fn pseudo_type_boolean() -> PseudoTypeRef {
    PSEUDO_TYPE_BOOLEAN.with(Rc::clone)
}

/// `PseudoTypeFalse`.
pub fn pseudo_type_false() -> PseudoTypeRef {
    PSEUDO_TYPE_FALSE.with(Rc::clone)
}

/// `PseudoTypeTrue`.
pub fn pseudo_type_true() -> PseudoTypeRef {
    PSEUDO_TYPE_TRUE.with(Rc::clone)
}

/// `type PseudoTypeDirect struct` — directly encodes the type referred to by
/// a given TypeNode.
#[derive(Debug)]
pub struct PseudoTypeDirect {
    /// `TypeNode`.
    pub type_node: NodeId,
}

/// `NewPseudoTypeDirect(typeNode)`.
pub fn new_pseudo_type_direct(type_node: NodeId) -> PseudoTypeRef {
    Rc::new(PseudoType::Direct(PseudoTypeDirect { type_node }))
}

/// `type PseudoTypeInferred struct` — directly encodes the type referred to by
/// a given Expression.
///
/// These represent cases where the expression was too complex for the
/// pseudochecker. Most of the time, these locations will produce an error
/// under ID. Specific error nodes (shorthand properties, spread assignments,
/// etc.) are stored on the `error_nodes` field, collected during
/// pseudochecker construction.
#[derive(Debug)]
pub struct PseudoTypeInferred {
    /// `Expression`.
    pub expression: NodeId,
    /// `ErrorNodes`.
    pub error_nodes: Vec<NodeId>,
    /// `IsSignatureReturn`.
    pub is_signature_return: bool,
}

/// `NewPseudoTypeInferred(expr, isSignatureReturn)`.
pub fn new_pseudo_type_inferred(expr: NodeId, is_signature_return: bool) -> PseudoTypeRef {
    Rc::new(PseudoType::Inferred(PseudoTypeInferred {
        expression: expr,
        error_nodes: Vec::new(),
        is_signature_return,
    }))
}

/// `NewPseudoTypeInferredWithErrors(expr, isSignatureReturn, errorNodes)`.
pub fn new_pseudo_type_inferred_with_errors(
    expr: NodeId,
    is_signature_return: bool,
    error_nodes: Vec<NodeId>,
) -> PseudoTypeRef {
    Rc::new(PseudoType::Inferred(PseudoTypeInferred {
        expression: expr,
        error_nodes,
        is_signature_return,
    }))
}

/// `type PseudoTypeNoResult struct` — analogous to `PseudoTypeInferred` in
/// that it references a case where the type was too complex for the
/// pseudochecker. Rather than an expression, however, it is referring to the
/// return type of a signature or declaration.
#[derive(Debug)]
pub struct PseudoTypeNoResult {
    /// `Declaration`.
    pub declaration: NodeId,
}

/// `NewPseudoTypeNoResult(decl)`.
pub fn new_pseudo_type_no_result(decl: NodeId) -> PseudoTypeRef {
    Rc::new(PseudoType::NoResult(PseudoTypeNoResult {
        declaration: decl,
    }))
}

/// `type PseudoTypeMaybeConstLocation struct` — encodes the const/regular
/// types of a location so the builder can later select the appropriate
/// pseudotype based on the location's context. This is used to ensure accuracy
/// in nested expressions without exposing type-based functionality to the
/// pseudochecker.
///
/// A nodebuilder that doesn't do contextual typing would need to, as policy,
/// reject these types if they are in a contextually typed position! (Otherwise
/// they could pick one, but either type could be wrong, depending on context!)
/// At the top-level, which is generally what ID is concerned with, nothing is
/// contextually typed, so these cases don't generally cause problems. Once you
/// get into reused nodes in nested expressions, however, this becomes
/// important. In strada, checker `isConstContext` functionality exposed to the
/// pseudochecker + type comparison sanity checking on nested results masks the
/// need for this abstraction, but with it present it clearly highlights a
/// shortcoming of the ID infernce model and how "standalone" it can(n't) truly
/// be without substantial restrictions on expression inference.
#[derive(Debug)]
pub struct PseudoTypeMaybeConstLocation {
    /// `Node`.
    pub node: NodeId,
    /// `ConstType`.
    pub const_type: PseudoTypeRef,
    /// `RegularType`.
    pub regular_type: PseudoTypeRef,
}

/// `NewPseudoTypeMaybeConstLocation(loc, ct, reg)`.
pub fn new_pseudo_type_maybe_const_location(
    loc: NodeId,
    ct: PseudoTypeRef,
    reg: PseudoTypeRef,
) -> PseudoTypeRef {
    Rc::new(PseudoType::MaybeConstLocation(
        PseudoTypeMaybeConstLocation {
            node: loc,
            const_type: ct,
            regular_type: reg,
        },
    ))
}

/// `type PseudoTypeUnion struct` — a collection of pseudotypes joined into a
/// union.
#[derive(Debug)]
pub struct PseudoTypeUnion {
    /// `Types`.
    pub types: Vec<PseudoTypeRef>,
}

/// `NewPseudoTypeUnion(types)`.
pub fn new_pseudo_type_union(types: Vec<PseudoTypeRef>) -> PseudoTypeRef {
    Rc::new(PseudoType::Union(PseudoTypeUnion { types }))
}

/// `type PseudoParameter struct`.
#[derive(Debug)]
pub struct PseudoParameter {
    /// `Rest`.
    pub rest: bool,
    /// `Name`.
    pub name: Option<NodeId>,
    /// `Optional`.
    pub optional: bool,
    /// `Type`.
    pub type_: PseudoTypeRef,
}

/// `NewPseudoParameter(isRest, name, isOptional, t)`.
pub fn new_pseudo_parameter(
    is_rest: bool,
    name: Option<NodeId>,
    is_optional: bool,
    t: PseudoTypeRef,
) -> PseudoParameter {
    PseudoParameter {
        rest: is_rest,
        name,
        optional: is_optional,
        type_: t,
    }
}

/// `type PseudoTypeSingleCallSignature struct` — represents an object type
/// with a single call signature, like an arrow or function expression.
#[derive(Debug)]
pub struct PseudoTypeSingleCallSignature {
    /// `Signature`.
    pub signature: NodeId,
    /// `Parameters`.
    pub parameters: Vec<PseudoParameter>,
    /// `TypeParameters` — `[]*ast.TypeParameterDeclaration` in Go; the
    /// `TypeParameterDeclaration` node ids here.
    pub type_parameters: Vec<NodeId>,
    /// `ReturnType`.
    pub return_type: PseudoTypeRef,
}

/// `NewPseudoTypeSingleCallSignature(signature, parameters, typeParameters, returnType)`.
pub fn new_pseudo_type_single_call_signature(
    signature: NodeId,
    parameters: Vec<PseudoParameter>,
    type_parameters: Vec<NodeId>,
    return_type: PseudoTypeRef,
) -> PseudoTypeRef {
    Rc::new(PseudoType::SingleCallSignature(
        PseudoTypeSingleCallSignature {
            signature,
            parameters,
            type_parameters,
            return_type,
        },
    ))
}

/// `type PseudoTypeTuple struct` — represents a tuple originating from an
/// `as const` array literal.
#[derive(Debug)]
pub struct PseudoTypeTuple {
    /// `Elements`.
    pub elements: Vec<PseudoTypeRef>,
}

/// `NewPseudoTypeTuple(elements)`.
pub fn new_pseudo_type_tuple(elements: Vec<PseudoTypeRef>) -> PseudoTypeRef {
    Rc::new(PseudoType::Tuple(PseudoTypeTuple { elements }))
}

/// `type PseudoObjectElementKind int8`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PseudoObjectElementKind {
    /// `PseudoObjectElementKindMethod`.
    Method,
    /// `PseudoObjectElementKindPropertyAssignment`.
    PropertyAssignment,
    /// `PseudoObjectElementKindSetAccessor`.
    SetAccessor,
    /// `PseudoObjectElementKindGetAccessor`.
    GetAccessor,
}

/// `type PseudoObjectElement struct` — Go's `data pseudoObjectElementData`
/// interface becomes the `PseudoObjectElementData` enum.
#[derive(Debug)]
pub struct PseudoObjectElement {
    /// `Name`.
    pub name: Option<NodeId>,
    /// `Optional`.
    pub optional: bool,
    /// `data`.
    pub data: PseudoObjectElementData,
}

/// `pseudoObjectElementData` — the Go interface, as an enum.
#[derive(Debug)]
pub enum PseudoObjectElementData {
    /// `PseudoObjectMethod`.
    Method(PseudoObjectMethod),
    /// `PseudoPropertyAssignment`.
    PropertyAssignment(PseudoPropertyAssignment),
    /// `PseudoSetAccessor`.
    SetAccessor(PseudoSetAccessor),
    /// `PseudoGetAccessor`.
    GetAccessor(PseudoGetAccessor),
}

impl PseudoObjectElement {
    /// `e.Kind`.
    pub fn kind(&self) -> PseudoObjectElementKind {
        match self.data {
            PseudoObjectElementData::Method(_) => PseudoObjectElementKind::Method,
            PseudoObjectElementData::PropertyAssignment(_) => {
                PseudoObjectElementKind::PropertyAssignment
            }
            PseudoObjectElementData::SetAccessor(_) => PseudoObjectElementKind::SetAccessor,
            PseudoObjectElementData::GetAccessor(_) => PseudoObjectElementKind::GetAccessor,
        }
    }

    /// `(e *PseudoObjectElement).Signature`.
    pub fn signature(&self) -> Option<NodeId> {
        match &self.data {
            PseudoObjectElementData::Method(m) => Some(m.signature),
            PseudoObjectElementData::SetAccessor(s) => Some(s.signature),
            PseudoObjectElementData::GetAccessor(g) => Some(g.signature),
            _ => None,
        }
    }

    /// `(e *PseudoObjectElement).AsPseudoObjectMethod` — panics on mismatch,
    /// like Go's type assertion.
    pub fn as_pseudo_object_method(&self) -> &PseudoObjectMethod {
        match &self.data {
            PseudoObjectElementData::Method(m) => m,
            _ => panic!("as_pseudo_object_method on {:?}", self.kind()),
        }
    }

    /// `(e *PseudoObjectElement).AsPseudoPropertyAssignment`.
    pub fn as_pseudo_property_assignment(&self) -> &PseudoPropertyAssignment {
        match &self.data {
            PseudoObjectElementData::PropertyAssignment(p) => p,
            _ => panic!("as_pseudo_property_assignment on {:?}", self.kind()),
        }
    }

    /// `(e *PseudoObjectElement).AsPseudoSetAccessor`.
    pub fn as_pseudo_set_accessor(&self) -> &PseudoSetAccessor {
        match &self.data {
            PseudoObjectElementData::SetAccessor(s) => s,
            _ => panic!("as_pseudo_set_accessor on {:?}", self.kind()),
        }
    }

    /// `(e *PseudoObjectElement).AsPseudoGetAccessor`.
    pub fn as_pseudo_get_accessor(&self) -> &PseudoGetAccessor {
        match &self.data {
            PseudoObjectElementData::GetAccessor(g) => g,
            _ => panic!("as_pseudo_get_accessor on {:?}", self.kind()),
        }
    }
}

/// `type PseudoObjectMethod struct`.
#[derive(Debug)]
pub struct PseudoObjectMethod {
    /// `Signature`.
    pub signature: NodeId,
    /// `TypeParameters` — `[]*ast.TypeParameterDeclaration` in Go.
    pub type_parameters: Vec<NodeId>,
    /// `Parameters`.
    pub parameters: Vec<PseudoParameter>,
    /// `ReturnType`.
    pub return_type: PseudoTypeRef,
}

/// `NewPseudoObjectMethod(signature, name, optional, typeParameters, parameters, returnType)`.
pub fn new_pseudo_object_method(
    signature: NodeId,
    name: Option<NodeId>,
    optional: bool,
    type_parameters: Vec<NodeId>,
    parameters: Vec<PseudoParameter>,
    return_type: PseudoTypeRef,
) -> PseudoObjectElement {
    PseudoObjectElement {
        name,
        optional,
        data: PseudoObjectElementData::Method(PseudoObjectMethod {
            signature,
            type_parameters,
            parameters,
            return_type,
        }),
    }
}

/// `type PseudoPropertyAssignment struct`.
#[derive(Debug)]
pub struct PseudoPropertyAssignment {
    /// `Readonly`.
    pub readonly: bool,
    /// `Type`.
    pub type_: PseudoTypeRef,
}

/// `NewPseudoPropertyAssignment(readonly, name, optional, t)`.
pub fn new_pseudo_property_assignment(
    readonly: bool,
    name: Option<NodeId>,
    optional: bool,
    t: PseudoTypeRef,
) -> PseudoObjectElement {
    PseudoObjectElement {
        name,
        optional,
        data: PseudoObjectElementData::PropertyAssignment(PseudoPropertyAssignment {
            readonly,
            type_: t,
        }),
    }
}

/// `type PseudoSetAccessor struct`.
#[derive(Debug)]
pub struct PseudoSetAccessor {
    /// `Signature`.
    pub signature: NodeId,
    /// `Parameter`.
    pub parameter: PseudoParameter,
}

/// `NewPseudoSetAccessor(signature, name, optional, p)`.
pub fn new_pseudo_set_accessor(
    signature: NodeId,
    name: Option<NodeId>,
    optional: bool,
    p: PseudoParameter,
) -> PseudoObjectElement {
    PseudoObjectElement {
        name,
        optional,
        data: PseudoObjectElementData::SetAccessor(PseudoSetAccessor {
            signature,
            parameter: p,
        }),
    }
}

/// `type PseudoGetAccessor struct`.
#[derive(Debug)]
pub struct PseudoGetAccessor {
    /// `Signature`.
    pub signature: NodeId,
    /// `Type`.
    pub type_: PseudoTypeRef,
}

/// `NewPseudoGetAccessor(signature, name, optional, t)`.
pub fn new_pseudo_get_accessor(
    signature: NodeId,
    name: Option<NodeId>,
    optional: bool,
    t: PseudoTypeRef,
) -> PseudoObjectElement {
    PseudoObjectElement {
        name,
        optional,
        data: PseudoObjectElementData::GetAccessor(PseudoGetAccessor {
            signature,
            type_: t,
        }),
    }
}

/// `type PseudoTypeObjectLiteral struct` — represents an object type
/// originating from an object literal.
#[derive(Debug)]
pub struct PseudoTypeObjectLiteral {
    /// `Elements`.
    pub elements: Vec<PseudoObjectElement>,
}

/// `NewPseudoTypeObjectLiteral(elements)`.
pub fn new_pseudo_type_object_literal(elements: Vec<PseudoObjectElement>) -> PseudoTypeRef {
    Rc::new(PseudoType::ObjectLiteral(PseudoTypeObjectLiteral {
        elements,
    }))
}

/// `type PseudoTypeLiteral struct` — represents a literal type.
#[derive(Debug)]
pub struct PseudoTypeLiteral {
    /// `Node`.
    pub node: NodeId,
}

/// `NewPseudoTypeStringLiteral(node)`.
pub fn new_pseudo_type_string_literal(node: NodeId) -> PseudoTypeRef {
    Rc::new(PseudoType::StringLiteral(PseudoTypeLiteral { node }))
}

/// `NewPseudoTypeNumericLiteral(node)`.
pub fn new_pseudo_type_numeric_literal(node: NodeId) -> PseudoTypeRef {
    Rc::new(PseudoType::NumericLiteral(PseudoTypeLiteral { node }))
}

/// `NewPseudoTypeBigIntLiteral(node)`.
pub fn new_pseudo_type_big_int_literal(node: NodeId) -> PseudoTypeRef {
    Rc::new(PseudoType::BigIntLiteral(PseudoTypeLiteral { node }))
}
