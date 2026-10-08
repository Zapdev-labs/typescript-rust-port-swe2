// Ported from tsc/internal/ast/subtreefacts.go + the hand-written
// `computeSubtreeFacts`/`propagateSubtreeFacts` bodies in
// tsc/internal/ast/ast.go @ ec47d33c23e464a17cdf2475632cba629bee8763.
//
// `SubtreeFacts` is a bitmask cached on `CompositeBase` nodes that records
// whether a subtree contains syntax relevant to a specific transform, plus
// scope-marker bits (e.g. lexical `this`/`super`) that are filtered out as
// they propagate across certain node boundaries (`SubtreeExclusions*`).
//
// Layout notes for the Rust port:
//   - The generator emits the trivial compute bodies (pure propagations of
//     child fields) inline in ast_generated.rs; every non-trivial Go body is
//     reimplemented here as `compute_<node>` and dispatched from
//     `NodeData::subtree_facts`.
//   - `propagateSubtreeFacts` overrides that are just
//     `self &^ exclusions` are generated; the only propagation terms appended
//     to exclusions (e.g. `| propagateSubtreeFacts(node.name)` on methods)
//     are handled through `propagate_fields` in the schema.

use crate::ast::{ModifierList, Node, NodeList};
use crate::ast_generated::{
    is_external_module_reference, is_identifier, is_private_identifier,
    propagate_subtree_facts, propagate_subtree_facts_opt,
};
use crate::ids::NodeId;
use crate::kind_generated::Kind;
use crate::modifierflags::ModifierFlags;
use crate::nodeflags::NodeFlags;
use crate::tokenflags::TokenFlags;
use crate::flagdef::flag_type;

flag_type! {
    /// `type SubtreeFacts uint32` — see subtreefacts.go for the semantics of
    /// each bit.
    pub struct SubtreeFacts(pub u32);
}

impl SubtreeFacts {
    // Facts — syntax relevant to a specific transform.
    pub const CONTAINS_TYPE_SCRIPT: SubtreeFacts = SubtreeFacts(1 << 0);
    pub const CONTAINS_JSX: SubtreeFacts = SubtreeFacts(1 << 1);
    pub const CONTAINS_ES_DECORATORS: SubtreeFacts = SubtreeFacts(1 << 2);
    pub const CONTAINS_USING: SubtreeFacts = SubtreeFacts(1 << 3);
    pub const CONTAINS_CLASS_STATIC_BLOCKS: SubtreeFacts = SubtreeFacts(1 << 4);
    pub const CONTAINS_ES_CLASS_FIELDS: SubtreeFacts = SubtreeFacts(1 << 5);
    pub const CONTAINS_LOGICAL_ASSIGNMENTS: SubtreeFacts = SubtreeFacts(1 << 6);
    pub const CONTAINS_NULLISH_COALESCING: SubtreeFacts = SubtreeFacts(1 << 7);
    pub const CONTAINS_OPTIONAL_CHAINING: SubtreeFacts = SubtreeFacts(1 << 8);
    pub const CONTAINS_MISSING_CATCH_CLAUSE_VARIABLE: SubtreeFacts = SubtreeFacts(1 << 9);
    pub const CONTAINS_ES_OBJECT_REST_OR_SPREAD: SubtreeFacts = SubtreeFacts(1 << 10);
    pub const CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR: SubtreeFacts = SubtreeFacts(1 << 11);
    pub const CONTAINS_ANY_AWAIT: SubtreeFacts = SubtreeFacts(1 << 12);
    pub const CONTAINS_EXPONENTIATION_OPERATOR: SubtreeFacts = SubtreeFacts(1 << 13);

    // Markers — a particular kind of syntax.
    pub const CONTAINS_LEXICAL_THIS: SubtreeFacts = SubtreeFacts(1 << 14);
    pub const CONTAINS_LEXICAL_SUPER: SubtreeFacts = SubtreeFacts(1 << 15);
    /// marker on any `...` — cleared on binding pattern exit
    pub const CONTAINS_REST_OR_SPREAD: SubtreeFacts = SubtreeFacts(1 << 16);
    /// marker on any `{...x}` — cleared on most scope exits
    pub const CONTAINS_OBJECT_REST_OR_SPREAD: SubtreeFacts = SubtreeFacts(1 << 17);
    pub const CONTAINS_AWAIT: SubtreeFacts = SubtreeFacts(1 << 18);
    pub const CONTAINS_DYNAMIC_IMPORT: SubtreeFacts = SubtreeFacts(1 << 19);
    pub const CONTAINS_CLASS_FIELDS: SubtreeFacts = SubtreeFacts(1 << 20);
    pub const CONTAINS_DECORATORS: SubtreeFacts = SubtreeFacts(1 << 21);
    pub const CONTAINS_IDENTIFIER: SubtreeFacts = SubtreeFacts(1 << 22);
    pub const CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION: SubtreeFacts = SubtreeFacts(1 << 23);
    pub const CONTAINS_INVALID_TEMPLATE_ESCAPE: SubtreeFacts = SubtreeFacts(1 << 24);

    /// NOTE: must always be last (mirrors Go's comment).
    pub const COMPUTED: SubtreeFacts = SubtreeFacts(1 << 25);

    // Aliases — combinations used by transformers; kept for parity.
    pub const CONTAINS_ES_NEXT: SubtreeFacts =
        Self(Self::CONTAINS_ES_DECORATORS.0 | Self::CONTAINS_USING.0);
    pub const CONTAINS_ES_2022: SubtreeFacts =
        Self(Self::CONTAINS_CLASS_STATIC_BLOCKS.0 | Self::CONTAINS_ES_CLASS_FIELDS.0);
    pub const CONTAINS_ES_2021: SubtreeFacts = Self::CONTAINS_LOGICAL_ASSIGNMENTS;
    pub const CONTAINS_ES_2020: SubtreeFacts =
        Self(Self::CONTAINS_NULLISH_COALESCING.0 | Self::CONTAINS_OPTIONAL_CHAINING.0);
    pub const CONTAINS_ES_2019: SubtreeFacts = Self::CONTAINS_MISSING_CATCH_CLAUSE_VARIABLE;
    pub const CONTAINS_ES_2018: SubtreeFacts = Self(
        Self::CONTAINS_ES_OBJECT_REST_OR_SPREAD.0
            | Self::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR.0
            | Self::CONTAINS_INVALID_TEMPLATE_ESCAPE.0,
    );
    pub const CONTAINS_ES_2017: SubtreeFacts = Self::CONTAINS_ANY_AWAIT;
    pub const CONTAINS_ES_2016: SubtreeFacts = Self::CONTAINS_EXPONENTIATION_OPERATOR;

    // Scope exclusions — bits filtered out as facts propagate past a node.
    pub const EXCLUSIONS_NODE: SubtreeFacts = Self::COMPUTED;
    /// `^SubtreeContainsTypeScript` — a full bitwise complement, not a mask.
    pub const EXCLUSIONS_ERASEABLE: SubtreeFacts = SubtreeFacts(!Self::CONTAINS_TYPE_SCRIPT.0);
    pub const EXCLUSIONS_OUTER_EXPRESSION: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_PROPERTY_ACCESS: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_ELEMENT_ACCESS: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_ARROW_FUNCTION: SubtreeFacts = Self(
        Self::EXCLUSIONS_NODE.0
            | Self::CONTAINS_AWAIT.0
            | Self::CONTAINS_OBJECT_REST_OR_SPREAD.0,
    );
    pub const EXCLUSIONS_FUNCTION: SubtreeFacts = Self(
        Self::EXCLUSIONS_NODE.0
            | Self::CONTAINS_LEXICAL_THIS.0
            | Self::CONTAINS_LEXICAL_SUPER.0
            | Self::CONTAINS_AWAIT.0
            | Self::CONTAINS_OBJECT_REST_OR_SPREAD.0,
    );
    pub const EXCLUSIONS_CONSTRUCTOR: SubtreeFacts = Self::EXCLUSIONS_FUNCTION;
    pub const EXCLUSIONS_METHOD: SubtreeFacts = Self::EXCLUSIONS_FUNCTION;
    pub const EXCLUSIONS_ACCESSOR: SubtreeFacts = Self::EXCLUSIONS_FUNCTION;
    pub const EXCLUSIONS_PROPERTY: SubtreeFacts = Self(
        Self::EXCLUSIONS_NODE.0
            | Self::CONTAINS_LEXICAL_THIS.0
            | Self::CONTAINS_LEXICAL_SUPER.0,
    );
    pub const EXCLUSIONS_CLASS: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_MODULE: SubtreeFacts = Self(
        Self::EXCLUSIONS_NODE.0
            | Self::CONTAINS_LEXICAL_THIS.0
            | Self::CONTAINS_LEXICAL_SUPER.0,
    );
    pub const EXCLUSIONS_OBJECT_LITERAL: SubtreeFacts =
        Self(Self::EXCLUSIONS_NODE.0 | Self::CONTAINS_OBJECT_REST_OR_SPREAD.0);
    pub const EXCLUSIONS_ARRAY_LITERAL: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_CALL: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_NEW: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_VARIABLE_DECLARATION_LIST: SubtreeFacts =
        Self(Self::EXCLUSIONS_NODE.0 | Self::CONTAINS_OBJECT_REST_OR_SPREAD.0);
    pub const EXCLUSIONS_PARAMETER: SubtreeFacts = Self::EXCLUSIONS_NODE;
    pub const EXCLUSIONS_CATCH_CLAUSE: SubtreeFacts =
        Self(Self::EXCLUSIONS_NODE.0 | Self::CONTAINS_OBJECT_REST_OR_SPREAD.0);
    pub const EXCLUSIONS_BINDING_PATTERN: SubtreeFacts =
        Self(Self::EXCLUSIONS_NODE.0 | Self::CONTAINS_REST_OR_SPREAD.0);

    // Mask.
    pub const CONTAINS_LEXICAL_THIS_OR_SUPER: SubtreeFacts =
        Self(Self::CONTAINS_LEXICAL_THIS.0 | Self::CONTAINS_LEXICAL_SUPER.0);
}

// ── propagation helpers ─────────────────────────────────────────────────

#[inline]
fn prop(nodes: &[Node], child: Option<NodeId>) -> SubtreeFacts {
    propagate_subtree_facts_opt(nodes, child)
}

#[inline]
fn prop_list(nodes: &[Node], children: Option<&NodeList>) -> SubtreeFacts {
    let Some(children) = children else {
        return SubtreeFacts::NONE;
    };
    let mut facts = SubtreeFacts::NONE;
    for &c in children.nodes.iter() {
        facts |= propagate_subtree_facts(nodes, c);
    }
    facts
}

#[inline]
fn prop_modifiers(nodes: &[Node], modifiers: Option<&ModifierList>) -> SubtreeFacts {
    let Some(modifiers) = modifiers else {
        return SubtreeFacts::NONE;
    };
    let mut facts = SubtreeFacts::NONE;
    for &c in modifiers.nodes.iter() {
        facts |= propagate_subtree_facts(nodes, c);
    }
    facts
}

/// `propagateEraseableSyntaxSubtreeFacts(child)` — a present type-annotated
/// child contributes `SubtreeContainsTypeScript`.
#[inline]
fn eraseable(child: Option<NodeId>) -> SubtreeFacts {
    if child.is_some() {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        SubtreeFacts::NONE
    }
}

/// `propagateEraseableSyntaxListSubtreeFacts(children)`.
#[inline]
fn eraseable_list(children: Option<&NodeList>) -> SubtreeFacts {
    if children.is_some() {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        SubtreeFacts::NONE
    }
}

/// `propagateObjectBindingElementSubtreeFacts`.
fn prop_object_binding_element(nodes: &[Node], child: NodeId) -> SubtreeFacts {
    let mut facts = propagate_subtree_facts(nodes, child);
    if facts.intersects(SubtreeFacts::CONTAINS_REST_OR_SPREAD) {
        facts.remove(SubtreeFacts::CONTAINS_REST_OR_SPREAD);
        facts |= SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
            | SubtreeFacts::CONTAINS_ES_OBJECT_REST_OR_SPREAD;
    }
    facts
}

/// `propagateBindingElementSubtreeFacts`.
fn prop_binding_element(nodes: &[Node], child: NodeId) -> SubtreeFacts {
    propagate_subtree_facts(nodes, child).without(SubtreeFacts::CONTAINS_REST_OR_SPREAD)
}

fn prop_list_with(
    nodes: &[Node],
    children: Option<&NodeList>,
    propagate: fn(&[Node], NodeId) -> SubtreeFacts,
) -> SubtreeFacts {
    let Some(children) = children else {
        return SubtreeFacts::NONE;
    };
    let mut facts = SubtreeFacts::NONE;
    for &c in children.nodes.iter() {
        facts |= propagate(nodes, c);
    }
    facts
}

// ── hand-ported computeSubtreeFacts bodies ──────────────────────────────
// Each function mirrors the Go method of the same node type in ast.go. The
// `node` parameter is the `Node` header; fields are read off the generated
// `as_*` accessor.

/// `(node *Token) computeSubtreeFacts` — kind-switch facts for token nodes.
pub fn compute_token(node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    match node.kind {
        Kind::UsingKeyword => SubtreeFacts::CONTAINS_USING,
        Kind::PublicKeyword
        | Kind::PrivateKeyword
        | Kind::ProtectedKeyword
        | Kind::ReadonlyKeyword
        | Kind::AbstractKeyword
        | Kind::DeclareKeyword
        | Kind::ConstKeyword
        | Kind::AnyKeyword
        | Kind::NumberKeyword
        | Kind::BigIntKeyword
        | Kind::NeverKeyword
        | Kind::ObjectKeyword
        | Kind::InKeyword
        | Kind::OutKeyword
        | Kind::OverrideKeyword
        | Kind::StringKeyword
        | Kind::BooleanKeyword
        | Kind::SymbolKeyword
        | Kind::VoidKeyword
        | Kind::UnknownKeyword
        | Kind::UndefinedKeyword
        | Kind::ExportKeyword => SubtreeFacts::CONTAINS_TYPE_SCRIPT,
        Kind::AccessorKeyword => SubtreeFacts::CONTAINS_CLASS_FIELDS,
        Kind::AsyncKeyword => SubtreeFacts::CONTAINS_ANY_AWAIT,
        Kind::SuperKeyword => SubtreeFacts::CONTAINS_LEXICAL_SUPER,
        Kind::ThisKeyword => SubtreeFacts::CONTAINS_LEXICAL_THIS,
        Kind::AsteriskAsteriskToken | Kind::AsteriskAsteriskEqualsToken => {
            SubtreeFacts::CONTAINS_EXPONENTIATION_OPERATOR
        }
        Kind::QuestionQuestionToken => SubtreeFacts::CONTAINS_NULLISH_COALESCING,
        Kind::QuestionDotToken => SubtreeFacts::CONTAINS_OPTIONAL_CHAINING,
        Kind::QuestionQuestionEqualsToken
        | Kind::BarBarEqualsToken
        | Kind::AmpersandAmpersandEqualsToken => {
            SubtreeFacts::CONTAINS_LOGICAL_ASSIGNMENTS
        }
        _ => SubtreeFacts::NONE,
    }
}

pub fn compute_private_identifier(_node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    SubtreeFacts::CONTAINS_CLASS_FIELDS
}

pub fn compute_decorator(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_decorator();
    prop(nodes, d.expression)
        | SubtreeFacts::CONTAINS_TYPE_SCRIPT
        | SubtreeFacts::CONTAINS_DECORATORS
}

pub fn compute_for_in_or_of_statement(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_for_in_or_of_statement();
    prop(nodes, d.initializer)
        | prop(nodes, d.expression)
        | prop(nodes, d.statement)
        | if d.await_modifier.is_some() {
            SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_return_statement(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    // `return` in an ES2018 async generator must be awaited.
    prop(nodes, node.as_return_statement().expression)
        | SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
}

pub fn compute_catch_clause(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_catch_clause();
    let mut res = prop(nodes, d.variable_declaration) | prop(nodes, d.block);
    if d.variable_declaration.is_none() {
        res |= SubtreeFacts::CONTAINS_MISSING_CATCH_CLAUSE_VARIABLE;
    }
    res
}

pub fn compute_variable_statement(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_variable_statement();
    if node
        .modifiers()
        .is_some_and(|m| m.modifier_flags.intersects(ModifierFlags::AMBIENT))
    {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, node.modifiers()) | prop(nodes, d.declaration_list)
    }
}

pub fn compute_variable_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_variable_declaration();
    prop(nodes, d.name)
        | eraseable(d.exclamation_token)
        | eraseable(d.type_)
        | prop(nodes, d.initializer)
}

pub fn compute_variable_declaration_list(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_variable_declaration_list();
    prop_list(nodes, d.declarations.as_ref())
        | if node.flags.intersects(NodeFlags::USING) {
            SubtreeFacts::CONTAINS_USING
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_binding_pattern(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_binding_pattern();
    match node.kind {
        Kind::ObjectBindingPattern => {
            prop_list_with(nodes, d.elements.as_ref(), prop_object_binding_element)
        }
        Kind::ArrayBindingPattern => {
            prop_list_with(nodes, d.elements.as_ref(), prop_binding_element)
        }
        _ => SubtreeFacts::NONE,
    }
}

pub fn compute_parameter_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_parameter_declaration();
    if let Some(name) = d.name
        && crate::utilities::is_this_identifier(&nodes[name])
    {
        return SubtreeFacts::CONTAINS_TYPE_SCRIPT;
    }
    prop_modifiers(nodes, node.modifiers())
        | prop(nodes, d.name)
        | eraseable(d.question_token)
        | eraseable(d.type_)
        | prop(nodes, d.initializer)
}

pub fn compute_binding_element(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_binding_element();
    prop(nodes, d.property_name)
        | prop(nodes, d.name)
        | prop(nodes, d.initializer)
        | if d.dot_dot_dot_token.is_some() {
            SubtreeFacts::CONTAINS_REST_OR_SPREAD
        } else {
            SubtreeFacts::NONE
        }
}

/// Shared helper for function-like computes with bodies — fields are read
/// through `FunctionLikeWithBodyBase`.
fn compute_function_like_with_body(
    modifiers: Option<&ModifierList>,
    asterisk_token: Option<NodeId>,
    name: Option<NodeId>,
    fl: &crate::ast_generated::FunctionLikeWithBodyBase,
    nodes: &[Node],
) -> SubtreeFacts {
    let is_async = modifiers.is_some_and(|m| m.modifier_flags.intersects(ModifierFlags::ASYNC));
    let is_generator = asterisk_token.is_some();
    prop_modifiers(nodes, modifiers)
        | prop(nodes, asterisk_token)
        | prop(nodes, name)
        | eraseable_list(fl.function_like_base.type_parameters.as_ref())
        | prop_list(nodes, fl.function_like_base.parameters.as_ref())
        | eraseable(fl.function_like_base.type_)
        | eraseable(fl.function_like_base.full_signature)
        | prop(nodes, fl.body_base.body)
        | if is_async && is_generator {
            SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
        } else {
            SubtreeFacts::NONE
        }
        | if is_async && !is_generator {
            SubtreeFacts::CONTAINS_ANY_AWAIT
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_function_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_function_declaration();
    if d.function_like_with_body_base.body_base.body.is_none()
        || node.modifier_flags().intersects(ModifierFlags::AMBIENT)
    {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        compute_function_like_with_body(
            node.modifiers(),
            d.function_like_with_body_base.body_base.asterisk_token,
            d.name,
            &d.function_like_with_body_base,
            node,
            nodes,
        )
    }
}

/// `(node *ClassLikeBase) computeSubtreeFacts` — shared by
/// ClassDeclaration/ClassExpression (InterfaceDeclaration goes through
/// `TypeSyntaxBase` and is generated).
fn compute_class_like(
    modifiers: Option<&ModifierList>,
    cl: &crate::ast_generated::ClassLikeBase,
    nodes: &[Node],
) -> SubtreeFacts {
    if modifiers.is_some_and(|m| m.modifier_flags.intersects(ModifierFlags::AMBIENT)) {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, modifiers)
            | prop(nodes, cl.name)
            | eraseable_list(cl.type_parameters.as_ref())
            | prop_list(nodes, cl.heritage_clauses.as_ref())
            | prop_list(nodes, cl.members.as_ref())
    }
}

pub fn compute_class_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    compute_class_like(node.modifiers(), &node.as_class_declaration().class_like_base, nodes)
}

pub fn compute_class_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    compute_class_like(node.modifiers(), &node.as_class_expression().class_like_base, nodes)
}

pub fn compute_heritage_clause(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_heritage_clause();
    match d.token {
        Kind::ExtendsKeyword => prop_list(nodes, d.types.as_ref()),
        Kind::ImplementsKeyword => SubtreeFacts::CONTAINS_TYPE_SCRIPT,
        _ => SubtreeFacts::NONE,
    }
}

pub fn compute_enum_member(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_enum_member();
    prop(nodes, d.named_member_base.name)
        | prop(nodes, d.initializer)
        | SubtreeFacts::CONTAINS_TYPE_SCRIPT
}

pub fn compute_enum_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_enum_declaration();
    if node
        .modifiers()
        .is_some_and(|m| m.modifier_flags.intersects(ModifierFlags::AMBIENT))
    {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, node.modifiers())
            | prop(nodes, d.name)
            | prop_list(nodes, d.members.as_ref())
            | SubtreeFacts::CONTAINS_TYPE_SCRIPT
    }
}

pub fn compute_module_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_module_declaration();
    if node.modifier_flags().intersects(ModifierFlags::AMBIENT) {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, node.modifiers())
            | prop(nodes, d.name)
            | prop(nodes, node.body())
            | SubtreeFacts::CONTAINS_TYPE_SCRIPT
    }
}

pub fn compute_import_equals_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_import_equals_declaration();
    if d.is_type_only
        || !d
            .module_reference
            .is_some_and(|m| is_external_module_reference(&nodes[m]))
    {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, node.modifiers())
            | prop(nodes, d.name)
            | prop(nodes, d.module_reference)
    }
}

pub fn compute_import_specifier(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_import_specifier();
    if d.is_type_only {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop(nodes, d.property_name) | prop(nodes, d.name)
    }
}

pub fn compute_import_clause(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_import_clause();
    if d.phase_modifier == Kind::TypeKeyword {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop(nodes, d.name) | prop(nodes, d.named_bindings)
    }
}

pub fn compute_export_assignment(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_export_assignment();
    prop_modifiers(nodes, node.modifiers())
        | prop(nodes, d.type_)
        | prop(nodes, d.expression)
        | if d.is_export_equals {
            SubtreeFacts::CONTAINS_TYPE_SCRIPT
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_export_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_export_declaration();
    prop_modifiers(nodes, node.modifiers())
        | prop(nodes, d.export_clause)
        | prop(nodes, d.module_specifier)
        | prop(nodes, d.attributes)
        | if d.is_type_only {
            SubtreeFacts::CONTAINS_TYPE_SCRIPT
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_export_specifier(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_export_specifier();
    if d.is_type_only {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop(nodes, d.property_name) | prop(nodes, d.name)
    }
}

pub fn compute_constructor_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let fl = &node.as_constructor_declaration().function_like_with_body_base;
    if fl.body_base.body.is_none() {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, node.modifiers())
            | eraseable_list(fl.function_like_base.type_parameters.as_ref())
            | prop_list(nodes, fl.function_like_base.parameters.as_ref())
            | eraseable(fl.function_like_base.type_)
            | eraseable(fl.function_like_base.full_signature)
            | prop(nodes, fl.body_base.body)
    }
}

/// `(node *AccessorDeclarationBase) computeSubtreeFacts` — shared by
/// GetAccessorDeclaration/SetAccessorDeclaration.
fn compute_accessor_like(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = match node.kind {
        Kind::GetAccessor => &node.as_get_accessor_declaration().accessor_declaration_base,
        _ => &node.as_set_accessor_declaration().accessor_declaration_base,
    };
    let fl = &d.function_like_with_body_base;
    if fl.body_base.body.is_none() {
        SubtreeFacts::CONTAINS_TYPE_SCRIPT
    } else {
        prop_modifiers(nodes, node.modifiers())
            | prop(nodes, d.named_member_base.name)
            | eraseable_list(fl.function_like_base.type_parameters.as_ref())
            | prop_list(nodes, fl.function_like_base.parameters.as_ref())
            | eraseable(fl.function_like_base.type_)
            | eraseable(fl.function_like_base.full_signature)
            | prop(nodes, fl.body_base.body)
    }
}

pub fn compute_get_accessor_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    compute_accessor_like(node, nodes)
}

pub fn compute_set_accessor_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    compute_accessor_like(node, nodes)
}

pub fn compute_method_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_method_declaration();
    let fl = &d.function_like_with_body_base;
    if fl.body_base.body.is_none() {
        return SubtreeFacts::CONTAINS_TYPE_SCRIPT;
    }
    let is_async = node
        .modifiers()
        .is_some_and(|m| m.modifier_flags.intersects(ModifierFlags::ASYNC));
    let is_generator = fl.body_base.asterisk_token.is_some();
    prop_modifiers(nodes, node.modifiers())
        | prop(nodes, fl.body_base.asterisk_token)
        | prop(nodes, d.named_member_base.name)
        | eraseable(d.named_member_base.postfix_token)
        | eraseable_list(fl.function_like_base.type_parameters.as_ref())
        | prop_list(nodes, fl.function_like_base.parameters.as_ref())
        | prop(nodes, fl.body_base.body)
        | eraseable(fl.function_like_base.type_)
        | eraseable(fl.function_like_base.full_signature)
        | if is_async && is_generator {
            SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
        } else {
            SubtreeFacts::NONE
        }
        | if is_async && !is_generator {
            SubtreeFacts::CONTAINS_ANY_AWAIT
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_property_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_property_declaration();
    prop_modifiers(nodes, node.modifiers())
        | prop(nodes, d.named_member_base.name)
        | eraseable(d.named_member_base.postfix_token)
        | eraseable(d.type_)
        | prop(nodes, d.initializer)
        | SubtreeFacts::CONTAINS_CLASS_FIELDS
}

pub fn compute_class_static_block_declaration(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_class_static_block_declaration();
    prop_modifiers(nodes, node.modifiers())
        | prop(nodes, d.body)
        | SubtreeFacts::CONTAINS_CLASS_FIELDS
}

pub fn compute_keyword_expression(node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    match node.kind {
        Kind::ThisKeyword => SubtreeFacts::CONTAINS_LEXICAL_THIS,
        Kind::SuperKeyword => SubtreeFacts::CONTAINS_LEXICAL_SUPER,
        _ => SubtreeFacts::NONE,
    }
}

pub fn compute_big_int_literal(_node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    SubtreeFacts::NONE // `bigint` is not downleveled in any way
}

pub fn compute_identifier(_node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    SubtreeFacts::CONTAINS_IDENTIFIER
}

fn template_escape_facts(template_flags: TokenFlags) -> SubtreeFacts {
    if template_flags.intersects(TokenFlags::CONTAINS_INVALID_ESCAPE) {
        SubtreeFacts::CONTAINS_INVALID_TEMPLATE_ESCAPE
    } else {
        SubtreeFacts::NONE
    }
}

pub fn compute_no_substitution_template_literal(node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    template_escape_facts(
        node.as_no_substitution_template_literal()
            .template_literal_like_node_base
            .template_flags,
    )
}

pub fn compute_template_head(node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    template_escape_facts(
        node.as_template_head()
            .template_literal_like_node_base
            .template_flags,
    )
}

pub fn compute_template_middle(node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    template_escape_facts(
        node.as_template_middle()
            .template_literal_like_node_base
            .template_flags,
    )
}

pub fn compute_template_tail(node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    template_escape_facts(
        node.as_template_tail()
            .template_literal_like_node_base
            .template_flags,
    )
}

pub fn compute_binary_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_binary_expression();
    let op_kind = d
        .operator_token
        .map(|t| nodes[t].kind)
        .unwrap_or(Kind::Unknown);
    let mut facts = prop_modifiers(nodes, node.modifiers())
        | prop(nodes, d.left)
        | prop(nodes, d.type_)
        | prop(nodes, d.operator_token)
        | prop(nodes, d.right)
        | if op_kind == Kind::InKeyword
            && d.left.is_some_and(|l| is_private_identifier(&nodes[l]))
        {
            SubtreeFacts::CONTAINS_CLASS_FIELDS
                | SubtreeFacts::CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION
        } else {
            SubtreeFacts::NONE
        };
    if op_kind == Kind::EqualsToken
        && let Some(left) = d.left
        && (crate::ast_generated::is_object_literal_expression(&nodes[left])
            || crate::ast_generated::is_array_literal_expression(&nodes[left]))
        && crate::utilities::contains_object_rest_or_spread(&nodes[left], nodes)
    {
        facts |= SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD;
    }
    facts
}

pub fn compute_yield_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_yield_expression().expression)
        | SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
}

pub fn compute_arrow_function(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_arrow_function();
    let fl = &d.function_like_with_body_base;
    prop_modifiers(nodes, node.modifiers())
        | eraseable_list(fl.function_like_base.type_parameters.as_ref())
        | prop_list(nodes, fl.function_like_base.parameters.as_ref())
        | eraseable(fl.function_like_base.type_)
        | eraseable(fl.function_like_base.full_signature)
        | prop(nodes, fl.body_base.body)
        | if node.modifier_flags().intersects(ModifierFlags::ASYNC) {
            SubtreeFacts::CONTAINS_ANY_AWAIT
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_function_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_function_expression();
    compute_function_like_with_body(
        node.modifiers(),
        d.function_like_with_body_base.body_base.asterisk_token,
        d.name,
        &d.function_like_with_body_base,
        node,
        nodes,
    )
}

pub fn compute_as_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_as_expression().expression) | SubtreeFacts::CONTAINS_TYPE_SCRIPT
}

pub fn compute_satisfies_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_satisfies_expression().expression) | SubtreeFacts::CONTAINS_TYPE_SCRIPT
}

pub fn compute_property_access_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_property_access_expression();
    let private_name = if d.name.is_some_and(|n| is_identifier(&nodes[n])) {
        SubtreeFacts::NONE
    } else {
        SubtreeFacts::CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION
    };
    prop(nodes, d.expression) | prop(nodes, d.question_dot_token) | prop(nodes, d.name)
        | private_name
}

pub fn compute_call_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_call_expression();
    prop(nodes, d.expression)
        | prop(nodes, d.question_dot_token)
        | eraseable_list(d.type_arguments.as_ref())
        | prop_list(nodes, d.arguments.as_ref())
        | if crate::utilities::is_import_call(node, nodes) {
            SubtreeFacts::CONTAINS_DYNAMIC_IMPORT
        } else {
            SubtreeFacts::NONE
        }
}

pub fn compute_new_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_new_expression();
    prop(nodes, d.expression)
        | eraseable_list(d.type_arguments.as_ref())
        | prop_list(nodes, d.arguments.as_ref())
}

pub fn compute_meta_property(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_meta_property().name).without(SubtreeFacts::CONTAINS_IDENTIFIER)
}

pub fn compute_non_null_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_non_null_expression().expression) | SubtreeFacts::CONTAINS_TYPE_SCRIPT
}

pub fn compute_spread_element(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_spread_element().expression) | SubtreeFacts::CONTAINS_REST_OR_SPREAD
}

pub fn compute_tagged_template_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_tagged_template_expression();
    prop(nodes, d.tag)
        | prop(nodes, d.question_dot_token)
        | eraseable_list(d.type_arguments.as_ref())
        | prop(nodes, d.template)
}

pub fn compute_spread_assignment(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_spread_assignment().expression)
        | SubtreeFacts::CONTAINS_ES_OBJECT_REST_OR_SPREAD
        | SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
}

pub fn compute_property_assignment(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_property_assignment();
    prop(nodes, d.named_member_base.name) | prop(nodes, d.type_) | prop(nodes, d.initializer)
}

pub fn compute_shorthand_property_assignment(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_shorthand_property_assignment();
    prop(nodes, d.named_member_base.name)
        | prop(nodes, d.type_)
        | prop(nodes, d.object_assignment_initializer)
        | SubtreeFacts::CONTAINS_TYPE_SCRIPT
}

pub fn compute_await_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    // `await` in an ES2018 async generator must use `yield __await(expr)`.
    prop(nodes, node.as_await_expression().expression)
        | SubtreeFacts::CONTAINS_AWAIT
        | SubtreeFacts::CONTAINS_ANY_AWAIT
        | SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
}

pub fn compute_type_assertion(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_type_assertion().expression) | SubtreeFacts::CONTAINS_TYPE_SCRIPT
}

pub fn compute_expression_with_type_arguments(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_expression_with_type_arguments();
    prop(nodes, d.expression) | eraseable_list(d.type_arguments.as_ref())
}

// JSX — every Jsx* node contributes `SubtreeContainsJsx`.

pub fn compute_jsx_element(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_jsx_element();
    prop(nodes, d.opening_element)
        | prop_list(nodes, d.children.as_ref())
        | prop(nodes, d.closing_element)
        | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_attributes(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop_list(nodes, node.as_jsx_attributes().properties.as_ref()) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_namespaced_name(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_jsx_namespaced_name();
    prop(nodes, d.namespace) | prop(nodes, d.name) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_opening_element(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_jsx_opening_element();
    prop(nodes, d.tag_name)
        | eraseable_list(d.type_arguments.as_ref())
        | prop(nodes, d.attributes)
        | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_self_closing_element(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_jsx_self_closing_element();
    prop(nodes, d.tag_name) | eraseable_list(d.type_arguments.as_ref()) | prop(nodes, d.attributes)
        | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_fragment(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop_list(nodes, node.as_jsx_fragment().children.as_ref()) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_opening_fragment(_node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_closing_fragment(_node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_attribute(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    let d = node.as_jsx_attribute();
    prop(nodes, d.name) | prop(nodes, d.initializer) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_spread_attribute(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_jsx_spread_attribute().expression) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_closing_element(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_jsx_closing_element().tag_name) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_expression(node: &Node, nodes: &[Node]) -> SubtreeFacts {
    prop(nodes, node.as_jsx_expression().expression) | SubtreeFacts::CONTAINS_JSX
}

pub fn compute_jsx_text(_node: &Node, _nodes: &[Node]) -> SubtreeFacts {
    SubtreeFacts::CONTAINS_JSX
}
