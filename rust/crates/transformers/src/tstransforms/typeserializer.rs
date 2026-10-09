// Ported from tsc/internal/transformers/tstransforms/typeserializer.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The decorator-metadata type serializer — turns a TypeScript type node into
// the runtime expression used for `design:type` / `design:paramtypes` /
// `design:returntype` metadata.
//
// PORT: Go's `metadataSerializer` stores `f *printer.NodeFactory` and
// `ec *printer.EmitContext`; here the serializer captures the shared `Ec`
// handle instead (the factory is reached through `ec.borrow_mut().factory`).
// `s.c` (the `metadataSerializerContext`) is a `Cell` of a `Copy` struct; the
// `Serialize*OfNode` wrappers save/restore it exactly like Go's `defer`.
// `s.resolver` is `Option<Rc<RefCell<dyn EmitResolver>>>` — Go stores the
// possibly-nil interface on the struct and would nil-panic on use.

use std::cell::Cell;
use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, Kind, Node, NodeId, NodeList};
use tsc_core::options_generated::ScriptTarget;
use tsc_printer::{EmitResolver, TypeReferenceSerializationKind};
use tsc_debug as debug;

use crate::estransforms::Ec;

/// `type metadataSerializerContext struct`.
#[derive(Clone, Copy, Default)]
pub struct MetadataSerializerContext {
    /// `currentLexicalScope *ast.Node` — SourceFile | Block | ModuleBlock |
    /// CaseBlock
    pub current_lexical_scope: Option<NodeId>,
    /// `currentNameScope *ast.Node` — the class/object literal that names
    /// scope to
    pub current_name_scope: Option<NodeId>,
    /// `serializingConditionalTypeBranch bool`
    pub serializing_conditional_type_branch: bool,
}

/// `type metadataSerializer struct`.
pub struct MetadataSerializer<'a> {
    /// `resolver printer.EmitResolver`
    resolver: Option<Rc<RefCell<dyn EmitResolver + 'a>>>,
    /// `languageVersion core.ScriptTarget`
    language_version: ScriptTarget,
    /// `strictNullChecks bool`
    strict_null_checks: bool,
    /// `ec *printer.EmitContext`
    ec: Ec,
    /// `c metadataSerializerContext`
    c: Cell<MetadataSerializerContext>,
}

/// `newMetadataSerializer` — the `f`/`ec` pair collapses to `ec` since the
/// printer factory is reached through it.
pub fn new_metadata_serializer<'a>(
    resolver: Option<Rc<RefCell<dyn EmitResolver + 'a>>>,
    ec: Ec,
    language_version: ScriptTarget,
    strict_null_checks: bool,
) -> MetadataSerializer<'a> {
    MetadataSerializer {
        resolver,
        language_version,
        strict_null_checks,
        ec,
        c: Cell::new(MetadataSerializerContext::default()),
    }
}

/// `GetSetAccessorValueParameter` — `node` must be a `SetAccessorDeclaration`
/// (Go takes `*ast.SetAccessorDeclaration`; `None` mirrors nil).
pub fn get_set_accessor_value_parameter(
    node: Option<NodeId>,
    nodes: &[Node],
) -> Option<NodeId> {
    let node = node?;
    let params = nodes[node].parameters()?;
    if !params.is_empty() {
        if params.len() >= 2 && ast::is_this_parameter(&nodes[params[0]], nodes) {
            return Some(params[1]);
        }
        return Some(params[0]);
    }
    None
}

/// `getSetAccessorTypeAnnotationNode` — gets the type annotation for the
/// value parameter. `node` must be a `SetAccessorDeclaration`.
fn get_set_accessor_type_annotation_node(
    node: Option<NodeId>,
    nodes: &[Node],
) -> Option<NodeId> {
    let p = get_set_accessor_value_parameter(node, nodes)?;
    nodes[p].as_parameter_declaration().type_
}

/// `getAccessorTypeNode`.
fn get_accessor_type_node(
    node: NodeId,
    container: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let accessors = ast::get_all_accessor_declarations(
        nodes[container].member_list().map(|m| m.nodes()).unwrap_or(&[]),
        node,
        nodes,
    );
    if accessors.set_accessor.is_some() {
        return get_set_accessor_type_annotation_node(accessors.set_accessor, nodes);
    }
    if let Some(get_accessor) = accessors.get_accessor {
        return nodes[get_accessor].type_();
    }
    None
}

/// `getParametersOfDecoratedDeclaration` — returns the parameter list to use
/// when serializing `design:paramtypes` for `node`. `container` is the
/// enclosing class/object literal, if any.
fn get_parameters_of_decorated_declaration(
    node: NodeId,
    container: Option<NodeId>,
    nodes: &[Node],
) -> Option<NodeList> {
    if let Some(container) = container {
        if nodes[node].kind == Kind::GetAccessor {
            let acc = ast::get_all_accessor_declarations(
                nodes[container].member_list().map(|m| m.nodes()).unwrap_or(&[]),
                node,
                nodes,
            );
            if let Some(set_accessor) = acc.set_accessor {
                return nodes[set_accessor].parameter_list().cloned();
            }
        }
    }
    nodes[node].parameter_list().cloned()
}

impl<'a> MetadataSerializer<'a> {
    /// `s.SerializeTypeOfNode` — runs `serializeTypeOfNode` under `ctx`,
    /// restoring the previous context afterwards.
    pub fn serialize_type_of_node(
        &self,
        nodes: &mut Vec<Node>,
        ctx: MetadataSerializerContext,
        node: NodeId,
        container: Option<NodeId>,
    ) -> NodeId {
        let old_ctx = self.c.get();
        self.c.set(ctx);
        let result = self.serialize_type_of_node_inner(nodes, node, container);
        self.c.set(old_ctx);
        result
    }

    /// `s.SerializeParameterTypesOfNode`.
    pub fn serialize_parameter_types_of_node(
        &self,
        nodes: &mut Vec<Node>,
        ctx: MetadataSerializerContext,
        node: NodeId,
        container: Option<NodeId>,
    ) -> NodeId {
        let old_ctx = self.c.get();
        self.c.set(ctx);
        let result = self.serialize_parameter_types_of_node_inner(nodes, node, container);
        self.c.set(old_ctx);
        result
    }

    /// `s.SerializeReturnTypeOfNode`.
    pub fn serialize_return_type_of_node(
        &self,
        nodes: &mut Vec<Node>,
        ctx: MetadataSerializerContext,
        node: NodeId,
    ) -> NodeId {
        let old_ctx = self.c.get();
        self.c.set(ctx);
        let result = self.serialize_return_type_of_node_inner(nodes, node);
        self.c.set(old_ctx);
        result
    }

    /// `s.serializeTypeOfNode` — serializes the type of a node for use with
    /// decorator type metadata.
    fn serialize_type_of_node_inner(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        container: Option<NodeId>,
    ) -> NodeId {
        match nodes[node].kind {
            Kind::PropertyDeclaration | Kind::Parameter => {
                self.serialize_type_node(nodes, nodes[node].type_())
            }
            Kind::GetAccessor | Kind::SetAccessor => {
                let type_node =
                    container.and_then(|c| get_accessor_type_node(node, c, nodes));
                self.serialize_type_node(nodes, type_node)
            }
            Kind::ClassDeclaration | Kind::ClassExpression | Kind::MethodDeclaration => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Function")
            }
            _ => self.ec.borrow_mut().factory.new_void_zero_expression(nodes),
        }
    }

    /// `s.serializeParameterTypesOfNode` — serializes the types of the
    /// parameters of a node for use with decorator type metadata.
    fn serialize_parameter_types_of_node_inner(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        container: Option<NodeId>,
    ) -> NodeId {
        let mut value_declaration: Option<NodeId> = None;
        if ast::is_class_like(Some(node), nodes) {
            value_declaration = ast::get_first_constructor_with_body(&nodes[node], nodes);
        } else if ast::is_function_like(Some(node), nodes)
            && ast::node_is_present(nodes[node].body(), nodes)
        {
            value_declaration = Some(node);
        }

        let Some(value_declaration) = value_declaration else {
            let elements = self.ec.borrow().factory.new_node_list([]);
            return self
                .ec
                .borrow_mut()
                .factory
                .new_array_literal_expression(nodes, Some(elements), false);
        };

        let mut expressions: Vec<NodeId> = Vec::new();
        let parameters = get_parameters_of_decorated_declaration(value_declaration, container, nodes);
        if let Some(parameters) = parameters {
            for (i, &parameter) in parameters.nodes.iter().enumerate() {
                if i == 0 {
                    let name = nodes[parameter].name();
                    if name.is_some_and(|n| {
                        ast::is_identifier(&nodes[n]) && nodes[n].text(nodes) == "this"
                    }) {
                        continue;
                    }
                }
                if nodes[parameter]
                    .as_parameter_declaration()
                    .dot_dot_dot_token
                    .is_some()
                {
                    let rest_type = ast::get_rest_parameter_element_type(
                        nodes[parameter].as_parameter_declaration().type_,
                        nodes,
                    );
                    expressions.push(self.serialize_type_node(nodes, rest_type));
                } else {
                    expressions.push(self.serialize_type_of_node_inner(nodes, parameter, container));
                }
            }
        }
        let elements = self.ec.borrow().factory.new_node_list(expressions);
        self.ec
            .borrow_mut()
            .factory
            .new_array_literal_expression(nodes, Some(elements), false)
    }

    /// `s.serializeReturnTypeOfNode` — serializes the return type of a node
    /// for use with decorator type metadata.
    fn serialize_return_type_of_node_inner(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        if ast::is_function_like(Some(node), nodes) && nodes[node].type_().is_some() {
            return self.serialize_type_node(nodes, nodes[node].type_());
        } else if ast::is_async_function(&nodes[node]) {
            return self.ec.borrow_mut().factory.new_identifier(nodes, "Promise");
        }
        self.ec.borrow_mut().factory.new_void_zero_expression(nodes)
    }

    /// `s.serializeTypeNode` — serializes a type node for use with decorator
    /// type metadata.
    fn serialize_type_node(&self, nodes: &mut Vec<Node>, node: Option<NodeId>) -> NodeId {
        let Some(node) = node else {
            return self.ec.borrow_mut().factory.new_identifier(nodes, "Object");
        };

        let node = ast::skip_type_parentheses(node, nodes);

        match nodes[node].kind {
            Kind::VoidKeyword | Kind::UndefinedKeyword | Kind::NeverKeyword => {
                return self.ec.borrow_mut().factory.new_void_zero_expression(nodes)
            }
            Kind::FunctionType | Kind::ConstructorType => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Function")
            }
            Kind::ArrayType | Kind::TupleType => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Array")
            }
            Kind::TypePredicate => {
                if nodes[node].as_type_predicate_node().asserts_modifier.is_some() {
                    return self.ec.borrow_mut().factory.new_void_zero_expression(nodes);
                }
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Boolean");
            }
            Kind::BooleanKeyword => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Boolean")
            }
            Kind::TemplateLiteralType | Kind::StringKeyword => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "String")
            }
            Kind::ObjectKeyword => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Object")
            }
            Kind::LiteralType => {
                if let Some(literal) = nodes[node].as_literal_type_node().literal {
                    return self.serialize_literal_of_literal_type_node(nodes, literal);
                }
            }
            Kind::NumberKeyword => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Number")
            }
            Kind::BigIntKeyword => return self.serialize_big_int_constructor(nodes),
            Kind::SymbolKeyword => {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Symbol")
            }
            Kind::TypeReference => return self.serialize_type_reference_node(nodes, node),
            Kind::IntersectionType => {
                let types = nodes[node]
                    .as_intersection_type_node()
                    .union_or_intersection_type_node_base
                    .types
                    .as_ref()
                    .map(|t| t.nodes.to_vec())
                    .unwrap_or_default();
                return self.serialize_union_or_intersection_constituents(nodes, &types, true);
            }
            Kind::UnionType => {
                let types = nodes[node]
                    .as_union_type_node()
                    .union_or_intersection_type_node_base
                    .types
                    .as_ref()
                    .map(|t| t.nodes.to_vec())
                    .unwrap_or_default();
                return self.serialize_union_or_intersection_constituents(nodes, &types, false);
            }
            Kind::ConditionalType => {
                let old_state = self.c.get().serializing_conditional_type_branch;
                let mut c = self.c.get();
                c.serializing_conditional_type_branch = true;
                self.c.set(c);
                let d = nodes[node].as_conditional_type_node();
                let types = [d.true_type, d.false_type]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                let result =
                    self.serialize_union_or_intersection_constituents(nodes, &types, false);
                let mut c = self.c.get();
                c.serializing_conditional_type_branch = old_state;
                self.c.set(c);
                return result;
            }
            Kind::TypeOperator => {
                if nodes[node].as_type_operator_node().operator == Kind::ReadonlyKeyword {
                    return self.serialize_type_node(nodes, nodes[node].type_());
                }
                // TODO: why is `unique symbol` not handled as `Symbol`? This
                // falls back to `Object`
            }
            Kind::TypeQuery
            | Kind::IndexedAccessType
            | Kind::MappedType
            | Kind::TypeLiteral
            | Kind::AnyKeyword
            | Kind::UnknownKeyword
            | Kind::ThisType
            | Kind::ImportType => {
                // These types fall back to Object.
            }
            // handle JSDoc types from an invalid parse
            Kind::JSDocAllType | Kind::JSDocVariadicType => {
                // no meaningful serialization for these invalid-parse JSDoc
                // types
            }
            Kind::JSDocNullableType | Kind::JSDocNonNullableType | Kind::JSDocOptionalType => {
                return self.serialize_type_node(nodes, nodes[node].type_());
            }
            _ => {
                debug::fail_bad_syntax_kind!(&nodes[node]);
            }
        }
        self.ec.borrow_mut().factory.new_identifier(nodes, "Object")
    }

    /// `s.serializeUnionOrIntersectionConstituents`.
    //
    // Note when updating logic here also update
    // `getEntityNameForDecoratorMetadata` in checker.ts so that aliases can be
    // marked as referenced
    fn serialize_union_or_intersection_constituents(
        &self,
        nodes: &mut Vec<Node>,
        types: &[NodeId],
        is_intersection: bool,
    ) -> NodeId {
        let mut serialized_type: Option<NodeId> = None;
        for &type_node in types {
            let type_node = ast::skip_type_parentheses(type_node, nodes);
            if nodes[type_node].kind == Kind::NeverKeyword {
                if is_intersection {
                    return self.ec.borrow_mut().factory.new_void_zero_expression(nodes); // Reduce to `never` in an intersection
                }
                continue; // Elide `never` in a union
            }

            if nodes[type_node].kind == Kind::UnknownKeyword {
                if !is_intersection {
                    return self.ec.borrow_mut().factory.new_identifier(nodes, "Object"); // Reduce to `unknown` in a union
                }
                continue; // Elide `unknown` in an intersection
            }

            if nodes[type_node].kind == Kind::AnyKeyword {
                return self.ec.borrow_mut().factory.new_identifier(nodes, "Object"); // Reduce to `any` in a union or intersection
            }

            if !self.strict_null_checks
                && ((ast::is_literal_type_node(&nodes[type_node])
                    && nodes[type_node]
                        .as_literal_type_node()
                        .literal
                        .is_some_and(|l| nodes[l].kind == Kind::NullKeyword))
                    || nodes[type_node].kind == Kind::UndefinedKeyword)
            {
                continue; // Elide null and undefined from unions for metadata, just like what we did prior to the implementation of strict null checks
            }

            let serialized_constituent = self.serialize_type_node(nodes, Some(type_node));
            if ast::is_identifier(&nodes[serialized_constituent])
                && nodes[serialized_constituent].text(nodes) == "Object"
            {
                // One of the individual is global object, return immediately
                return serialized_constituent;
            }

            // If there exists union that is not `void 0` expression, check if
            // the the common type is identifier.
            // anything more complex and we will just default to Object
            if let Some(serialized_type) = serialized_type {
                // Different types
                if !self.equate_serialized_type_nodes(nodes, serialized_type, serialized_constituent)
                {
                    return self.ec.borrow_mut().factory.new_identifier(nodes, "Object");
                }
            } else {
                // Initialize the union type
                serialized_type = Some(serialized_constituent);
            }
        }

        // If we were able to find common type, use it
        if let Some(serialized_type) = serialized_type {
            return serialized_type;
        }
        self.ec.borrow_mut().factory.new_void_zero_expression(nodes) // Fallback is only hit if all union constituents are null/undefined/never
    }

    /// `s.serializeLiteralOfLiteralTypeNode`.
    fn serialize_literal_of_literal_type_node(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        match nodes[node].kind {
            Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "String")
            }
            Kind::PrefixUnaryExpression => {
                let operand = nodes[node]
                    .as_prefix_unary_expression()
                    .operand
                    .expect("prefix unary has no operand");
                match nodes[operand].kind {
                    Kind::NumericLiteral | Kind::BigIntLiteral => {
                        self.serialize_literal_of_literal_type_node(nodes, operand)
                    }
                    _ => debug::fail_bad_syntax_kind!(&nodes[operand]),
                }
            }
            Kind::NumericLiteral => self.ec.borrow_mut().factory.new_identifier(nodes, "Number"),
            Kind::BigIntLiteral => self.serialize_big_int_constructor(nodes),
            Kind::TrueKeyword | Kind::FalseKeyword => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Boolean")
            }
            Kind::NullKeyword => self.ec.borrow_mut().factory.new_void_zero_expression(nodes),
            _ => debug::fail_bad_syntax_kind!(&nodes[node]),
        }
    }

    /// `s.serializeTypeReferenceNode` — serializes a TypeReferenceNode to an
    /// appropriate JS constructor value for use with decorator type
    /// metadata. `node` must be a `TypeReference`.
    fn serialize_type_reference_node(&self, nodes: &mut Vec<Node>, node: NodeId) -> NodeId {
        let type_name = nodes[node].as_type_reference_node().type_name;
        let mut serial_scope = self.c.get().current_name_scope;
        if serial_scope.is_none() {
            serial_scope = self.c.get().current_lexical_scope;
        }
        // PORT: Go passes `s.ec.ParseNode(...)` results (possibly nil) through
        // to the resolver; the trait signature takes `NodeId`/`Option<NodeId>`,
        // so fall back to the un-parsed node.
        let name = type_name
            .map(|n| self.ec.borrow().parse_node(nodes, n).unwrap_or(n))
            .unwrap_or(node);
        let serial_scope = serial_scope.and_then(|s| self.ec.borrow().parse_node(nodes, s));
        let kind = self
            .resolver
            .as_ref()
            .expect("metadataSerializer requires an emit resolver")
            .borrow()
            .get_type_reference_serialization_kind(name, serial_scope, nodes);
        match kind {
            TypeReferenceSerializationKind::Unknown => {
                // From conditional type type reference that cannot be resolved
                // is Similar to any or unknown
                if self.c.get().serializing_conditional_type_branch {
                    return self.ec.borrow_mut().factory.new_identifier(nodes, "Object");
                }

                let serialized = self.serialize_entity_name_as_expression_fallback(
                    nodes,
                    type_name.unwrap_or(node),
                );
                let temp = self.ec.borrow_mut().factory.new_temp_variable(nodes);
                self.ec.borrow_mut().add_variable_declaration(nodes, temp);
                let assignment = self
                    .ec
                    .borrow_mut()
                    .factory
                    .new_assignment_expression(nodes, temp, serialized);
                let type_check =
                    self.ec.borrow_mut().factory.new_type_check(nodes, assignment, "function");
                let question = self
                    .ec
                    .borrow_mut()
                    .factory
                    .new_token(nodes, Kind::QuestionToken);
                let colon = self
                    .ec
                    .borrow_mut()
                    .factory
                    .new_token(nodes, Kind::ColonToken);
                let object = self.ec.borrow_mut().factory.new_identifier(nodes, "Object");
                self.ec.borrow_mut().factory.new_conditional_expression(
                    nodes,
                    Some(type_check),
                    Some(question),
                    Some(temp),
                    Some(colon),
                    Some(object),
                )
            }

            TypeReferenceSerializationKind::TypeWithConstructSignatureAndValue => self
                .serialize_entity_name_as_expression(nodes, type_name.unwrap_or(node)),

            TypeReferenceSerializationKind::VoidNullableOrNeverType => {
                self.ec.borrow_mut().factory.new_void_zero_expression(nodes)
            }

            TypeReferenceSerializationKind::BigIntLikeType => {
                self.serialize_big_int_constructor(nodes)
            }

            TypeReferenceSerializationKind::BooleanType => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Boolean")
            }

            TypeReferenceSerializationKind::NumberLikeType => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Number")
            }

            TypeReferenceSerializationKind::StringLikeType => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "String")
            }

            TypeReferenceSerializationKind::ArrayLikeType => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Array")
            }

            TypeReferenceSerializationKind::ESSymbolType => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Symbol")
            }

            TypeReferenceSerializationKind::TypeWithCallSignature => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Function")
            }

            TypeReferenceSerializationKind::Promise => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Promise")
            }

            TypeReferenceSerializationKind::ObjectType => {
                self.ec.borrow_mut().factory.new_identifier(nodes, "Object")
            }
        }
    }

    /// `s.serializeBigIntConstructor`.
    fn serialize_big_int_constructor(&self, nodes: &mut Vec<Node>) -> NodeId {
        if self.language_version >= ScriptTarget::ES2020 {
            return self.ec.borrow_mut().factory.new_identifier(nodes, "BigInt");
        }
        let big_int = self.ec.borrow_mut().factory.new_identifier(nodes, "BigInt");
        let type_check =
            self.ec.borrow_mut().factory.new_type_check(nodes, big_int, "function");
        let question = self
            .ec
            .borrow_mut()
            .factory
            .new_token(nodes, Kind::QuestionToken);
        let big_int = self.ec.borrow_mut().factory.new_identifier(nodes, "BigInt");
        let colon = self
            .ec
            .borrow_mut()
            .factory
            .new_token(nodes, Kind::ColonToken);
        let object = self.ec.borrow_mut().factory.new_identifier(nodes, "Object");
        self.ec.borrow_mut().factory.new_conditional_expression(
            nodes,
            Some(type_check),
            Some(question),
            Some(big_int),
            Some(colon),
            Some(object),
        )
    }

    /// `s.serializeEntityNameAsExpression` — serializes an entity name as an
    /// expression for decorator type metadata.
    fn serialize_entity_name_as_expression(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        match nodes[node].kind {
            Kind::Identifier => {
                // Create a clone of the name with a new parent, and treat it
                // as if it were a source tree node for the purposes of the
                // checker.
                let name = self.ec.borrow_mut().factory.clone_node(nodes, node);
                nodes[name].loc = nodes[node].loc;
                self.ec.borrow().unset_original(name); // make this identifier emulate a parse node, making it behave correctly when inspected by the module transforms
                // .parent is set to ensure the parent is a parse tree node.
                nodes[name].parent = self
                    .c
                    .get()
                    .current_lexical_scope
                    .and_then(|s| self.ec.borrow().parse_node(nodes, s));
                name
            }
            Kind::QualifiedName => self.serialize_qualified_name_as_expression(nodes, node),
            _ => node, // unreachable in Go (returns nil for other kinds)
        }
    }

    /// `s.serializeQualifiedNameAsExpression` — serializes a qualified name
    /// as an expression for decorator type metadata. `node` must be a
    /// `QualifiedName`.
    fn serialize_qualified_name_as_expression(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        let (left, right) = {
            let d = nodes[node].as_qualified_name();
            (d.left, d.right)
        };
        let left = self.serialize_entity_name_as_expression(nodes, left.unwrap_or(node));
        self.ec.borrow_mut().factory.new_property_access_expression(
            nodes,
            Some(left),
            None, /* questionDotToken */
            right,
            ast::NodeFlags::NONE,
        )
    }

    /// `s.serializeEntityNameAsExpressionFallback` — serializes an entity
    /// name which may not exist at runtime, but whose access shouldn't throw.
    fn serialize_entity_name_as_expression_fallback(
        &self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        if nodes[node].kind == Kind::Identifier {
            // A -> typeof A !== "undefined" && A
            let copied = self.serialize_entity_name_as_expression(nodes, node);
            return self.create_checked_value(nodes, copied, copied);
        }
        let left_id = nodes[node].as_qualified_name().left;
        if left_id.is_some_and(|l| nodes[l].kind == Kind::Identifier) {
            // A.B -> typeof A !== "undefined" && A.B
            let left = self.serialize_entity_name_as_expression(
                nodes,
                left_id.expect("qualified name has no left"),
            );
            let full = self.serialize_entity_name_as_expression(nodes, node);
            return self.create_checked_value(nodes, left, full);
        }
        // A.B.C -> typeof A !== "undefined" && (_a = A.B) !== void 0 && _a.C
        let left = self.serialize_entity_name_as_expression_fallback(
            nodes,
            left_id.expect("qualified name has no left"),
        );
        let temp = self.ec.borrow_mut().factory.new_temp_variable(nodes);
        self.ec.borrow_mut().add_variable_declaration(nodes, temp);
        let (left_left, left_right) = {
            let d = nodes[left].as_binary_expression();
            (d.left, d.right)
        };
        let void_zero = self.ec.borrow_mut().factory.new_void_zero_expression(nodes);
        let assigned = self.ec.borrow_mut().factory.new_assignment_expression(
            nodes,
            temp,
            left_right.expect("fallback left has no right"),
        );
        let strict_neq = self.ec.borrow_mut().factory.new_strict_inequality_expression(
            nodes,
            assigned,
            void_zero,
        );
        let and1 = self.ec.borrow_mut().factory.new_logical_and_expression(
            nodes,
            left_left.expect("fallback left has no left"),
            strict_neq,
        );
        let right = nodes[node].as_qualified_name().right;
        let prop = self.ec.borrow_mut().factory.new_property_access_expression(
            nodes,
            Some(temp),
            None, /* questionDotToken */
            right,
            ast::NodeFlags::NONE,
        );
        self.ec
            .borrow_mut()
            .factory
            .new_logical_and_expression(nodes, and1, prop)
    }

    /// `s.createCheckedValue` — produces an expression that results in
    /// `right` if `left` is not undefined at runtime:
    ///
    /// ```text
    /// typeof left !== "undefined" && right
    /// ```
    ///
    /// We use `typeof L !== "undefined"` (rather than `L !== undefined`) since
    /// `L` may not be declared. It's acceptable for this expression to result
    /// in `false` at runtime, as the result is intended to be further checked
    /// by any containing expression.
    fn create_checked_value(
        &self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        let typeof_expr = self
            .ec
            .borrow_mut()
            .factory
            .new_type_of_expression(nodes, Some(left));
        let undefined_lit = self.ec.borrow_mut().factory.new_string_literal(
            nodes,
            "undefined",
            ast::TokenFlags::NONE,
        );
        let strict_neq = self.ec.borrow_mut().factory.new_strict_inequality_expression(
            nodes,
            typeof_expr,
            undefined_lit,
        );
        self.ec
            .borrow_mut()
            .factory
            .new_logical_and_expression(nodes, strict_neq, right)
    }

    /// `s.equateSerializedTypeNodes`.
    fn equate_serialized_type_nodes(
        &self,
        nodes: &[Node],
        left: NodeId,
        right: NodeId,
    ) -> bool {
        // temp vars used in fallback
        if crate::utilities::is_generated_identifier(&self.ec.borrow(), left) {
            return crate::utilities::is_generated_identifier(&self.ec.borrow(), right);
        }
        // entity names
        if ast::is_identifier(&nodes[left]) {
            return ast::is_identifier(&nodes[right])
                && nodes[left].text(nodes) == nodes[right].text(nodes);
        }
        if ast::is_property_access_expression(&nodes[left]) {
            return ast::is_property_access_expression(&nodes[right])
                && self.equate_serialized_type_nodes(
                    nodes,
                    nodes[left].expression().unwrap_or(left),
                    nodes[right].expression().unwrap_or(right),
                )
                && self.equate_serialized_type_nodes(
                    nodes,
                    nodes[left].name().unwrap_or(left),
                    nodes[right].name().unwrap_or(right),
                );
        }
        // `void 0`
        if ast::is_void_expression(&nodes[left]) {
            return ast::is_void_expression(&nodes[right])
                && nodes[left]
                    .expression()
                    .is_some_and(|l| ast::is_numeric_literal(&nodes[l]))
                && nodes[right]
                    .expression()
                    .is_some_and(|r| ast::is_numeric_literal(&nodes[r]))
                && nodes[left]
                    .expression()
                    .is_some_and(|l| nodes[l].text(nodes) == "0")
                && nodes[right]
                    .expression()
                    .is_some_and(|r| nodes[r].text(nodes) == "0");
        }
        // `"undefined"` or `"function"` in `typeof` checks
        if ast::is_string_literal(&nodes[left]) {
            return ast::is_string_literal(&nodes[right])
                && nodes[left].text(nodes) == nodes[right].text(nodes);
        }
        // used in `typeof` checks for fallback
        if ast::is_type_of_expression(&nodes[left]) {
            return ast::is_type_of_expression(&nodes[right])
                && self.equate_serialized_type_nodes(
                    nodes,
                    nodes[left].expression().unwrap_or(left),
                    nodes[right].expression().unwrap_or(right),
                );
        }
        // parens in `typeof` checks with temps
        if ast::is_parenthesized_expression(&nodes[left]) {
            return ast::is_parenthesized_expression(&nodes[right])
                && self.equate_serialized_type_nodes(
                    nodes,
                    nodes[left].expression().unwrap_or(left),
                    nodes[right].expression().unwrap_or(right),
                );
        }
        // conditionals used in fallback
        if ast::is_conditional_expression(&nodes[left]) {
            if !ast::is_conditional_expression(&nodes[right]) {
                return false;
            }
            let (lc, lt, lf) = {
                let d = nodes[left].as_conditional_expression();
                (d.condition, d.when_true, d.when_false)
            };
            let (rc, rt, rf) = {
                let d = nodes[right].as_conditional_expression();
                (d.condition, d.when_true, d.when_false)
            };
            return self.equate_option(nodes, lc, rc)
                && self.equate_option(nodes, lt, rt)
                && self.equate_option(nodes, lf, rf);
        }
        // logical binary and assignments used in fallback
        if ast::is_binary_expression(&nodes[left]) {
            if !ast::is_binary_expression(&nodes[right]) {
                return false;
            }
            let (lk, ll, lr) = {
                let d = nodes[left].as_binary_expression();
                (
                    d.operator_token.map(|t| nodes[t].kind),
                    d.left,
                    d.right,
                )
            };
            let (rk, rl, rr) = {
                let d = nodes[right].as_binary_expression();
                (
                    d.operator_token.map(|t| nodes[t].kind),
                    d.left,
                    d.right,
                )
            };
            return lk == rk
                && self.equate_option(nodes, ll, rl)
                && self.equate_option(nodes, lr, rr);
        }
        false
    }

    /// Equates two nilable operands of `equateSerializedTypeNodes` (Go would
    /// call `.Kind`/`.Expression()` on nil — practically these are always
    /// populated when reached; `None == None` equates).
    fn equate_option(
        &self,
        nodes: &[Node],
        left: Option<NodeId>,
        right: Option<NodeId>,
    ) -> bool {
        match (left, right) {
            (Some(l), Some(r)) => self.equate_serialized_type_nodes(nodes, l, r),
            (None, None) => true,
            _ => false,
        }
    }
}
