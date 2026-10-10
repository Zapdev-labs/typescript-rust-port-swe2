// Ported from tsc/internal/checker/jsx.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// JSX checking: all `func`s in jsx.go are ported as `impl Checker` methods or
// free functions, in Go declaration order.
//
// Conventions follow `checker_core.rs`/`types.rs`:
//   `*ast.Node` → `NodeId` (`Option<NodeId>` when the Go pointer is
//   nil-able), `*ast.Symbol` → `SymbolId`, `*Type` → `TypeId`,
//   `*Signature` → `SignatureId`, `*diagnostics.Message` → `&'static
//   tsc_diagnostics::Message`, `*ast.Diagnostic` → `ast::diagnostic::
//   DiagnosticRef`, and Go's variadic diagnostic args → `&[String]`.
//
// Go's `c._jsxFactoryEntity`/`parseIsolatedEntityName` build nodes in a
// pointer-free AST; this port materializes synthesized nodes into the
// enclosing file's arena (`NodeId` packs `file_index`) — a port-added
// `file_index` parameter on `parse_isolated_entity_name` selects the target
// arena. Cross-file calls resolve to sibling files (`checker_a.rs`–
// `checker_d.rs`, `utilities.rs`) by snake_case name — unresolved symbols are
// expected until those land.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_core::options_generated::JsxEmit;
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;

use crate::checker_core::{CheckMode, Checker, InferenceContextId, InferencePriority, JsxFlags};
use crate::checker_types::{IterationTypeKind, IterationUse};
use crate::relater::{SharedRelation, is_hyphenated_jsx_name};
use crate::types::{
    AccessFlags, ContextFlags, ObjectFlags, SignatureId, SignatureKind, TypeFlags, TypeId,
};

impl JsxFlags {
    /// `JsxFlagsIntrinsicNamedElement` — an element from a named property of
    /// the JSX.IntrinsicElements interface.
    pub const INTRINSIC_NAMED_ELEMENT: JsxFlags = JsxFlags(1 << 0);
    /// `JsxFlagsIntrinsicIndexedElement` — an element inferred from the
    /// string index signature of the JSX.IntrinsicElements interface.
    pub const INTRINSIC_INDEXED_ELEMENT: JsxFlags = JsxFlags(1 << 1);
    /// `JsxFlagsIntrinsicElement`.
    pub const INTRINSIC_ELEMENT: JsxFlags =
        JsxFlags(Self::INTRINSIC_NAMED_ELEMENT.0 | Self::INTRINSIC_INDEXED_ELEMENT.0);
}

/// `type JsxReferenceKind int32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(i32)]
pub enum JsxReferenceKind {
    /// `JsxReferenceKindComponent`.
    Component = 0,
    /// `JsxReferenceKindFunction`.
    Function = 1,
    /// `JsxReferenceKindMixed`.
    Mixed = 2,
}

/// `var JsxNames` — well-known member names of the `JSX` namespace.
pub struct JsxNames {
    /// `JSX`.
    pub jsx: &'static str,
    /// `IntrinsicElements`.
    pub intrinsic_elements: &'static str,
    /// `ElementClass`.
    pub element_class: &'static str,
    /// `ElementAttributesPropertyNameContainer`.
    pub element_attributes_property_name_container: &'static str,
    /// `ElementChildrenAttributeNameContainer`.
    pub element_children_attribute_name_container: &'static str,
    /// `Element`.
    pub element: &'static str,
    /// `ElementType`.
    pub element_type: &'static str,
    /// `IntrinsicAttributes`.
    pub intrinsic_attributes: &'static str,
    /// `IntrinsicClassAttributes`.
    pub intrinsic_class_attributes: &'static str,
    /// `LibraryManagedAttributes`.
    pub library_managed_attributes: &'static str,
}

/// `var JsxNames = struct{...}{...}`.
pub const JSX_NAMES: JsxNames = JsxNames {
    jsx: "JSX",
    intrinsic_elements: "IntrinsicElements",
    element_class: "ElementClass",
    element_attributes_property_name_container: "ElementAttributesProperty",
    element_children_attribute_name_container: "ElementChildrenAttribute",
    element: "Element",
    element_type: "ElementType",
    intrinsic_attributes: "IntrinsicAttributes",
    intrinsic_class_attributes: "IntrinsicClassAttributes",
    library_managed_attributes: "LibraryManagedAttributes",
};

/// `var ReactNames`.
pub struct ReactNames {
    /// `Fragment`.
    pub fragment: &'static str,
}

/// `var ReactNames = struct{...}{Fragment: "Fragment"}`.
pub const REACT_NAMES: ReactNames = ReactNames {
    fragment: "Fragment",
};

/// `type JsxElaborationElement struct` — the `createDiagnostic` field is the
/// optional custom-diagnostic factory (`nil` in Go ⇒ `None`).
pub(crate) struct JsxElaborationElement {
    /// `errorNode`.
    pub error_node: Option<NodeId>,
    /// `innerExpression`.
    pub inner_expression: Option<NodeId>,
    /// `nameType` — `TypeId::NONE` when unset.
    pub name_type: Option<TypeId>,
    /// `createDiagnostic` — creates a custom diagnostic for this element.
    pub create_diagnostic:
        Option<Box<dyn FnMut(&mut Checker, Option<NodeId>) -> ast::diagnostic::DiagnosticRef>>,
}

/// `getInvalidTextDiagnostic func() (*diagnostics.Message, []any)` — lazily
/// materialized message+args shared by every elaboration element produced for
/// one children list. Wrapped in `Rc<RefCell>` so all the `createDiagnostic`
/// closures capture the same lazily-filled cache, as in Go.
type InvalidTextDiagnostic =
    Rc<RefCell<dyn FnMut(&mut Checker) -> (&'static diagnostics::Message, Vec<String>)>>;

impl Checker {
    /// `func (c *Checker) checkJsxElement` (jsx.go:72).
    pub(crate) fn check_jsx_element(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let _ = check_mode;
        self.check_node_deferred(node);
        self.get_jsx_element_type_at(node)
    }

    /// `func (c *Checker) checkJsxElementDeferred` (jsx.go:77).
    pub(crate) fn check_jsx_element_deferred(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let jsx_element = nodes[node].as_jsx_element();
        let opening_element = jsx_element
            .opening_element
            .expect("JsxElement.opening_element");
        let closing_element = jsx_element
            .closing_element
            .expect("JsxElement.closing_element");
        let closing_tag_name = nodes[closing_element].tag_name();
        self.check_jsx_opening_like_element_or_opening_fragment(opening_element);
        // Perform resolution on the closing tag so that rename/go to
        // definition/etc work
        if let Some(tag_name) = closing_tag_name {
            if crate::utilities::is_jsx_intrinsic_tag_name(tag_name, &nodes) {
                self.get_intrinsic_tag_symbol(closing_element);
            } else {
                self.check_expression(tag_name);
            }
        }
        self.check_jsx_children(node, CheckMode::NORMAL);
    }

    /// `func (c *Checker) checkJsxExpression` (jsx.go:89).
    pub(crate) fn check_jsx_expression(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        self.check_grammar_jsx_expression(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let Some(expression) = nodes[node].expression() else {
            return self.error_type;
        };
        let dot_dot_dot = nodes[node].as_jsx_expression().dot_dot_dot_token.is_some();
        let t = self.check_expression_ex(expression, check_mode);
        if dot_dot_dot && t != self.any_type && !self.is_array_type(t) {
            self.error(
                Some(node),
                &diagnostics::JSX_spread_child_must_be_an_array_type,
                &[],
            );
        }
        t
    }

    /// `func (c *Checker) checkJsxSelfClosingElement` (jsx.go:101).
    pub(crate) fn check_jsx_self_closing_element(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let _ = check_mode;
        self.check_node_deferred(node);
        self.get_jsx_element_type_at(node)
    }

    /// `func (c *Checker) checkJsxSelfClosingElementDeferred` (jsx.go:106).
    pub(crate) fn check_jsx_self_closing_element_deferred(&mut self, node: NodeId) {
        self.check_jsx_opening_like_element_or_opening_fragment(node);
    }

    /// `func (c *Checker) checkJsxFragment` (jsx.go:110).
    pub(crate) fn check_jsx_fragment(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let opening_fragment = nodes[node]
            .as_jsx_fragment()
            .opening_fragment
            .expect("JsxFragment.opening_fragment");
        self.check_jsx_opening_like_element_or_opening_fragment(opening_fragment);
        // by default, jsx:'react' will use jsxFactory = React.createElement
        // and jsxFragmentFactory = React.Fragment
        // if jsxFactory compiler option is provided, ensure
        // jsxFragmentFactory compiler option or @jsxFrag pragma is provided
        // too
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        if let Some(source_file) = source_file {
            let sf = nodes[source_file].as_source_file();
            let jsx_pragma = ast::get_pragma_from_source_file(sf, "jsx").is_some();
            let jsxfrag_pragma = ast::get_pragma_from_source_file(sf, "jsxfrag").is_some();
            if self.compiler_options.get_jsx_transform_enabled()
                && (!self.compiler_options.jsx_factory.is_empty() || jsx_pragma)
                && self.compiler_options.jsx_fragment_factory.is_empty()
                && !jsxfrag_pragma
            {
                let message: &'static diagnostics::Message = if !self
                    .compiler_options
                    .jsx_factory
                    .is_empty()
                {
                    &diagnostics::The_jsxFragmentFactory_compiler_option_must_be_provided_to_use_JSX_fragments_with_the_jsxFactory_compiler_option
                } else {
                    &diagnostics::An_jsxFrag_pragma_is_required_when_using_an_jsx_pragma_with_JSX_fragments
                };
                self.error(Some(node), message, &[]);
            }
        }
        self.check_jsx_children(node, CheckMode::NORMAL);
        let t = self.get_jsx_element_type_at(node);
        if self.is_error_type(t) {
            self.any_type
        } else {
            t
        }
    }

    /// `func (c *Checker) checkJsxAttributes` (jsx.go:126).
    pub(crate) fn check_jsx_attributes(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        self.check_node_deferred(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent.expect("JsxAttributes.parent");
        self.create_jsx_attributes_type_from_attributes_property(parent, check_mode)
    }

    /// `func (c *Checker) checkJsxOpeningLikeElementOrOpeningFragment`
    /// (jsx.go:131).
    pub(crate) fn check_jsx_opening_like_element_or_opening_fragment(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_node_opening_like_element = ast::is_jsx_opening_like_element(&nodes[node]);
        if is_node_opening_like_element {
            self.check_grammar_jsx_element(node);
        }
        self.check_jsx_preconditions(node);
        self.mark_jsx_alias_referenced(node);
        let sig = self.get_resolved_signature(node, None, CheckMode::NORMAL);
        if let Some(sig) = sig {
            self.check_deprecated_signature(sig, node);
        }
        if is_node_opening_like_element {
            let element_type_constraint = self.get_jsx_element_type_type_at(node);
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let tag_name = nodes[node].tag_name().expect("opening-like tag name");
            if let Some(element_type_constraint) = element_type_constraint {
                let tag_type = if crate::utilities::is_jsx_intrinsic_tag_name(tag_name, &nodes) {
                    let text = nodes[tag_name].text(&nodes).into_owned();
                    self.get_string_literal_type(&text)
                } else {
                    self.check_expression(tag_name)
                };
                let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
                let relation = self.assignable_relation.clone();
                if !self.check_type_related_to_ex(
                    tag_type,
                    element_type_constraint,
                    &relation,
                    Some(tag_name),
                    Some(&diagnostics::Its_type_0_is_not_a_valid_JSX_element_type),
                    Some(&mut diags),
                ) {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((node).file_index());
                    let chain = ast::diagnostic::new_diagnostic_chain(
                        diags.first(),
                        &diagnostics::X_0_cannot_be_used_as_a_JSX_component,
                        &[tsc_scanner::utilities::get_text_of_node(tag_name, &nodes)],
                    );
                    self.add_diagnostic(&chain);
                }
            } else {
                let ref_kind = self.get_jsx_reference_kind(node);
                let elem_instance_type = sig
                    .map(|sig| self.get_return_type_of_signature(sig))
                    .unwrap_or(self.error_type);
                self.check_jsx_return_assignable_to_appropriate_bound(
                    ref_kind,
                    elem_instance_type,
                    node,
                );
            }
        }
    }

    /// `func (c *Checker) checkJsxPreconditions` (jsx.go:160).
    pub(crate) fn check_jsx_preconditions(&mut self, error_node: NodeId) {
        // Preconditions for using JSX
        if self.compiler_options.jsx == JsxEmit::None {
            self.error(
                Some(error_node),
                &diagnostics::Cannot_use_JSX_unless_the_jsx_flag_is_provided,
                &[],
            );
        }
        if self.no_implicit_any && self.get_jsx_element_type_at(error_node) == TypeId::NONE {
            self.error(
                Some(error_node),
                &diagnostics::JSX_element_implicitly_has_type_any_because_the_global_type_JSX_Element_does_not_exist,
                &[],
            );
        }
    }

    /// `func (c *Checker) checkJsxReturnAssignableToAppropriateBound`
    /// (jsx.go:170).
    pub(crate) fn check_jsx_return_assignable_to_appropriate_bound(
        &mut self,
        ref_kind: JsxReferenceKind,
        elem_instance_type: TypeId,
        opening_like_element: NodeId,
    ) {
        let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
        let relation = self.assignable_relation.clone();
        let tag_name = {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((opening_like_element).file_index());
            nodes[opening_like_element].tag_name()
        };
        match ref_kind {
            JsxReferenceKind::Function => {
                let sfc_return_constraint =
                    self.get_jsx_stateless_element_type_at(opening_like_element);
                if let Some(sfc_return_constraint) = sfc_return_constraint {
                    self.check_type_related_to_ex(
                        elem_instance_type,
                        sfc_return_constraint,
                        &relation,
                        tag_name,
                        Some(&diagnostics::Its_return_type_0_is_not_a_valid_JSX_element),
                        Some(&mut diags),
                    );
                }
            }
            JsxReferenceKind::Component => {
                let class_constraint = self.get_jsx_element_class_type_at(opening_like_element);
                if let Some(class_constraint) = class_constraint {
                    // Issue an error if this return type isn't assignable to
                    // JSX.ElementClass, failing that
                    self.check_type_related_to_ex(
                        elem_instance_type,
                        class_constraint,
                        &relation,
                        tag_name,
                        Some(&diagnostics::Its_instance_type_0_is_not_a_valid_JSX_element),
                        Some(&mut diags),
                    );
                }
            }
            _ => {
                let sfc_return_constraint =
                    self.get_jsx_stateless_element_type_at(opening_like_element);
                let class_constraint = self.get_jsx_element_class_type_at(opening_like_element);
                if sfc_return_constraint.is_none() || class_constraint.is_none() {
                    return;
                }
                let combined = self
                    .get_union_type(&[sfc_return_constraint.unwrap(), class_constraint.unwrap()]);
                self.check_type_related_to_ex(
                    elem_instance_type,
                    combined,
                    &relation,
                    tag_name,
                    Some(&diagnostics::Its_element_type_0_is_not_a_valid_JSX_element),
                    Some(&mut diags),
                );
            }
        }
        if !diags.is_empty() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((opening_like_element).file_index());
            let text = tag_name
                .map(|t| tsc_scanner::utilities::get_text_of_node(t, &nodes))
                .unwrap_or_default();
            let chain = ast::diagnostic::new_diagnostic_chain(
                diags.first(),
                &diagnostics::X_0_cannot_be_used_as_a_JSX_component,
                &[text],
            );
            self.add_diagnostic(&chain);
        }
    }

    /// `func (c *Checker) inferJsxTypeArguments` (jsx.go:198).
    pub(crate) fn infer_jsx_type_arguments(
        &mut self,
        node: NodeId,
        signature: SignatureId,
        check_mode: CheckMode,
        context: InferenceContextId,
    ) -> Vec<TypeId> {
        let param_type = self.get_effective_first_argument_for_jsx_signature(signature, node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let attributes = nodes[node].attributes().expect("jsx attributes");
        let check_attr_type = self.check_expression_with_contextual_type(
            attributes,
            param_type,
            Some(context),
            check_mode,
        );
        let mut inferences =
            std::mem::take(&mut self.inference_contexts[context.index()].inferences);
        self.infer_types(
            &mut inferences,
            check_attr_type,
            param_type,
            InferencePriority::NONE_PRIORITY,
            false,
        );
        self.inference_contexts[context.index()].inferences = inferences;
        self.get_inferred_types(context)
    }

    /// `func (c *Checker) getContextualTypeForJsxExpression` (jsx.go:205).
    pub(crate) fn get_contextual_type_for_jsx_expression(
        &mut self,
        node: NodeId,
        context_flags: ContextFlags,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent?;
        if ast::is_jsx_attribute_like(&nodes[parent]) {
            return self.get_contextual_type(node, context_flags);
        }
        if ast::is_jsx_element(&nodes[parent]) {
            return self.get_contextual_type_for_child_jsx_expression(parent, node, context_flags);
        }
        None
    }

    /// `func (c *Checker) getContextualTypeForJsxAttribute` (jsx.go:215).
    pub(crate) fn get_contextual_type_for_jsx_attribute(
        &mut self,
        attribute: NodeId,
        context_flags: ContextFlags,
    ) -> Option<TypeId> {
        // When we trying to resolve JsxOpeningLikeElement as a stateless
        // function element, we will already give its attributes a contextual
        // type which is a type of the parameter of the signature we are
        // trying out. If there is no contextual type (e.g. we are trying to
        // resolve stateful component), get attributes type from resolving
        // element's tagName
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((attribute).file_index());
        let parent = nodes[attribute].parent?;
        if ast::is_jsx_attribute(&nodes[attribute]) {
            let attributes_type = self.get_apparent_type_of_contextual_type(parent, context_flags);
            if attributes_type.is_none()
                || crate::types::is_type_any(&self.types, attributes_type.unwrap())
            {
                return None;
            }
            let name = nodes[attribute].name()?;
            let name_text = nodes[name].text(&nodes).into_owned();
            return self
                .get_type_of_property_of_contextual_type(attributes_type.unwrap(), &name_text);
        }
        self.get_contextual_type(parent, context_flags)
    }

    /// `func (c *Checker) getContextualJsxElementAttributesType` (jsx.go:229).
    pub(crate) fn get_contextual_jsx_element_attributes_type(
        &mut self,
        node: NodeId,
        context_flags: ContextFlags,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_jsx_opening_element(&nodes[node])
            && context_flags != ContextFlags::IGNORE_NODE_INFERENCES
        {
            let parent = nodes[node].parent?;
            let index = self.find_contextual_node(parent, context_flags == ContextFlags::NONE);
            if index >= 0 {
                // Contextually applied type is moved from attributes up to
                // the outer jsx attributes so when walking up from the
                // children they get hit _However_ to hit them from the
                // _attributes_ we must look for them here; otherwise we'll
                // used the declared type (as below) instead!
                return self.contextual_infos[index as usize].t;
            }
        }
        self.get_contextual_type_for_argument_at_index(node, 0)
    }

    /// `func (c *Checker) getContextualTypeForChildJsxExpression` (jsx.go:242).
    pub(crate) fn get_contextual_type_for_child_jsx_expression(
        &mut self,
        node: NodeId,
        child: NodeId,
        context_flags: ContextFlags,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let opening_element = nodes[node]
            .as_jsx_element()
            .opening_element
            .expect("JsxElement.opening_element");
        let attributes = nodes[opening_element].attributes()?;
        let attributes_type = self.get_apparent_type_of_contextual_type(attributes, context_flags);
        // JSX expression is in children of JSX Element, we will look for an
        // "children" attribute (we get the name from
        // JSX.ElementAttributesProperty)
        let jsx_namespace = self.get_jsx_namespace_at(Some(node));
        let jsx_children_property_name = self.get_jsx_element_children_property_name(jsx_namespace);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let children: Vec<NodeId> = nodes[node]
            .children()
            .map(|c| c.nodes.to_vec())
            .unwrap_or_default();
        if !(attributes_type.is_some()
            && !crate::types::is_type_any(&self.types, attributes_type.unwrap())
            && jsx_children_property_name != ast::symbol::INTERNAL_SYMBOL_NAME_MISSING
            && !jsx_children_property_name.is_empty())
        {
            return None;
        }
        let real_children = ast::get_semantic_jsx_children(&children, &nodes);
        let child_index = real_children.iter().position(|&c| c == child);
        let child_field_type = self.get_type_of_property_of_contextual_type(
            attributes_type.unwrap(),
            &jsx_children_property_name,
        )?;
        if real_children.len() == 1 {
            return Some(child_field_type);
        }
        let child_index = child_index.unwrap_or(0);
        self.map_type_ex(
            child_field_type,
            Rc::new(move |c: &mut Checker, t: TypeId| -> TypeId {
                if c.is_array_like_type(t) {
                    let index_t = c.get_number_literal_type(tsc_jsnum::Number(child_index as f64));
                    c.get_indexed_access_type(t, index_t)
                } else {
                    t
                }
            }),
            true, /*noReductions*/
        )
    }

    /// `func (c *Checker) discriminateContextualTypeByJSXAttributes`
    /// (jsx.go:266).
    pub(crate) fn discriminate_contextual_type_by_jsx_attributes(
        &mut self,
        node: NodeId,
        contextual_type: TypeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let key = crate::checker_types::DiscriminatedContextualTypeKey {
            node_id: ast::get_node_id(&nodes[node]),
            type_id: contextual_type,
        };
        if let Some(&discriminated) = self.discriminated_contextual_types.get(&key) {
            return discriminated;
        }
        let jsx_namespace = self.get_jsx_namespace_at(Some(node));
        let jsx_children_property_name = self.get_jsx_element_children_property_name(jsx_namespace);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let properties = nodes[node].properties().unwrap_or(&[]).to_vec();
        let discriminant_properties: Vec<NodeId> = properties
            .iter()
            .copied()
            .filter(|&p| {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((p).file_index());
                let symbol = nodes[p].symbol();
                if symbol.is_none() || !ast::is_jsx_attribute(&nodes[p]) {
                    return false;
                }
                let initializer = nodes[p].initializer();
                let name = self.sym(symbol.unwrap()).name.clone();
                (initializer.is_none() || self.is_possibly_discriminant_value(initializer.unwrap()))
                    && self.is_discriminant_property(contextual_type, &name)
            })
            .collect();
        let discriminant_members: Vec<SymbolId> = self
            .get_properties_of_type(contextual_type)
            .iter()
            .copied()
            .filter(|&s| {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                let node_symbol = nodes[node].symbol();
                if !self.sym(s).flags.intersects(ast::SymbolFlags::OPTIONAL)
                    || node_symbol.is_none()
                {
                    return false;
                }
                let element = nodes[node].parent.and_then(|p| nodes[p].parent);
                let s_name = self.sym(s).name.clone();
                if s_name == jsx_children_property_name
                    && element.is_some_and(|e| ast::is_jsx_element(&nodes[e]))
                {
                    let element_children: Vec<NodeId> = element
                        .and_then(|e| nodes[e].children().map(|c| c.nodes.to_vec()))
                        .unwrap_or_default();
                    if !ast::get_semantic_jsx_children(&element_children, &nodes).is_empty() {
                        return false;
                    }
                }
                !self.sym(node_symbol.unwrap()).members.has(&s_name)
                    && self.is_discriminant_property(contextual_type, &s_name)
            })
            .collect();
        let mut discriminator = crate::checker_d::ObjectLiteralDiscriminator {
            props: discriminant_properties,
            members: discriminant_members,
        };
        let discriminated = self.discriminate_type_by_discriminable_items(
            contextual_type,
            None,
            &mut discriminator,
        );
        self.discriminated_contextual_types
            .insert(key, discriminated);
        discriminated
    }

    /// `func (c *Checker) elaborateJsxComponents` (jsx.go:296).
    pub(crate) fn elaborate_jsx_components(
        &mut self,
        node: NodeId,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let mut diagnostic_output = diagnostic_output;
        let mut reported_error = false;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let props = nodes[node].properties().unwrap_or(&[]).to_vec();
        let parent = nodes[node].parent;
        for prop in props {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((prop).file_index());
            if !ast::is_jsx_spread_attribute(&nodes[prop]) {
                let prop_name = nodes[prop].name().expect("jsx attribute name");
                let prop_name_text = nodes[prop_name].text(&nodes).into_owned();
                if !is_hyphenated_jsx_name(&prop_name_text) {
                    let name_type = self.get_string_literal_type(&prop_name_text);
                    if !self
                        .types_handle()
                        .get(name_type)
                        .flags
                        .intersects(TypeFlags::NEVER)
                    {
                        let initializer = nodes[prop].initializer();
                        let relation = relation.clone();
                        reported_error = self.elaborate_element(
                            source,
                            target,
                            &relation,
                            Some(prop_name),
                            initializer,
                            name_type,
                            None,
                            None,
                            diagnostic_output.as_deref_mut(),
                        ) || reported_error;
                    }
                }
            }
        }
        if let Some(parent) = parent {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            if ast::is_jsx_opening_element(&nodes[parent])
                && nodes[parent]
                    .parent
                    .is_some_and(|pp| ast::is_jsx_element(&nodes[pp]))
            {
                let containing_element = nodes[parent].parent.unwrap(); // Containing JSXElement
                let jsx_namespace = self.get_jsx_namespace_at(Some(node));
                let mut children_prop_name =
                    self.get_jsx_element_children_property_name(jsx_namespace);
                if children_prop_name == ast::symbol::INTERNAL_SYMBOL_NAME_MISSING {
                    children_prop_name = "children".to_string();
                }
                let children_name_type = self.get_string_literal_type(&children_prop_name);
                let children_target_type = self.get_indexed_access_type(target, children_name_type);
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((containing_element).file_index());
                let children: Vec<NodeId> = nodes[containing_element]
                    .children()
                    .map(|c| c.nodes.to_vec())
                    .unwrap_or_default();
                let valid_children = ast::get_semantic_jsx_children(&children, &nodes);
                if valid_children.is_empty() {
                    return reported_error;
                }
                let more_than_one_real_children = valid_children.len() > 1;
                let iterable_type = {
                    let thunk = self.get_global_iterable_type.clone().expect("thunk");
                    thunk(self)
                };
                let (array_like_target_parts, non_array_like_target_parts);
                if iterable_type != self.empty_generic_type {
                    let any_iterable = self.create_iterable_type(self.any_type);
                    array_like_target_parts = self
                        .filter_type(children_target_type, &|c: &mut Checker, t: TypeId| {
                            c.is_type_assignable_to(t, any_iterable)
                        });
                    non_array_like_target_parts = self
                        .filter_type(children_target_type, &|c: &mut Checker, t: TypeId| {
                            !c.is_type_assignable_to(t, any_iterable)
                        });
                } else {
                    array_like_target_parts =
                        self.filter_type(children_target_type, &|c: &mut Checker, t: TypeId| {
                            c.is_array_like_type(t) || c.is_tuple_like_type(t)
                        });
                    non_array_like_target_parts =
                        self.filter_type(children_target_type, &|c: &mut Checker, t: TypeId| {
                            !(c.is_array_like_type(t) || c.is_tuple_like_type(t))
                        });
                }
                let invalid_text_diagnostic: InvalidTextDiagnostic = {
                    let children_prop_name = children_prop_name.clone();
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((node).file_index());
                    let tag_name = nodes[parent].tag_name();
                    let cache: Rc<RefCell<Option<Vec<String>>>> = Rc::new(RefCell::new(None));
                    Rc::new(RefCell::new(
                        move |c: &mut Checker| -> (&'static diagnostics::Message, Vec<String>) {
                            if let Some(args) = cache.borrow().as_ref() {
                                return (
                                    &diagnostics::X_0_components_don_t_accept_text_as_child_elements_Text_in_JSX_has_the_type_string_but_the_expected_type_of_1_is_2,
                                    args.clone(),
                                );
                            }
                            let tag_name_text = tag_name
                                .map(|t| {
                                    let __program = c.program.clone().expect("program");
                                    let nodes = __program.nodes((t).file_index());
                                    tsc_scanner::utilities::get_text_of_node(t, &nodes)
                                })
                                .unwrap_or_default();
                            let args = vec![
                                tag_name_text,
                                children_prop_name.clone(),
                                c.type_to_string(children_target_type),
                            ];
                            *cache.borrow_mut() = Some(args.clone());
                            (
                                &diagnostics::X_0_components_don_t_accept_text_as_child_elements_Text_in_JSX_has_the_type_string_but_the_expected_type_of_1_is_2,
                                args,
                            )
                        },
                    ))
                };
                if more_than_one_real_children {
                    if array_like_target_parts != self.never_type {
                        let checked_children =
                            self.check_jsx_children(containing_element, CheckMode::NORMAL);
                        let real_source = self.create_tuple_type(&checked_children);
                        let children = self.generate_jsx_children(
                            containing_element,
                            invalid_text_diagnostic.clone(),
                        );
                        let relation = relation.clone();
                        reported_error = self.elaborate_iterable_or_array_like_target_elementwise(
                            children,
                            real_source,
                            array_like_target_parts,
                            &relation,
                            diagnostic_output.as_deref_mut(),
                        ) || reported_error;
                    } else {
                        let relation = relation.clone();
                        let source_children =
                            self.get_indexed_access_type(source, children_name_type);
                        if !self.is_type_related_to(
                            source_children,
                            children_target_type,
                            &relation,
                        ) {
                            // arity mismatch
                            let __program = self.program.clone().expect("program");
                            let nodes = __program.nodes((containing_element).file_index());
                            let opening_tag = nodes[containing_element]
                                .as_jsx_element()
                                .opening_element
                                .and_then(|o| nodes[o].tag_name());
                            let children_target_str = self.type_to_string(children_target_type);
                            let diag = self.error(
                                opening_tag,
                                &diagnostics::This_JSX_tag_s_0_prop_expects_a_single_child_of_type_1_but_multiple_children_were_provided,
                                &[children_prop_name.clone(), children_target_str],
                            );
                            self.report_diagnostic(diag, diagnostic_output.as_deref_mut());
                            reported_error = true;
                        }
                    }
                } else if non_array_like_target_parts != self.never_type {
                    let child = valid_children[0];
                    let e = self.get_elaboration_element_for_jsx_child(
                        child,
                        Some(children_name_type),
                        invalid_text_diagnostic.clone(),
                    );
                    if e.error_node.is_some() {
                        let mut create_diagnostic = e.create_diagnostic;
                        let relation = relation.clone();
                        reported_error = self.elaborate_element(
                            source,
                            target,
                            &relation,
                            e.error_node,
                            e.inner_expression,
                            e.name_type.expect("name type"),
                            None,
                            create_diagnostic.as_deref_mut(),
                            diagnostic_output.as_deref_mut(),
                        ) || reported_error;
                    }
                } else {
                    let relation = relation.clone();
                    let source_children = self.get_indexed_access_type(source, children_name_type);
                    if !self.is_type_related_to(source_children, children_target_type, &relation) {
                        // arity mismatch
                        let __program = self.program.clone().expect("program");
                        let nodes = __program.nodes((containing_element).file_index());
                        let opening_tag = nodes[containing_element]
                            .as_jsx_element()
                            .opening_element
                            .and_then(|o| nodes[o].tag_name());
                        let children_target_str = self.type_to_string(children_target_type);
                        let diag = self.error(
                            opening_tag,
                            &diagnostics::This_JSX_tag_s_0_prop_expects_type_1_which_requires_multiple_children_but_only_a_single_child_was_provided,
                            &[children_prop_name.clone(), children_target_str],
                        );
                        self.report_diagnostic(diag, diagnostic_output.as_deref_mut());
                        reported_error = true;
                    }
                }
            }
        }
        reported_error
    }

    /// `func (c *Checker) generateJsxChildren` (jsx.go:376) — the Go `iter.Seq`
    /// is eagerly materialized; `getElaborationElementForJsxChild` has no
    /// ordering-sensitive side effects, so evaluation order is identical.
    pub(crate) fn generate_jsx_children(
        &mut self,
        node: NodeId,
        get_invalid_text_diagnostic: InvalidTextDiagnostic,
    ) -> Vec<JsxElaborationElement> {
        let mut result = Vec::new();
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let children: Vec<NodeId> = nodes[node]
            .children()
            .map(|c| c.nodes.to_vec())
            .unwrap_or_default();
        let mut member_offset = 0usize;
        for (i, child) in children.iter().enumerate() {
            let name_type =
                self.get_number_literal_type(tsc_jsnum::Number((i - member_offset) as f64));
            let e = self.get_elaboration_element_for_jsx_child(
                *child,
                Some(name_type),
                get_invalid_text_diagnostic.clone(),
            );
            if e.error_node.is_some() {
                result.push(e);
            } else {
                member_offset += 1;
            }
        }
        result
    }

    /// `func (c *Checker) getElaborationElementForJsxChild` (jsx.go:393).
    pub(crate) fn get_elaboration_element_for_jsx_child(
        &mut self,
        child: NodeId,
        name_type: Option<TypeId>,
        get_invalid_text_diagnostic: InvalidTextDiagnostic,
    ) -> JsxElaborationElement {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((child).file_index());
        match nodes[child].kind {
            ast::Kind::JsxExpression => {
                // child is of the type of the expression
                let inner_expression = nodes[child].expression();
                JsxElaborationElement {
                    error_node: Some(child),
                    inner_expression,
                    name_type,
                    create_diagnostic: None,
                }
            }
            ast::Kind::JsxText => {
                if nodes[child].as_jsx_text().contains_only_trivia_white_spaces {
                    // Whitespace only jsx text isn't real jsx text
                    return JsxElaborationElement {
                        error_node: None,
                        inner_expression: None,
                        name_type: None,
                        create_diagnostic: None,
                    };
                }
                // child is a string
                let get_invalid_text_diagnostic = get_invalid_text_diagnostic.clone();
                JsxElaborationElement {
                    error_node: Some(child),
                    inner_expression: None,
                    name_type,
                    create_diagnostic: Some(Box::new(
                        move |c: &mut Checker, prop: Option<NodeId>| {
                            let (error_message, error_args) =
                                (get_invalid_text_diagnostic.borrow_mut())(c);
                            let __program = c.program.clone().expect("program");
                            let nodes = __program.nodes((child).file_index());
                            crate::utilities::new_diagnostic_for_node(
                                prop,
                                &nodes,
                                error_message,
                                &error_args,
                            )
                        },
                    )),
                }
            }
            ast::Kind::JsxElement | ast::Kind::JsxSelfClosingElement | ast::Kind::JsxFragment => {
                // child is of type JSX.Element
                JsxElaborationElement {
                    error_node: Some(child),
                    inner_expression: Some(child),
                    name_type,
                    create_diagnostic: None,
                }
            }
            _ => panic!("Unhandled case in get_elaboration_element_for_jsx_child"),
        }
    }

    /// `func (c *Checker) elaborateIterableOrArrayLikeTargetElementwise`
    /// (jsx.go:420) — the Go `iter.Seq` param arrives as an eagerly
    /// materialized `Vec` (see `generateJsxChildren`).
    pub(crate) fn elaborate_iterable_or_array_like_target_elementwise(
        &mut self,
        elements: Vec<JsxElaborationElement>,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let mut diagnostic_output = diagnostic_output;
        let tuple_or_array_like_target_parts = self
            .filter_type(target, &|c: &mut Checker, t: TypeId| {
                c.is_array_like_type(t) || c.is_tuple_like_type(t)
            });
        let non_tuple_or_array_like_target_parts = self
            .filter_type(target, &|c: &mut Checker, t: TypeId| {
                !(c.is_array_like_type(t) || c.is_tuple_like_type(t))
            });
        // If `nonTupleOrArrayLikeTargetParts` is not `never`, then that
        // should mean `Iterable` is defined.
        let mut iteration_type = None;
        if non_tuple_or_array_like_target_parts != self.never_type {
            iteration_type = self.get_iteration_type_of_iterable(
                IterationUse::FOR_OF,
                IterationTypeKind::Yield,
                non_tuple_or_array_like_target_parts,
                None, /*errorNode*/
            );
        }
        let mut reported_error = false;
        for e in elements {
            let prop = e.error_node;
            let next = e.inner_expression;
            let name_type = e.name_type.expect("name type");
            let mut target_prop_type = iteration_type;
            let mut target_indexed_prop_type = None;
            if tuple_or_array_like_target_parts != self.never_type {
                target_indexed_prop_type = self.get_best_match_indexed_access_type_or_undefined(
                    source,
                    tuple_or_array_like_target_parts,
                    name_type,
                );
            }
            if let Some(t) = target_indexed_prop_type {
                if !self
                    .types_handle()
                    .get(t)
                    .flags
                    .intersects(TypeFlags::INDEXED_ACCESS)
                {
                    if let Some(iteration_type) = iteration_type {
                        target_prop_type = Some(self.get_union_type(&[iteration_type, t]));
                    } else {
                        target_prop_type = Some(t);
                    }
                }
            }
            let Some(mut target_prop_type) = target_prop_type else {
                continue;
            };
            let Some(mut source_prop_type) = self.get_indexed_access_type_or_undefined(
                source,
                name_type,
                AccessFlags::NONE,
                None,
                None,
            ) else {
                continue;
            };
            let prop_name = self.get_property_name_from_index(name_type, None);
            let relation = relation.clone();
            if !self.check_type_related_to(source_prop_type, target_prop_type, &relation, None) {
                let elaborated = next.is_some()
                    && self.elaborate_error(
                        next,
                        source_prop_type,
                        target_prop_type,
                        &relation,
                        None, /*headMessage*/
                        diagnostic_output.as_deref_mut(),
                    );
                reported_error = true;
                if !elaborated {
                    // Issue error on the prop itself, since the prop couldn't
                    // elaborate the error. Use the expression type, if
                    // available.
                    let mut specific_source = source_prop_type;
                    if let Some(next) = next {
                        specific_source = self
                            .check_expression_for_mutable_location_with_contextual_type(
                                next,
                                source_prop_type,
                            );
                    }
                    if let Some(mut create_diagnostic) = e.create_diagnostic {
                        // Use the custom diagnostic factory if provided
                        // (e.g., for JSX text children with dynamic error
                        // messages)
                        let diag = create_diagnostic(self, prop);
                        self.report_diagnostic(Some(diag), diagnostic_output.as_deref_mut());
                    } else if self.exact_optional_property_types
                        && self.is_exact_optional_property_mismatch(
                            Some(specific_source),
                            Some(target_prop_type),
                        )
                    {
                        // `prop` is `e.errorNode` — always present on the
                        // paths that reach this (Go would nil-deref here).
                        let __program = self.program.clone().expect("program");
                        let nodes = __program.nodes((prop.expect("prop")).file_index());
                        let diag = crate::checker_b::create_diagnostic_for_node(
                            prop,
                            &nodes,
                            &diagnostics::Type_0_is_not_assignable_to_type_1_with_exactOptionalPropertyTypes_Colon_true_Consider_adding_undefined_to_the_type_of_the_target,
                            &[
                                self.type_to_string(specific_source),
                                self.type_to_string(target_prop_type),
                            ],
                        );
                        self.report_diagnostic(Some(diag), diagnostic_output.as_deref_mut());
                    } else {
                        let target_is_optional =
                            prop_name != ast::symbol::INTERNAL_SYMBOL_NAME_MISSING && {
                                let s = self
                                    .get_property_of_type(
                                        tuple_or_array_like_target_parts,
                                        &prop_name,
                                    )
                                    .unwrap_or(self.unknown_symbol);
                                self.sym(s).flags.intersects(ast::SymbolFlags::OPTIONAL)
                            };
                        let source_is_optional =
                            prop_name != ast::symbol::INTERNAL_SYMBOL_NAME_MISSING && {
                                let s = self
                                    .get_property_of_type(source, &prop_name)
                                    .unwrap_or(self.unknown_symbol);
                                self.sym(s).flags.intersects(ast::SymbolFlags::OPTIONAL)
                            };
                        target_prop_type =
                            self.remove_missing_type(target_prop_type, target_is_optional);
                        source_prop_type = self.remove_missing_type(
                            source_prop_type,
                            target_is_optional && source_is_optional,
                        );
                        let result = self.check_type_related_to_ex(
                            specific_source,
                            target_prop_type,
                            &relation,
                            prop,
                            None,
                            diagnostic_output.as_deref_mut(),
                        );
                        if result && specific_source != source_prop_type {
                            // If for whatever reason the expression type
                            // doesn't yield an error, make sure we still
                            // issue an error on the sourcePropType
                            self.check_type_related_to_ex(
                                source_prop_type,
                                target_prop_type,
                                &relation,
                                prop,
                                None,
                                diagnostic_output.as_deref_mut(),
                            );
                        }
                    }
                }
            }
        }
        reported_error
    }

    /// `func (c *Checker) getSuggestedSymbolForNonexistentJSXAttribute`
    /// (jsx.go:485).
    pub(crate) fn get_suggested_symbol_for_nonexistent_jsx_attribute(
        &mut self,
        name: &str,
        containing_type: TypeId,
    ) -> Option<SymbolId> {
        let properties = self.get_properties_of_type(containing_type);
        let jsx_specific = match name {
            "for" => properties
                .iter()
                .copied()
                .find(|&x| self.sym(x).name == "htmlFor"),
            "class" => properties
                .iter()
                .copied()
                .find(|&x| self.sym(x).name == "className"),
            _ => None,
        };
        if jsx_specific.is_some() {
            return jsx_specific;
        }
        self.get_spelling_suggestion_for_name(name, properties, ast::SymbolFlags::VALUE)
    }

    /// `func (c *Checker) getJSXFragmentType` (jsx.go:500).
    pub(crate) fn get_jsx_fragment_type(&mut self, node: NodeId) -> TypeId {
        // An opening fragment is required in order for `getJsxNamespace` to
        // give the fragment factory
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let file =
            ast::get_source_file_of_node(Some(node), &nodes).expect("jsx fragment source file");
        if let Some(t) = self.source_file_links.get(file).jsx_fragment_type {
            return t;
        }
        let jsx_fragment_factory_name = self.get_jsx_namespace(node);
        // #38720/60122, allow null as jsxFragmentFactory
        let should_resolve_factory_reference = (self.compiler_options.jsx == JsxEmit::React
            || !self.compiler_options.jsx_fragment_factory.is_empty())
            && jsx_fragment_factory_name != "null";
        if !should_resolve_factory_reference {
            let t = self.any_type;
            self.source_file_links.get(file).jsx_fragment_type = Some(t);
            return t;
        }
        let mut jsx_factory_symbol = self.get_jsx_namespace_container_for_implicit_import(node);
        if jsx_factory_symbol.is_none() {
            let should_module_ref_err = self.compiler_options.jsx != JsxEmit::Preserve
                && self.compiler_options.jsx != JsxEmit::ReactNative;
            let mut flags = ast::SymbolFlags::VALUE;
            if !should_module_ref_err {
                flags = flags.without(ast::SymbolFlags::ENUM);
            }
            jsx_factory_symbol = self.resolve_name_thunk(
                Some(node),
                &jsx_fragment_factory_name,
                flags,
                Some(
                    &diagnostics::Using_JSX_fragments_requires_fragment_factory_0_to_be_in_scope_but_it_could_not_be_found,
                ),
                true,  /*isUse*/
                false, /*excludeGlobals*/
            );
        }
        let Some(jsx_factory_symbol) = jsx_factory_symbol else {
            let t = self.error_type;
            self.source_file_links.get(file).jsx_fragment_type = Some(t);
            return t;
        };
        if self.sym(jsx_factory_symbol).name == REACT_NAMES.fragment {
            let t = self.get_type_of_symbol(jsx_factory_symbol);
            self.source_file_links.get(file).jsx_fragment_type = Some(t);
            return t;
        }
        let mut resolved_alias = jsx_factory_symbol;
        if self
            .sym(jsx_factory_symbol)
            .flags
            .intersects(ast::SymbolFlags::ALIAS)
        {
            resolved_alias = self.resolve_alias(jsx_factory_symbol);
        }
        let react_exports = self.get_exports_of_symbol(resolved_alias);
        let type_symbol = self.get_symbol(
            &react_exports,
            REACT_NAMES.fragment,
            ast::SymbolFlags::BLOCK_SCOPED_VARIABLE,
        );
        let t = if let Some(type_symbol) = type_symbol {
            self.get_type_of_symbol(type_symbol)
        } else {
            self.error_type
        };
        self.source_file_links.get(file).jsx_fragment_type = Some(t);
        t
    }

    /// `func (c *Checker) resolveJsxOpeningLikeElement` (jsx.go:545).
    pub(crate) fn resolve_jsx_opening_like_element(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_jsx_open_fragment = ast::is_jsx_opening_fragment(&nodes[node]);
        let tag_name = nodes[node].tag_name();
        let attributes = nodes[node].attributes();
        let expr_types;
        if !is_jsx_open_fragment {
            if crate::utilities::is_jsx_intrinsic_tag_name(tag_name.expect("tag name"), &nodes) {
                let result = self.get_intrinsic_attributes_type_from_jsx_opening_like_element(node);
                let fake_signature = self.create_signature_for_jsx_intrinsic(node, result);
                let effective_first_arg =
                    self.get_effective_first_argument_for_jsx_signature(fake_signature, node);
                let attr_type = self.check_expression_with_contextual_type(
                    attributes.expect("attributes"),
                    effective_first_arg,
                    None, /*inferenceContext*/
                    CheckMode::NORMAL,
                );
                self.check_type_assignable_to_and_optionally_elaborate(
                    attr_type, result, tag_name, attributes, None, None,
                );
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                let type_arguments = nodes[node].type_arguments().unwrap_or(&[]).to_vec();
                if !type_arguments.is_empty() {
                    self.check_source_elements(&type_arguments);
                    let source_file =
                        ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
                    let type_argument_list = nodes[node]
                        .type_argument_list()
                        .expect("type argument list");
                    let sf_text = nodes[source_file].as_source_file().text.clone();
                    let loc = TextRange::new(
                        tsc_scanner::scanner::skip_trivia(&sf_text, type_argument_list.loc.pos()),
                        type_argument_list.loc.end(),
                    );
                    let diagnostic = ast::diagnostic::new_diagnostic(
                        Some(ast::diagnostic::DiagnosticFile::from_node(
                            source_file,
                            &nodes,
                        )),
                        loc,
                        &diagnostics::Expected_0_type_arguments_but_got_1,
                        &["0".to_string(), type_arguments.len().to_string()],
                    );
                    self.add_diagnostic(&diagnostic);
                }
                return fake_signature;
            }
            expr_types = self.check_expression(tag_name.expect("tag name"));
        } else {
            expr_types = self.get_jsx_fragment_type(node);
        }
        let apparent_type = self.get_apparent_type(expr_types);
        if self.is_error_type(apparent_type) {
            return self.resolve_error_call(node);
        }
        let signatures = self.get_uninstantiated_jsx_signatures_of_type(expr_types, node);
        if self.is_untyped_function_call(expr_types, apparent_type, signatures.len() as i32, 0) {
            return self.resolve_untyped_call(node);
        }
        if signatures.is_empty() {
            // We found no signatures at all, which is an error
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            if is_jsx_open_fragment {
                let text = tsc_scanner::utilities::get_text_of_node(node, &nodes);
                self.error(
                    Some(node),
                    &diagnostics::JSX_element_type_0_does_not_have_any_construct_or_call_signatures,
                    &[text],
                );
            } else if let Some(tag_name) = tag_name {
                let text = tsc_scanner::utilities::get_text_of_node(tag_name, &nodes);
                self.error(
                    Some(tag_name),
                    &diagnostics::JSX_element_type_0_does_not_have_any_construct_or_call_signatures,
                    &[text],
                );
            }
            return self.resolve_error_call(node);
        }
        self.resolve_call(
            node,
            signatures,
            candidates_out_array,
            check_mode,
            crate::types::SignatureFlags::NONE,
            None,
        )
    }

    /// `func (c *Checker) checkApplicableSignatureForJsxCallLikeElement`
    /// (jsx.go:591).
    ///
    /// Check if the given signature can possibly be a signature called by the
    /// JSX opening-like element.
    /// `node` a JSX opening-like element we are trying to figure its call
    /// signature; `signature` a candidate signature we are trying whether it
    /// is a call signature; `relation` a relationship to check parameter and
    /// argument type.
    pub(crate) fn check_applicable_signature_for_jsx_call_like_element(
        &mut self,
        node: NodeId,
        signature: SignatureId,
        relation: &SharedRelation,
        check_mode: CheckMode,
        report_errors: bool,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        // Stateless function components can have maximum of three arguments:
        // "props", "context", and "updater". However "context" and "updater"
        // are implicit and can't be specify by users. Only the first
        // parameter, props, can be specified by users through attributes
        // property.
        let mut diagnostic_output = diagnostic_output;
        let param_type = self.get_effective_first_argument_for_jsx_signature(signature, node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_opening_fragment = ast::is_jsx_opening_fragment(&nodes[node]);
        let attributes = nodes[node].attributes();
        let attributes_type = if is_opening_fragment {
            self.create_jsx_attributes_type_from_attributes_property(node, CheckMode::NORMAL)
        } else {
            self.check_expression_with_contextual_type(
                attributes.expect("attributes"),
                param_type,
                None, /*inferenceContext*/
                check_mode,
            )
        };
        let check_attributes_type;
        if check_mode.intersects(CheckMode::SKIP_CONTEXT_SENSITIVE) {
            check_attributes_type = self.get_regular_type_of_object_literal(attributes_type);
        } else {
            check_attributes_type = attributes_type;
        }
        if !self.check_tag_name_does_not_expect_too_many_arguments(
            node,
            report_errors,
            diagnostic_output.as_deref_mut(),
        ) {
            return false;
        }
        let mut error_node = None;
        if report_errors {
            if is_opening_fragment {
                error_node = Some(node);
            } else {
                error_node = tag_name_or_none(self, node);
            }
        }
        let attributes = if is_opening_fragment {
            None
        } else {
            attributes
        };
        self.check_type_related_to_and_optionally_elaborate(
            check_attributes_type,
            param_type,
            relation,
            error_node,
            attributes,
            None,
            diagnostic_output,
        )
    }

    /// `checkTagNameDoesNotExpectTooManyArguments` — the Go local closure
    /// inside `checkApplicableSignatureForJsxCallLikeElement` (jsx.go:603).
    fn check_tag_name_does_not_expect_too_many_arguments(
        &mut self,
        node: NodeId,
        report_errors: bool,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let mut diagnostic_output = diagnostic_output;
        if self
            .get_jsx_namespace_container_for_implicit_import(node)
            .is_some()
        {
            return true; // factory is implicitly jsx/jsxdev - assume it fits
            // the bill, since we don't strongly look for the jsx/jsxs/jsxDEV
            // factory APIs anywhere else (at least not yet)
        }
        // We assume fragments have the correct arity since the node does not
        // have attributes
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let tag_name = nodes[node].tag_name();
        let mut tag_type = None;
        if (ast::is_jsx_opening_element(&nodes[node])
            || ast::is_jsx_self_closing_element(&nodes[node]))
            && tag_name.is_some_and(|t| {
                !crate::utilities::is_jsx_intrinsic_tag_name(t, &nodes)
                    && !ast::is_jsx_namespaced_name(&nodes[t])
            })
        {
            tag_type = Some(self.check_expression(tag_name.unwrap()));
        }
        let Some(tag_type) = tag_type else {
            return true;
        };
        let tag_call_signatures = self.get_signatures_of_type(tag_type, SignatureKind::Call);
        if tag_call_signatures.is_empty() {
            return true;
        }
        let Some(factory) = self.get_jsx_factory_entity(node) else {
            return true;
        };
        let factory_symbol = self.resolve_entity_name(
            Some(factory),
            ast::SymbolFlags::VALUE,
            true,  /*ignoreErrors*/
            false, /*dontResolveAlias*/
            Some(node),
        );
        let Some(factory_symbol) = factory_symbol else {
            return true;
        };
        let factory_type = self.get_type_of_symbol(factory_symbol);
        let call_signatures = self.get_signatures_of_type(factory_type, SignatureKind::Call);
        if call_signatures.is_empty() {
            return true;
        }
        let mut has_first_param_signatures = false;
        let mut max_param_count = 0usize;
        // Check that _some_ first parameter expects a FC-like thing, and that
        // some overload of the SFC expects an acceptable number of arguments
        for sig in &call_signatures {
            let firstparam = self.get_type_at_position(*sig, 0);
            let signatures_of_param = self.get_signatures_of_type(firstparam, SignatureKind::Call);
            if signatures_of_param.is_empty() {
                continue;
            }
            for param_sig in signatures_of_param {
                has_first_param_signatures = true;
                if self.has_effective_rest_parameter(param_sig) {
                    return true; // some signature has a rest param, so
                    // function components can have an arbitrary number of
                    // arguments
                }
                let param_count = self.get_parameter_count(param_sig);
                if param_count > max_param_count {
                    max_param_count = param_count;
                }
            }
        }
        if !has_first_param_signatures {
            // Not a single signature had a first parameter which expected a
            // signature - for back compat, and to guard against generic
            // factories which won't have signatures directly, do not error
            return true;
        }
        let mut absolute_min_arg_count = i32::MAX;
        for tag_sig in &tag_call_signatures {
            let tag_required_arg_count = self.get_min_argument_count(*tag_sig);
            if tag_required_arg_count < absolute_min_arg_count {
                absolute_min_arg_count = tag_required_arg_count;
            }
        }
        if absolute_min_arg_count as usize <= max_param_count {
            return true; // some signature accepts the number of arguments the
            // function component provides
        }
        if report_errors {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let tag_name = nodes[node].tag_name();
            // We will not report errors in this function for fragments, since
            // we do not check them in this function
            let tag_name_str = tag_name
                .map(|t| crate::utilities::entity_name_to_string(t, &nodes))
                .unwrap_or_default();
            let factory_str = {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((factory).file_index());
                crate::utilities::entity_name_to_string(factory, &nodes)
            };
            let diag = crate::utilities::new_diagnostic_for_node(
                tag_name,
                &nodes,
                &diagnostics::Tag_0_expects_at_least_1_arguments_but_the_JSX_factory_2_provides_at_most_3,
                &[
                    tag_name_str.clone(),
                    absolute_min_arg_count.to_string(),
                    factory_str,
                    max_param_count.to_string(),
                ],
            );
            if let Some(tag_name) = tag_name {
                if let Some(tag_name_symbol) = self.get_symbol_at_location(tag_name, false) {
                    if let Some(value_declaration) = self.sym(tag_name_symbol).value_declaration {
                        let __program = self.program.clone().expect("program");
                        let nodes = __program.nodes((value_declaration).file_index());
                        let related = crate::utilities::new_diagnostic_for_node(
                            Some(value_declaration),
                            &nodes,
                            &diagnostics::X_0_is_declared_here,
                            &[tag_name_str],
                        );
                        ast::diagnostic::lock_diagnostic(&diag).add_related_info(Some(related));
                    }
                }
            }
            self.report_diagnostic(Some(diag), diagnostic_output.as_deref_mut());
        }
        false
    }

    /// `func (c *Checker) createJsxAttributesTypeFromAttributesProperty`
    /// (jsx.go:710).
    ///
    /// Get attributes type of the JSX opening-like element. The result is
    /// from resolving "attributes" property of the opening-like element.
    /// Because this function calls `getSpreadType`, it needs to use the same
    /// checks as `checkObjectLiteral`, which also calls `getSpreadType`.
    pub(crate) fn create_jsx_attributes_type_from_attributes_property(
        &mut self,
        opening_like_element: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let mut all_attributes_table = if self.strict_null_checks {
            Some(ast::SymbolTable::new())
        } else {
            None
        };
        let mut attributes_table = ast::SymbolTable::new();
        let mut attributes_symbol = None;
        let mut attribute_parent = opening_like_element;
        let mut spread = self.empty_jsx_object_type;
        let mut has_spread_any_type = false;
        let mut type_to_intersect = None;
        let mut explicitly_specify_children_attribute = false;
        let mut object_flags = ObjectFlags::JSX_ATTRIBUTES;
        let jsx_namespace = self.get_jsx_namespace_at(Some(opening_like_element));
        let jsx_children_property_name = self.get_jsx_element_children_property_name(jsx_namespace);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((opening_like_element).file_index());
        let is_jsx_open_fragment = ast::is_jsx_opening_fragment(&nodes[opening_like_element]);
        if !is_jsx_open_fragment {
            let attributes = nodes[opening_like_element]
                .attributes()
                .expect("jsx attributes");
            attributes_symbol = nodes[attributes].symbol();
            attribute_parent = attributes;
            let contextual_type = self.get_contextual_type(attributes, ContextFlags::NONE);
            // Create anonymous type from given attributes symbol table.
            // `symbol` is a symbol of JsxAttributes containing attributes
            // corresponding to attributesTable; `attributesTable` is a
            // symbol table of attributes property.
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((attributes).file_index());
            let props = nodes[attributes].properties().unwrap_or(&[]).to_vec();
            for attribute_decl in props {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((attribute_decl).file_index());
                let member = nodes[attribute_decl].symbol().expect("attribute symbol");
                if ast::is_jsx_attribute(&nodes[attribute_decl]) {
                    let expr_type = self.check_jsx_attribute(attribute_decl, check_mode);
                    object_flags |= self.types_handle().get(expr_type).object_flags
                        & ObjectFlags::PROPAGATING_FLAGS;
                    let member_flags = self.sym(member).flags;
                    let member_name = self.sym(member).name.clone();
                    let attribute_symbol =
                        self.new_symbol(ast::SymbolFlags::PROPERTY | member_flags, &member_name);
                    {
                        let member_decls = self.sym(member).declarations.clone();
                        let member_parent = self.sym(member).parent;
                        let member_value_decl = self.sym(member).value_declaration;
                        let mut sym_mut = self.sym_mut(attribute_symbol);
                        sym_mut.declarations = member_decls;
                        sym_mut.parent = member_parent;
                        if member_value_decl.is_some() {
                            sym_mut.value_declaration = member_value_decl;
                        }
                    }
                    {
                        let links = self.value_symbol_links.get(attribute_symbol);
                        links.resolved_type = Some(expr_type);
                        links.target = Some(member);
                    }
                    attributes_table.set(member_name.clone(), attribute_symbol);
                    if let Some(table) = all_attributes_table.as_mut() {
                        table.set(member_name.clone(), attribute_symbol);
                    }
                    let attr_name = nodes[attribute_decl]
                        .name()
                        .map(|n| nodes[n].text(&nodes).into_owned())
                        .unwrap_or_default();
                    if attr_name == jsx_children_property_name {
                        explicitly_specify_children_attribute = true;
                    }
                    if contextual_type.is_some()
                        && check_mode.intersects(CheckMode::INFERENTIAL)
                        && !check_mode.intersects(CheckMode::SKIP_CONTEXT_SENSITIVE)
                        && self.is_context_sensitive(attribute_decl)
                    {
                        let inference_context = self.get_inference_context(attributes);
                        debug_assert!(inference_context.is_some());
                        // In CheckMode.Inferential we should always have an
                        // inference context
                        let inference_node = nodes[attribute_decl]
                            .initializer()
                            .and_then(|i| nodes[i].expression())
                            .expect("jsx attribute initializer expression");
                        self.add_intra_expression_inference_site(
                            inference_context,
                            inference_node,
                            expr_type,
                        );
                    }
                } else {
                    debug_assert!(nodes[attribute_decl].kind == ast::Kind::JsxSpreadAttribute);
                    if !attributes_table.is_empty() {
                        // `createJsxAttributesType()` runs (and mutates
                        // `objectFlags`) before `objectFlags` is read as the
                        // getSpreadType argument — preserved here by the
                        // hoist (Rust forbids the nested `&mut self` call).
                        let attrs_type = self.create_jsx_attributes_type(
                            attributes_symbol,
                            &mut attributes_table,
                            &mut object_flags,
                        );
                        spread = self.get_spread_type(
                            spread,
                            attrs_type,
                            attributes_symbol,
                            object_flags,
                            false, /*readonly*/
                        );
                    }
                    let expression = nodes[attribute_decl]
                        .expression()
                        .expect("spread expression");
                    let checked_expr_type =
                        self.check_expression_ex(expression, check_mode & CheckMode::INFERENTIAL);
                    let expr_type = self.get_reduced_type(checked_expr_type);
                    if crate::types::is_type_any(&self.types, expr_type) {
                        has_spread_any_type = true;
                    }
                    if self.is_valid_spread_type(expr_type) {
                        spread = self.get_spread_type(
                            spread,
                            expr_type,
                            attributes_symbol,
                            object_flags,
                            false, /*readonly*/
                        );
                        if let Some(table) = all_attributes_table.as_ref() {
                            self.check_spread_prop_overrides(
                                expr_type,
                                table.clone(),
                                attribute_decl,
                            );
                        }
                    } else {
                        self.error(
                            Some(expression),
                            &diagnostics::Spread_types_may_only_be_created_from_object_types,
                            &[],
                        );
                        type_to_intersect = Some(match type_to_intersect {
                            Some(t) => self.get_intersection_type(&[t, expr_type]),
                            None => expr_type,
                        });
                    }
                }
            }
            if !has_spread_any_type && !attributes_table.is_empty() {
                let attrs_type = self.create_jsx_attributes_type(
                    attributes_symbol,
                    &mut attributes_table,
                    &mut object_flags,
                );
                spread = self.get_spread_type(
                    spread,
                    attrs_type,
                    attributes_symbol,
                    object_flags,
                    false, /*readonly*/
                );
            }
        }
        if self.parent_has_semantic_jsx_children(opening_like_element) {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((opening_like_element).file_index());
            let parent = nodes[opening_like_element].parent.expect("jsx parent");
            let child_types = self.check_jsx_children(parent, check_mode);
            if !has_spread_any_type
                && jsx_children_property_name != ast::symbol::INTERNAL_SYMBOL_NAME_MISSING
                && !jsx_children_property_name.is_empty()
            {
                // Error if there is a attribute named "children" explicitly
                // specified and children element. This is because children
                // element will overwrite the value from attributes. Note: we
                // will not warn "children" attribute overwritten if
                // "children" attribute is specified in object spread.
                if explicitly_specify_children_attribute {
                    self.error(
                        Some(attribute_parent),
                        &diagnostics::X_0_are_specified_twice_The_attribute_named_0_will_be_overwritten,
                        &[jsx_children_property_name.clone()],
                    );
                }
                let mut children_contextual_type = None;
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((opening_like_element).file_index());
                if ast::is_jsx_opening_element(&nodes[opening_like_element]) {
                    if let Some(attributes) = nodes[opening_like_element].attributes() {
                        if let Some(contextual_type) = self
                            .get_apparent_type_of_contextual_type(attributes, ContextFlags::NONE)
                        {
                            children_contextual_type = self
                                .get_type_of_property_of_contextual_type(
                                    contextual_type,
                                    &jsx_children_property_name,
                                );
                        }
                    }
                }
                // If there are children in the body of JSX element, create
                // dummy attribute "children" with the union of children types
                // so that it will pass the attribute checking process
                let children_prop_symbol =
                    self.new_symbol(ast::SymbolFlags::PROPERTY, &jsx_children_property_name);
                // Compute before taking the `value_symbol_links` guard so
                // the `&mut self` calls below don't overlap it.
                let children_resolved_type = if child_types.len() == 1 {
                    Some(child_types[0])
                } else if children_contextual_type.is_some_and(|t| {
                    crate::checker_d::some_type(self, t, |c: &mut Checker, t: TypeId| {
                        c.is_tuple_like_type(t)
                    })
                }) {
                    Some(self.create_tuple_type(&child_types))
                } else {
                    let union = self.get_union_type(&child_types);
                    Some(self.create_array_type(union))
                };
                self.value_symbol_links
                    .get(children_prop_symbol)
                    .resolved_type = children_resolved_type;
                // Fake up a property declaration for the children
                let file_index = opening_like_element.file_index();
                let declaration = {
                    let program = self.program.clone().expect("program");
                    let mut arena = program.nodes_mut(file_index);
                    let old_file_index = self.factory.file_index();
                    self.factory.set_file_index(file_index);
                    let name = self
                        .factory
                        .new_identifier(&mut arena, &jsx_children_property_name);
                    let decl = self.factory.new_property_signature_declaration(
                        &mut arena,
                        None,
                        Some(name),
                        None, /*postfixToken*/
                        None, /*type*/
                        None, /*initializer*/
                    );
                    self.factory.set_file_index(old_file_index);
                    decl
                };
                self.sym_mut(children_prop_symbol).value_declaration = Some(declaration);
                {
                    let program = self.program.clone().expect("program");
                    let mut arena = program.nodes_mut(file_index);
                    arena[declaration].parent = Some(attribute_parent);
                    arena[declaration]
                        .as_property_signature_declaration_mut()
                        .declaration_base
                        .symbol = Some(children_prop_symbol);
                }
                let mut child_prop_map = ast::SymbolTable::new();
                child_prop_map.set(jsx_children_property_name.clone(), children_prop_symbol);
                let propagating =
                    self.get_propagating_flags_of_types(&child_types, TypeFlags::NONE);
                let anon =
                    self.new_anonymous_type(attributes_symbol, child_prop_map, &[], &[], &[]);
                spread = self.get_spread_type(
                    spread,
                    anon,
                    attributes_symbol,
                    object_flags | propagating,
                    false, /*readonly*/
                );
            }
        }
        if has_spread_any_type {
            return self.any_type;
        }
        if let Some(type_to_intersect) = type_to_intersect {
            if spread != self.empty_jsx_object_type {
                return self.get_intersection_type(&[type_to_intersect, spread]);
            }
            return type_to_intersect;
        }
        if spread == self.empty_jsx_object_type {
            return self.create_jsx_attributes_type(
                attributes_symbol,
                &mut attributes_table,
                &mut object_flags,
            );
        }
        spread
    }

    /// `createJsxAttributesType` — the Go local closure inside
    /// `createJsxAttributesTypeFromAttributesProperty` (jsx.go:723). Takes the
    /// attributes table by value (Go swaps in a fresh map after spreading).
    fn create_jsx_attributes_type(
        &mut self,
        attributes_symbol: Option<SymbolId>,
        attributes_table: &mut ast::SymbolTable,
        object_flags: &mut ObjectFlags,
    ) -> TypeId {
        *object_flags |= ObjectFlags::FRESH_LITERAL;
        let result = self.new_anonymous_type(
            attributes_symbol,
            std::mem::take(attributes_table),
            &[],
            &[],
            &[],
        );
        self.types_handle().get_mut(result).object_flags |= *object_flags
            | ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        result
    }

    /// `parentHasSemanticJsxChildren` — the Go local closure inside
    /// `createJsxAttributesTypeFromAttributesProperty` (jsx.go:798).
    fn parent_has_semantic_jsx_children(&mut self, opening_like_element: NodeId) -> bool {
        // Handle children attribute
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((opening_like_element).file_index());
        let Some(parent) = nodes[opening_like_element].parent else {
            return false;
        };
        let children: Vec<NodeId>;
        if ast::is_jsx_element(&nodes[parent]) {
            // We have to check that openingElement of the parent is the one
            // we are visiting as this may not be true for selfClosingElement
            if nodes[parent].as_jsx_element().opening_element == Some(opening_like_element) {
                children = nodes[parent]
                    .children()
                    .map(|c| c.nodes.to_vec())
                    .unwrap_or_default();
            } else {
                children = Vec::new();
            }
        } else if ast::is_jsx_fragment(&nodes[parent]) {
            if nodes[parent].as_jsx_fragment().opening_fragment == Some(opening_like_element) {
                children = nodes[parent]
                    .children()
                    .map(|c| c.nodes.to_vec())
                    .unwrap_or_default();
            } else {
                children = Vec::new();
            }
        } else {
            children = Vec::new();
        }
        !ast::get_semantic_jsx_children(&children, &nodes).is_empty()
    }

    /// `func (c *Checker) checkJsxAttribute` (jsx.go:869).
    pub(crate) fn check_jsx_attribute(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(initializer) = nodes[node].initializer() {
            return self.check_expression_for_mutable_location(initializer, check_mode);
        }
        // <Elem attr /> is sugar for <Elem attr={true} />
        self.true_type
    }

    /// `func (c *Checker) checkJsxChildren` (jsx.go:877).
    pub(crate) fn check_jsx_children(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> Vec<TypeId> {
        let mut child_types = Vec::new();
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let children: Vec<NodeId> = nodes[node]
            .children()
            .map(|c| c.nodes.to_vec())
            .unwrap_or_default();
        for child in children {
            // In React, JSX text that contains only whitespaces will be
            // ignored so we don't want to type-check that because then type
            // of children property will have constituent of string type.
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((child).file_index());
            if ast::is_jsx_text(&nodes[child]) {
                if !nodes[child].as_jsx_text().contains_only_trivia_white_spaces {
                    child_types.push(self.string_type);
                }
            } else if ast::is_jsx_expression(&nodes[child]) && nodes[child].expression().is_none() {
                // empty jsx expressions don't *really* count as present
                // children
                continue;
            } else {
                child_types.push(self.check_expression_for_mutable_location(child, check_mode));
            }
        }
        child_types
    }

    /// `func (c *Checker) getUninstantiatedJsxSignaturesOfType` (jsx.go:896).
    pub(crate) fn get_uninstantiated_jsx_signatures_of_type(
        &mut self,
        element_type: TypeId,
        caller: NodeId,
    ) -> Vec<SignatureId> {
        if self
            .types_handle()
            .get(element_type)
            .flags
            .intersects(TypeFlags::STRING)
        {
            return vec![self.any_signature];
        }
        if self
            .types_handle()
            .get(element_type)
            .flags
            .intersects(TypeFlags::STRING_LITERAL)
        {
            let intrinsic_type =
                self.get_intrinsic_attributes_type_from_string_literal_type(element_type, caller);
            let Some(intrinsic_type) = intrinsic_type else {
                self.error(
                    Some(caller),
                    &diagnostics::Property_0_does_not_exist_on_type_1,
                    &[
                        crate::checker_d::get_string_literal_value(&self.types, element_type),
                        format!("JSX.{}", JSX_NAMES.intrinsic_elements),
                    ],
                );
                return Vec::new();
            };
            let fake_signature = self.create_signature_for_jsx_intrinsic(caller, intrinsic_type);
            return vec![fake_signature];
        }
        let apparent_elem_type = self.get_apparent_type(element_type);
        // Resolve the signatures, preferring constructor
        let mut signatures =
            self.get_signatures_of_type(apparent_elem_type, SignatureKind::Construct);
        if signatures.is_empty() {
            // No construct signatures, try call signatures
            signatures = self.get_signatures_of_type(apparent_elem_type, SignatureKind::Call);
        }
        if signatures.is_empty()
            && self
                .types_handle()
                .get(apparent_elem_type)
                .flags
                .intersects(TypeFlags::UNION)
        {
            // If each member has some combination of new/call signatures;
            // make a union signature list for those
            let __arena_types = self.types.clone();
            let types = __arena_types.get(apparent_elem_type).types().to_vec();
            let signature_lists: Vec<Vec<SignatureId>> = types
                .iter()
                .map(|&t| self.get_uninstantiated_jsx_signatures_of_type(t, caller))
                .collect();
            signatures = self.get_union_signatures(&signature_lists);
        }
        signatures
    }

    /// `func (c *Checker) getEffectiveFirstArgumentForJsxSignature`
    /// (jsx.go:925).
    pub(crate) fn get_effective_first_argument_for_jsx_signature(
        &mut self,
        signature: SignatureId,
        node: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_jsx_opening_fragment(&nodes[node])
            || self.get_jsx_reference_kind(node) != JsxReferenceKind::Component
        {
            return self.get_jsx_props_type_from_call_signature(signature, node);
        }
        self.get_jsx_props_type_from_class_type(signature, node)
    }

    /// `func (c *Checker) getJsxPropsTypeFromCallSignature` (jsx.go:932).
    pub(crate) fn get_jsx_props_type_from_call_signature(
        &mut self,
        sig: SignatureId,
        context: NodeId,
    ) -> TypeId {
        let mut props_type =
            self.get_type_of_first_parameter_of_signature_with_fallback(sig, self.unknown_type);
        let ns = self.get_jsx_namespace_at(Some(context));
        props_type =
            self.get_jsx_managed_attributes_from_located_attributes(context, ns, props_type);
        let intrinsic_attribs = self.get_jsx_type(JSX_NAMES.intrinsic_attributes, Some(context));
        if !self.is_error_type(intrinsic_attribs) {
            props_type = self
                .intersect_types(Some(intrinsic_attribs), Some(props_type))
                .unwrap_or(props_type);
        }
        props_type
    }

    /// `func (c *Checker) getJsxPropsTypeFromClassType` (jsx.go:942).
    pub(crate) fn get_jsx_props_type_from_class_type(
        &mut self,
        sig: SignatureId,
        context: NodeId,
    ) -> TypeId {
        let ns = self.get_jsx_namespace_at(Some(context));
        let forced_lookup_location = self.get_jsx_element_properties_name(ns);
        let attributes_type: Option<TypeId>;
        if forced_lookup_location == ast::symbol::INTERNAL_SYMBOL_NAME_MISSING {
            attributes_type = Some(
                self.get_type_of_first_parameter_of_signature_with_fallback(sig, self.unknown_type),
            );
        } else if forced_lookup_location.is_empty() {
            attributes_type = Some(self.get_return_type_of_signature(sig));
        } else {
            attributes_type =
                self.get_jsx_props_type_for_signature_from_member(sig, &forced_lookup_location);
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((context).file_index());
            let has_attributes = nodes[context]
                .attributes()
                .and_then(|a| nodes[a].properties().map(|p| !p.is_empty()))
                .unwrap_or(false);
            if attributes_type.is_none() && has_attributes {
                // There is no property named 'props' on this instance type
                self.error(
                    Some(context),
                    &diagnostics::JSX_element_class_does_not_support_attributes_because_it_does_not_have_a_0_property,
                    &[forced_lookup_location.clone()],
                );
            }
        }
        let Some(mut attributes_type) = attributes_type else {
            return self.unknown_type;
        };
        attributes_type =
            self.get_jsx_managed_attributes_from_located_attributes(context, ns, attributes_type);
        if crate::types::is_type_any(&self.types, attributes_type) {
            // Props is of type 'any' or unknown
            return attributes_type;
        }
        // Normal case -- add in IntrinsicClassAttributes<T> and
        // IntrinsicAttributes
        let mut apparent_attributes_type = attributes_type;
        let intrinsic_class_attribs =
            self.get_jsx_type(JSX_NAMES.intrinsic_class_attributes, Some(context));
        if !self.is_error_type(intrinsic_class_attribs) {
            // `intrinsicClassAttribs.symbol` may be absent; Go's
            // `getLocalTypeParametersOfClassOrInterfaceOrTypeAlias` returns
            // `nil` both for a nil symbol and for no appended parameters.
            let __arena_intrinsic_symbol = self.types.clone();
            let intrinsic_symbol = __arena_intrinsic_symbol.get(intrinsic_class_attribs).symbol;
            let type_params = intrinsic_symbol
                .map(|s| self.get_local_type_parameters_of_class_or_interface_or_type_alias(s))
                .filter(|t| !t.is_empty());
            let host_class_type = self.get_return_type_of_signature(sig);
            let library_managed_attribute_type;
            if let Some(type_params) = type_params {
                // apply JSX.IntrinsicClassAttributes<hostClassType, ...>
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((context).file_index());
                let in_js_file = ast::is_in_js_file(Some(context), &nodes);
                let min_args = self.get_min_type_argument_count(&type_params);
                let inferred_args = self.fill_missing_type_arguments(
                    &[host_class_type],
                    &type_params,
                    min_args,
                    in_js_file,
                );
                let mapper = crate::mapper::new_type_mapper(self, type_params, inferred_args);
                library_managed_attribute_type =
                    self.instantiate_type(intrinsic_class_attribs, Some(mapper));
            } else {
                library_managed_attribute_type = intrinsic_class_attribs;
            }
            apparent_attributes_type = self
                .intersect_types(
                    Some(library_managed_attribute_type),
                    Some(apparent_attributes_type),
                )
                .unwrap_or(apparent_attributes_type);
        }
        let intrinsic_attribs = self.get_jsx_type(JSX_NAMES.intrinsic_attributes, Some(context));
        if !self.is_error_type(intrinsic_attribs) {
            apparent_attributes_type = self
                .intersect_types(Some(intrinsic_attribs), Some(apparent_attributes_type))
                .unwrap_or(apparent_attributes_type);
        }
        apparent_attributes_type
    }

    /// `func (c *Checker) getJsxPropsTypeForSignatureFromMember` (jsx.go:989).
    pub(crate) fn get_jsx_props_type_for_signature_from_member(
        &mut self,
        sig: SignatureId,
        forced_lookup_location: &str,
    ) -> Option<TypeId> {
        if let Some(composite) = self.signature_arena.get(sig).composite.clone() {
            // JSX Elements using the legacy `props`-field based lookup (eg,
            // react class components) need to treat the `props` member as an
            // input instead of an output position when resolving the
            // signature. We need to go back to the input signatures of the
            // composite signature, get the type of `props` on each return
            // type individually, and then _intersect them_, rather than
            // union them (as would normally occur for a union signature).
            // It's an unfortunate quirk of looking in the output of the
            // signature for the type we want to use for the input. The
            // default behavior of
            // `getTypeOfFirstParameterOfSignatureWithFallback` when no
            // `props` member name is defined is much more sane.
            let mut results = Vec::new();
            for signature in composite.signatures {
                let instance = self.get_return_type_of_signature(signature);
                if crate::types::is_type_any(&self.types, instance) {
                    return Some(instance);
                }
                let prop_type = self.get_type_of_property_of_type(instance, forced_lookup_location);
                prop_type?;
                results.push(prop_type.unwrap());
            }
            return Some(self.get_intersection_type(&results));
            // Same result for both union and intersection signatures
        }
        let instance_type = self.get_return_type_of_signature(sig);
        if crate::types::is_type_any(&self.types, instance_type) {
            return Some(instance_type);
        }
        self.get_type_of_property_of_type(instance_type, forced_lookup_location)
    }

    /// `func (c *Checker) getJsxManagedAttributesFromLocatedAttributes`
    /// (jsx.go:1018).
    pub(crate) fn get_jsx_managed_attributes_from_located_attributes(
        &mut self,
        context: NodeId,
        ns: Option<SymbolId>,
        attributes_type: TypeId,
    ) -> TypeId {
        let managed_sym = self.get_jsx_library_managed_attributes(ns);
        if let Some(managed_sym) = managed_sym {
            let ctor_type = self.get_static_type_of_referenced_jsx_constructor(context);
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((context).file_index());
            let in_js_file = ast::is_in_js_file(Some(context), &nodes);
            if let Some(result) = self.instantiate_alias_or_interface_with_defaults(
                managed_sym,
                &[ctor_type, attributes_type],
                in_js_file,
            ) {
                return result;
            }
        }
        attributes_type
    }

    /// `func (c *Checker) instantiateAliasOrInterfaceWithDefaults`
    /// (jsx.go:1030).
    pub(crate) fn instantiate_alias_or_interface_with_defaults(
        &mut self,
        managed_sym: SymbolId,
        type_arguments: &[TypeId],
        in_javascript: bool,
    ) -> Option<TypeId> {
        let declared_managed_type = self.get_declared_type_of_symbol(managed_sym);
        // fetches interface type, or initializes symbol links type parameters
        if self
            .sym(managed_sym)
            .flags
            .intersects(ast::SymbolFlags::TYPE_ALIAS)
        {
            let params = self
                .type_alias_links
                .get(managed_sym)
                .type_parameters
                .clone();
            if params.len() >= type_arguments.len() {
                let args = self.fill_missing_type_arguments(
                    type_arguments,
                    &params,
                    type_arguments.len(),
                    in_javascript,
                );
                if args.is_empty() {
                    return Some(declared_managed_type);
                }
                return Some(self.get_type_alias_instantiation(managed_sym, &args, None));
            }
        }
        if self
            .types_handle()
            .get(declared_managed_type)
            .object_flags
            .intersects(ObjectFlags::CLASS_OR_INTERFACE)
        {
            let __arena_type_parameters = self.types.clone();
            let type_parameters = __arena_type_parameters
                .get(declared_managed_type)
                .as_interface_type()
                .map(|i| i.type_parameters().to_vec())
                .unwrap_or_default();
            if type_parameters.len() >= type_arguments.len() {
                let args = self.fill_missing_type_arguments(
                    type_arguments,
                    &type_parameters,
                    type_arguments.len(),
                    in_javascript,
                );
                return Some(self.create_type_reference(declared_managed_type, &args));
            }
        }
        None
    }

    /// `func (c *Checker) getJsxLibraryManagedAttributes` (jsx.go:1050).
    pub(crate) fn get_jsx_library_managed_attributes(
        &mut self,
        jsx_namespace: Option<SymbolId>,
    ) -> Option<SymbolId> {
        if let Some(jsx_namespace) = jsx_namespace {
            let exports = self.sym(jsx_namespace).exports.clone();
            return self.get_symbol(
                &exports,
                JSX_NAMES.library_managed_attributes,
                ast::SymbolFlags::TYPE,
            );
        }
        None
    }

    /// `func (c *Checker) getJsxElementTypeSymbol` (jsx.go:1057).
    pub(crate) fn get_jsx_element_type_symbol(
        &mut self,
        jsx_namespace: Option<SymbolId>,
    ) -> Option<SymbolId> {
        // JSX.ElementType [symbol]
        if let Some(jsx_namespace) = jsx_namespace {
            let exports = self.sym(jsx_namespace).exports.clone();
            return self.get_symbol(&exports, JSX_NAMES.element_type, ast::SymbolFlags::TYPE);
        }
        None
    }

    /// `func (c *Checker) getJsxElementPropertiesName` (jsx.go:1073) — e.g.
    /// "props" for React.d.ts, or `InternalSymbolNameMissing` if
    /// `ElementAttributesProperty` doesn't exist (which means all
    /// non-intrinsic elements' attributes type is 'any'), or "" if it has 0
    /// properties (which means every non-intrinsic elements' attributes type
    /// is the element instance type).
    pub(crate) fn get_jsx_element_properties_name(
        &mut self,
        jsx_namespace: Option<SymbolId>,
    ) -> String {
        self.get_name_from_jsx_element_attributes_container(
            JSX_NAMES.element_attributes_property_name_container,
            jsx_namespace,
        )
    }

    /// `func (c *Checker) getJsxElementChildrenPropertyName` (jsx.go:1077).
    pub(crate) fn get_jsx_element_children_property_name(
        &mut self,
        jsx_namespace: Option<SymbolId>,
    ) -> String {
        if self.compiler_options.jsx == JsxEmit::ReactJSX
            || self.compiler_options.jsx == JsxEmit::ReactJSXDev
        {
            // In these JsxEmit modes the children property is fixed to
            // 'children'
            return "children".to_string();
        }
        self.get_name_from_jsx_element_attributes_container(
            JSX_NAMES.element_children_attribute_name_container,
            jsx_namespace,
        )
    }

    /// `func (c *Checker) getNameFromJsxElementAttributesContainer`
    /// (jsx.go:1091).
    ///
    /// Look into JSX namespace and then look for container with matching
    /// name as `nameOfAttribPropContainer`. Get a single property from that
    /// container if existed. Report an error if there are more than one
    /// property.
    ///
    /// `nameOfAttribPropContainer` is a string of value
    /// `JsxNames.ElementAttributesPropertyNameContainer` or
    /// `JsxNames.ElementChildrenAttributeNameContainer`; if another string is
    /// given or the container doesn't exist, return
    /// `InternalSymbolNameMissing`.
    pub(crate) fn get_name_from_jsx_element_attributes_container(
        &mut self,
        name_of_attrib_prop_container: &str,
        jsx_namespace: Option<SymbolId>,
    ) -> String {
        // JSX.ElementAttributesProperty | JSX.ElementChildrenAttribute
        // [symbol]
        if let Some(jsx_namespace) = jsx_namespace {
            let exports = self.sym(jsx_namespace).exports.clone();
            let jsx_element_attrib_prop_interface_sym = self.get_symbol(
                &exports,
                name_of_attrib_prop_container,
                ast::SymbolFlags::TYPE,
            );
            if let Some(sym) = jsx_element_attrib_prop_interface_sym {
                let jsx_element_attrib_prop_interface_type = self.get_declared_type_of_symbol(sym);
                let properties =
                    self.get_properties_of_type(jsx_element_attrib_prop_interface_type);
                // Element Attributes has zero properties, so the element
                // attributes type will be the class instance type
                if properties.is_empty() {
                    return String::new();
                }
                if properties.len() == 1 {
                    return self.sym(properties[0]).name.clone();
                }
                let declarations = self.sym(sym).declarations.clone();
                if properties.len() > 1 && !declarations.is_empty() {
                    // More than one property on ElementAttributesProperty is
                    // an error
                    self.error(
                        Some(declarations[0]),
                        &diagnostics::The_global_type_JSX_0_may_not_have_more_than_one_property,
                        &[name_of_attrib_prop_container.to_string()],
                    );
                }
            }
        }
        ast::symbol::INTERNAL_SYMBOL_NAME_MISSING.to_string()
    }

    /// `func (c *Checker) getStaticTypeOfReferencedJsxConstructor`
    /// (jsx.go:1114).
    pub(crate) fn get_static_type_of_referenced_jsx_constructor(
        &mut self,
        context: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((context).file_index());
        if ast::is_jsx_opening_fragment(&nodes[context]) {
            return self.get_jsx_fragment_type(context);
        }
        let tag_name = nodes[context].tag_name().expect("jsx tag name");
        if crate::utilities::is_jsx_intrinsic_tag_name(tag_name, &nodes) {
            let result = self.get_intrinsic_attributes_type_from_jsx_opening_like_element(context);
            let fake_signature = self.create_signature_for_jsx_intrinsic(context, result);
            return self.get_or_create_type_from_signature(fake_signature);
        }
        let tag_type = self.check_expression_cached(tag_name);
        if self
            .types_handle()
            .get(tag_type)
            .flags
            .intersects(TypeFlags::STRING_LITERAL)
        {
            let Some(result) =
                self.get_intrinsic_attributes_type_from_string_literal_type(tag_type, context)
            else {
                return self.error_type;
            };
            let fake_signature = self.create_signature_for_jsx_intrinsic(context, result);
            return self.get_or_create_type_from_signature(fake_signature);
        }
        tag_type
    }

    /// `func (c *Checker) getIntrinsicAttributesTypeFromStringLiteralType`
    /// (jsx.go:1135).
    ///
    /// If the elemType is a stringLiteral type, we can then provide a check
    /// to make sure that the string literal type is one of the Jsx intrinsic
    /// element type. For example:
    /// ```ignore
    /// var CustomTag: "h1" = "h1";
    /// <CustomTag> Hello World </CustomTag>
    /// ```
    pub(crate) fn get_intrinsic_attributes_type_from_string_literal_type(
        &mut self,
        t: TypeId,
        location: NodeId,
    ) -> Option<TypeId> {
        let intrinsic_elements_type =
            self.get_jsx_type(JSX_NAMES.intrinsic_elements, Some(location));
        if !self.is_error_type(intrinsic_elements_type) {
            let string_literal_type_name =
                crate::checker_d::get_string_literal_value(&self.types, t);
            let intrinsic_prop =
                self.get_property_of_type(intrinsic_elements_type, &string_literal_type_name);
            if let Some(intrinsic_prop) = intrinsic_prop {
                return Some(self.get_type_of_symbol(intrinsic_prop));
            }
            let index_signature_type =
                self.get_index_type_of_type(intrinsic_elements_type, self.string_type);
            if index_signature_type.is_some() {
                return index_signature_type;
            }
            return None;
        }
        // If we need to report an error, we already done so here. So just
        // return any to prevent any more error downstream
        Some(self.any_type)
    }

    /// `func (c *Checker) getJsxReferenceKind` (jsx.go:1157).
    pub(crate) fn get_jsx_reference_kind(&mut self, node: NodeId) -> JsxReferenceKind {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let tag_name = nodes[node].tag_name().expect("jsx tag name");
        if crate::utilities::is_jsx_intrinsic_tag_name(tag_name, &nodes) {
            return JsxReferenceKind::Mixed;
        }
        let tag_type = self.check_expression(tag_name);
        let tag_type = self.get_apparent_type(tag_type);
        if !self
            .get_signatures_of_type(tag_type, SignatureKind::Construct)
            .is_empty()
        {
            return JsxReferenceKind::Component;
        }
        if !self
            .get_signatures_of_type(tag_type, SignatureKind::Call)
            .is_empty()
        {
            return JsxReferenceKind::Function;
        }
        JsxReferenceKind::Mixed
    }

    /// `func (c *Checker) createSignatureForJSXIntrinsic` (jsx.go:1171).
    pub(crate) fn create_signature_for_jsx_intrinsic(
        &mut self,
        node: NodeId,
        result: TypeId,
    ) -> SignatureId {
        let mut element_type = self.error_type;
        if let Some(namespace) = self.get_jsx_namespace_at(Some(node)) {
            let exports = self.get_exports_of_symbol(namespace);
            if let Some(type_symbol) =
                self.get_symbol(&exports, JSX_NAMES.element, ast::SymbolFlags::TYPE)
            {
                element_type = self.get_declared_type_of_symbol(type_symbol);
            }
        }
        // returnNode := typeSymbol && c.nodeBuilder.symbolToEntityName(...)
        // declaration := factory.createFunctionTypeNode(...) — see Go comment.
        let parameter_symbol = self.new_symbol(ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE, "props");
        self.value_symbol_links.get(parameter_symbol).resolved_type = Some(result);
        self.new_signature(
            crate::types::SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            vec![parameter_symbol],
            Some(element_type),
            None,
            1,
        )
    }

    /// `func (c *Checker) getIntrinsicAttributesTypeFromJsxOpeningLikeElement`
    /// (jsx.go:1188).
    ///
    /// Get attributes type of the given intrinsic opening-like Jsx element
    /// by resolving the tag name. The function is intended to be called from
    /// a function which has checked that the opening element is an intrinsic
    /// element.
    /// `node` an intrinsic JSX opening-like element.
    pub(crate) fn get_intrinsic_attributes_type_from_jsx_opening_like_element(
        &mut self,
        node: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let tag_name = nodes[node].tag_name().expect("jsx tag name");
        debug_assert!(crate::utilities::is_jsx_intrinsic_tag_name(
            tag_name, &nodes
        ));
        if let Some(t) = self
            .jsx_element_links
            .get(node)
            .resolved_jsx_element_attributes_type
        {
            return t;
        }
        let symbol = self.get_intrinsic_tag_symbol(node);
        if self
            .jsx_element_links
            .get(node)
            .jsx_flags
            .intersects(JsxFlags::INTRINSIC_NAMED_ELEMENT)
        {
            let t = if symbol == SymbolId::NONE {
                self.error_type
            } else {
                self.get_type_of_symbol(symbol)
            };
            self.jsx_element_links
                .get(node)
                .resolved_jsx_element_attributes_type = Some(t);
            return t;
        }
        if self
            .jsx_element_links
            .get(node)
            .jsx_flags
            .intersects(JsxFlags::INTRINSIC_INDEXED_ELEMENT)
        {
            let intrinsic_elements = self.get_jsx_type(JSX_NAMES.intrinsic_elements, Some(node));
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let tag_name = nodes[node].tag_name().expect("jsx tag name");
            let name = nodes[tag_name].text(&nodes).into_owned();
            let index_info = self.get_applicable_index_info_for_name(intrinsic_elements, &name);
            if let Some(index_info) = index_info {
                let t = self.index_info_arena.get(index_info).value_type;
                let t = t.unwrap_or(self.error_type);
                self.jsx_element_links
                    .get(node)
                    .resolved_jsx_element_attributes_type = Some(t);
                return t;
            }
        }
        let t = self.error_type;
        self.jsx_element_links
            .get(node)
            .resolved_jsx_element_attributes_type = Some(t);
        t
    }

    /// `func (c *Checker) getIntrinsicTagSymbol` (jsx.go:1214).
    ///
    /// Looks up an intrinsic tag name and returns a symbol that either
    /// points to an intrinsic property (in which case nodeLinks.jsxFlags
    /// will be IntrinsicNamedElement) or an intrinsic string index signature
    /// (in which case nodeLinks.jsxFlags will be IntrinsicIndexedElement).
    /// May also return unknownSymbol if both of these lookups fail.
    pub(crate) fn get_intrinsic_tag_symbol(&mut self, node: NodeId) -> SymbolId {
        if let Some(s) = self.symbol_node_links.get(node).resolved_symbol {
            return s;
        }
        let intrinsic_elements_type = self.get_jsx_type(JSX_NAMES.intrinsic_elements, Some(node));
        if !self.is_error_type(intrinsic_elements_type) {
            // Property case
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let tag_name = nodes[node].tag_name().expect("jsx tag name");
            if !ast::is_identifier(&nodes[tag_name])
                && !ast::is_jsx_namespaced_name(&nodes[tag_name])
            {
                panic!("Invalid tag name");
            }
            let prop_name = nodes[tag_name].text(&nodes).into_owned();
            let intrinsic_prop = self.get_property_of_type(intrinsic_elements_type, &prop_name);
            if let Some(intrinsic_prop) = intrinsic_prop {
                self.jsx_element_links.get(node).jsx_flags |= JsxFlags::INTRINSIC_NAMED_ELEMENT;
                self.symbol_node_links.get(node).resolved_symbol = Some(intrinsic_prop);
                return intrinsic_prop;
            }
            // Intrinsic string indexer case
            let key_type = self.get_string_literal_type(&prop_name);
            let index_symbol = self.get_applicable_index_symbol(intrinsic_elements_type, key_type);
            if let Some(index_symbol) = index_symbol {
                self.jsx_element_links.get(node).jsx_flags |= JsxFlags::INTRINSIC_INDEXED_ELEMENT;
                self.symbol_node_links.get(node).resolved_symbol = Some(index_symbol);
                return index_symbol;
            }
            if self
                .get_type_of_property_or_index_signature_of_type(
                    intrinsic_elements_type,
                    &prop_name,
                )
                .is_some()
            {
                self.jsx_element_links.get(node).jsx_flags |= JsxFlags::INTRINSIC_INDEXED_ELEMENT;
                let __arena_symbol = self.types.clone();
                let symbol = __arena_symbol.get(intrinsic_elements_type).symbol;
                self.symbol_node_links.get(node).resolved_symbol = symbol;
                return symbol.unwrap_or(self.unknown_symbol);
            }
            // Wasn't found
            self.error(
                Some(node),
                &diagnostics::Property_0_does_not_exist_on_type_1,
                &[prop_name, format!("JSX.{}", JSX_NAMES.intrinsic_elements)],
            );
            let unknown = self.unknown_symbol;
            self.symbol_node_links.get(node).resolved_symbol = Some(unknown);
            return unknown;
        }
        if self.no_implicit_any {
            self.error(
                Some(node),
                &diagnostics::JSX_element_implicitly_has_type_any_because_no_interface_JSX_0_exists,
                &[JSX_NAMES.intrinsic_elements.to_string()],
            );
        }
        let unknown = self.unknown_symbol;
        self.symbol_node_links.get(node).resolved_symbol = Some(unknown);
        unknown
    }

    /// `func (c *Checker) getJsxStatelessElementTypeAt` (jsx.go:1257).
    pub(crate) fn get_jsx_stateless_element_type_at(&mut self, location: NodeId) -> Option<TypeId> {
        let jsx_element_type = self.get_jsx_element_type_at(location);
        if jsx_element_type == TypeId::NONE {
            return None;
        }
        Some(self.get_union_type(&[jsx_element_type, self.null_type]))
    }

    /// `func (c *Checker) getJsxElementClassTypeAt` (jsx.go:1265).
    pub(crate) fn get_jsx_element_class_type_at(&mut self, location: NodeId) -> Option<TypeId> {
        let t = self.get_jsx_type(JSX_NAMES.element_class, Some(location));
        if self.is_error_type(t) {
            return None;
        }
        Some(t)
    }

    /// `func (c *Checker) getJsxElementTypeAt` (jsx.go:1273).
    pub(crate) fn get_jsx_element_type_at(&mut self, location: NodeId) -> TypeId {
        self.get_jsx_type(JSX_NAMES.element, Some(location))
    }

    /// `func (c *Checker) getJsxElementTypeTypeAt` (jsx.go:1277).
    pub(crate) fn get_jsx_element_type_type_at(&mut self, location: NodeId) -> Option<TypeId> {
        let ns = self.get_jsx_namespace_at(Some(location))?;
        let sym = self.get_jsx_element_type_symbol(Some(ns))?;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        let in_js_file = ast::is_in_js_file(Some(location), &nodes);
        let t = self.instantiate_alias_or_interface_with_defaults(sym, &[], in_js_file)?;
        if self.is_error_type(t) {
            return None;
        }
        Some(t)
    }

    /// `func (c *Checker) getJsxType` (jsx.go:1293).
    pub(crate) fn get_jsx_type(
        &mut self,
        name: &str,
        location: impl Into<Option<NodeId>>,
    ) -> TypeId {
        if let Some(namespace) = self.get_jsx_namespace_at(location.into()) {
            let exports = self.get_exports_of_symbol(namespace);
            if let Some(type_symbol) = self.get_symbol(&exports, name, ast::SymbolFlags::TYPE) {
                return self.get_declared_type_of_symbol(type_symbol);
            }
        }
        self.error_type
    }

    /// `func (c *Checker) getJsxNamespaceAt` (jsx.go:1304).
    pub(crate) fn get_jsx_namespace_at(
        &mut self,
        location: impl Into<Option<NodeId>>,
    ) -> Option<SymbolId> {
        let location = location.into();
        if let Some(location) = location {
            let jsx_namespace = self.jsx_element_links.get(location).jsx_namespace;
            if let Some(jsx_namespace) = jsx_namespace {
                if jsx_namespace != self.unknown_symbol {
                    return Some(jsx_namespace);
                }
            }
        }
        let has_unknown = location
            .map(|l| self.jsx_element_links.get(l).jsx_namespace == Some(self.unknown_symbol))
            .unwrap_or(false);
        // `links == nil || links.jsxNamespace != c.unknownSymbol`
        if location.is_none() || !has_unknown {
            let mut resolved_namespace =
                self.get_jsx_namespace_container_for_implicit_import(location);
            if resolved_namespace.is_none() || resolved_namespace == Some(self.unknown_symbol) {
                let namespace_name = self.get_jsx_namespace(location);
                resolved_namespace = self.resolve_name_thunk(
                    location,
                    &namespace_name,
                    ast::SymbolFlags::NAMESPACE,
                    None,  /*nameNotFoundMessage*/
                    false, /*isUse*/
                    false, /*excludeGlobals*/
                );
            }
            if let Some(resolved_namespace) = resolved_namespace {
                let resolved = self.resolve_symbol(resolved_namespace);
                let exports = self.get_exports_of_symbol(resolved);
                let candidate = self
                    .get_symbol(&exports, JSX_NAMES.jsx, ast::SymbolFlags::NAMESPACE)
                    .map(|s| self.resolve_symbol(s));
                if let Some(candidate) = candidate {
                    if candidate != self.unknown_symbol {
                        if let Some(location) = location {
                            self.jsx_element_links.get(location).jsx_namespace = Some(candidate);
                        }
                        return Some(candidate);
                    }
                }
            }
            if let Some(location) = location {
                self.jsx_element_links.get(location).jsx_namespace = Some(self.unknown_symbol);
            }
        }
        // JSX global fallback
        let s = self
            .get_global_symbol(JSX_NAMES.jsx, ast::SymbolFlags::NAMESPACE, None)
            .map(|s| self.resolve_symbol(s));
        if s == Some(self.unknown_symbol) {
            return None;
        }
        s
    }

    /// `func (c *Checker) getJsxNamespace` (jsx.go:1339).
    pub fn get_jsx_namespace(&mut self, location: impl Into<Option<NodeId>>) -> String {
        let location = location.into();
        if let Some(location) = location {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((location).file_index());
            if let Some(file) = ast::get_source_file_of_node(Some(location), &nodes) {
                let is_opening_fragment = ast::is_jsx_opening_fragment(&nodes[location]);
                if is_opening_fragment {
                    let local = self
                        .source_file_links
                        .get(file)
                        .local_jsx_fragment_namespace
                        .clone();
                    if !local.is_empty() {
                        return local;
                    }
                    let jsx_frag_pragma_value = {
                        let sf = nodes[file].as_source_file();
                        ast::get_pragma_from_source_file(sf, "jsxfrag")
                            .map(|p| ast::get_pragma_argument(Some(p), "factory"))
                    };
                    if let Some(value) = jsx_frag_pragma_value {
                        let factory = self.parse_isolated_entity_name(&value, file.file_index());
                        self.source_file_links.get(file).local_jsx_fragment_factory = factory;
                        if let Some(factory) = factory {
                            let first = ast::get_first_identifier(factory, &nodes);
                            let text = nodes[first].text(&nodes).into_owned();
                            self.source_file_links
                                .get(file)
                                .local_jsx_fragment_namespace = text.clone();
                            return text;
                        }
                    }
                    if let Some(entity) = self.get_jsx_fragment_factory_entity(Some(location)) {
                        self.source_file_links.get(file).local_jsx_fragment_factory = Some(entity);
                        let first = ast::get_first_identifier(entity, &nodes);
                        let text = nodes[first].text(&nodes).into_owned();
                        self.source_file_links
                            .get(file)
                            .local_jsx_fragment_namespace = text.clone();
                        return text;
                    }
                } else {
                    let local_jsx_namespace = self.get_local_jsx_namespace(file);
                    if !local_jsx_namespace.is_empty() {
                        self.source_file_links.get(file).local_jsx_namespace =
                            local_jsx_namespace.clone();
                        return local_jsx_namespace;
                    }
                }
            }
        }
        let file_index = location.map(|l| l.file_index()).unwrap_or(0);
        if self.jsx_namespace.is_empty() {
            self.jsx_namespace = "React".to_string();
            if !self.compiler_options.jsx_factory.is_empty() {
                let jsx_factory = self.compiler_options.jsx_factory.clone();
                self.jsx_factory_entity = self.parse_isolated_entity_name(&jsx_factory, file_index);
                if let Some(entity) = self.jsx_factory_entity {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((entity).file_index());
                    let first = ast::get_first_identifier(entity, &nodes);
                    self.jsx_namespace = nodes[first].text(&nodes).into_owned();
                }
            } else if !self.compiler_options.react_namespace.is_empty() {
                self.jsx_namespace = self.compiler_options.react_namespace.clone();
            }
        }
        if self.jsx_factory_entity.is_none() {
            let program = self.program.clone().expect("program");
            let mut arena = program.nodes_mut(file_index);
            let old_file_index = self.factory.file_index();
            self.factory.set_file_index(file_index);
            let left = self
                .factory
                .new_identifier(&mut arena, &self.jsx_namespace.clone());
            let right = self.factory.new_identifier(&mut arena, "createElement");
            let qualified = self
                .factory
                .new_qualified_name(&mut arena, Some(left), Some(right));
            self.factory.set_file_index(old_file_index);
            drop(arena);
            self.jsx_factory_entity = Some(qualified);
        }
        self.jsx_namespace.clone()
    }

    /// `func (c *Checker) getLocalJsxNamespace` (jsx.go:1388).
    pub(crate) fn get_local_jsx_namespace(&mut self, file: NodeId) -> String {
        let local = self.source_file_links.get(file).local_jsx_namespace.clone();
        if !local.is_empty() {
            return local;
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((file).file_index());
        let jsx_pragma_value = {
            let sf = nodes[file].as_source_file();
            ast::get_pragma_from_source_file(sf, "jsx")
                .map(|p| ast::get_pragma_argument(Some(p), "factory"))
        };
        if let Some(value) = jsx_pragma_value {
            let factory = self.parse_isolated_entity_name(&value, file.file_index());
            self.source_file_links.get(file).local_jsx_factory = factory;
            if let Some(factory) = factory {
                let first = ast::get_first_identifier(factory, &nodes);
                let text = nodes[first].text(&nodes).into_owned();
                self.source_file_links.get(file).local_jsx_namespace = text.clone();
                return text;
            }
        }
        String::new()
    }

    /// `func (c *Checker) getJsxFactoryEntity` (jsx.go:1404).
    pub fn get_jsx_factory_entity(
        &mut self,
        location: impl Into<Option<NodeId>>,
    ) -> Option<NodeId> {
        let location = location.into();
        if let Some(location) = location {
            self.get_jsx_namespace(Some(location));
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((location).file_index());
            let file = ast::get_source_file_of_node(Some(location), &nodes);
            if let Some(file) = file {
                if let Some(local_jsx_factory) = self.source_file_links.get(file).local_jsx_factory
                {
                    return Some(local_jsx_factory);
                }
            }
        }
        self.jsx_factory_entity
    }

    /// `func (c *Checker) getJsxFragmentFactoryEntity` (jsx.go:1414).
    pub fn get_jsx_fragment_factory_entity(
        &mut self,
        location: impl Into<Option<NodeId>>,
    ) -> Option<NodeId> {
        let location = location.into();
        if let Some(location) = location {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((location).file_index());
            if let Some(file) = ast::get_source_file_of_node(Some(location), &nodes) {
                if let Some(local) = self.source_file_links.get(file).local_jsx_fragment_factory {
                    return Some(local);
                }
                let jsx_frag_pragma_value = {
                    let sf = nodes[file].as_source_file();
                    ast::get_pragma_from_source_file(sf, "jsxfrag")
                        .map(|p| ast::get_pragma_argument(Some(p), "factory"))
                };
                if let Some(value) = jsx_frag_pragma_value {
                    let parsed = self.parse_isolated_entity_name(&value, file.file_index());
                    self.source_file_links.get(file).local_jsx_fragment_factory = parsed;
                    return parsed;
                }
            }
        }
        if !self.compiler_options.jsx_fragment_factory.is_empty() {
            let file_index = location.map(|l| l.file_index()).unwrap_or(0);
            let name = self.compiler_options.jsx_fragment_factory.clone();
            return self.parse_isolated_entity_name(&name, file_index);
        }
        None
    }

    /// `func (c *Checker) parseIsolatedEntityName` (jsx.go:1435). PORT: the
    /// parse happens in a scratch arena (`tsc_parser`); the resulting entity
    /// name is then re-materialized into the `file_index` file's arena so
    /// its `NodeId`s resolve through `program.nodes` — a faithful stand-in
    /// for Go's pointer-free synthesized nodes.
    pub(crate) fn parse_isolated_entity_name(
        &mut self,
        name: &str,
        file_index: u32,
    ) -> Option<NodeId> {
        let (entity, src) = tsc_parser::parser::parse_isolated_entity_name(name);
        let entity = entity?;
        let result = self.materialize_entity_name(entity, &src, file_index);
        let program = self.program.clone().expect("program");
        let mut arena = program.nodes_mut(file_index);
        mark_as_synthetic(result, &mut arena);
        Some(result)
    }

    /// `materializeEntityName` — port helper: re-create a parsed
    /// `EntityName` (identifier | qualified-name chain) inside the
    /// destination file arena.
    fn materialize_entity_name(
        &mut self,
        node: NodeId,
        src: &[ast::Node],
        file_index: u32,
    ) -> NodeId {
        let program = self.program.clone().expect("program");
        match src[node].kind {
            ast::Kind::QualifiedName => {
                let q = src[node].as_qualified_name();
                let left = self.materialize_entity_name(
                    q.left.expect("qualified name left"),
                    src,
                    file_index,
                );
                let right = self.materialize_entity_name(
                    q.right.expect("qualified name right"),
                    src,
                    file_index,
                );
                let mut arena = program.nodes_mut(file_index);
                let old_file_index = self.factory.file_index();
                self.factory.set_file_index(file_index);
                let result = self
                    .factory
                    .new_qualified_name(&mut arena, Some(left), Some(right));
                self.factory.set_file_index(old_file_index);
                result
            }
            _ => {
                let text = src[node].text(src).into_owned();
                let mut arena = program.nodes_mut(file_index);
                let old_file_index = self.factory.file_index();
                self.factory.set_file_index(file_index);
                let result = self.factory.new_identifier(&mut arena, &text);
                self.factory.set_file_index(old_file_index);
                result
            }
        }
    }

    /// `func (c *Checker) getJsxNamespaceContainerForImplicitImport`
    /// (jsx.go:1449).
    pub(crate) fn get_jsx_namespace_container_for_implicit_import(
        &mut self,
        location: impl Into<Option<NodeId>>,
    ) -> Option<SymbolId> {
        let location = location.into();
        // PORT(borrowck): hoist the program handle so `nodes` borrows it rather
        // than pinning `*self` across `&mut` checker calls below.
        let __program = self.program.clone().expect("program");
        let nodes = location.map(|l| __program.nodes(l.file_index()));
        let file = location.and_then(|l| {
            ast::get_source_file_of_node(Some(l), nodes.as_deref().expect("nodes"))
        })?;
        {
            let jsx_implicit_import_container = self
                .jsx_element_links
                .get(file)
                .jsx_implicit_import_container;
            if let Some(container) = jsx_implicit_import_container {
                return if container == self.unknown_symbol {
                    None
                } else {
                    Some(container)
                };
            }
        }
        let mut canonical_error_tag = self.jsx_element_links.get(file).first_jsx_tag_in_file;
        if canonical_error_tag.is_none() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((file).file_index());
            let mut found = None;
            visit_for_first_jsx_tag(file, &nodes, &mut found);
            canonical_error_tag = found;
            self.jsx_element_links.get(file).first_jsx_tag_in_file = canonical_error_tag;
        }
        let path_key = {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((file).file_index());
            nodes[file].as_source_file().path_key().clone()
        };
        let (module_reference, specifier) = self
            .program
            .as_ref()
            .expect("program")
            .get_jsx_runtime_import_specifier(&path_key);
        if module_reference.is_empty() {
            return None;
        }
        let location_node = specifier.or(canonical_error_tag);
        let module_symbol = self.resolve_external_module(
            location_node.expect("jsx error location"),
            &module_reference,
            Some(
                &diagnostics::This_JSX_tag_requires_the_module_path_0_to_exist_but_none_could_be_found_Make_sure_you_have_types_for_the_appropriate_package_installed,
            ),
            canonical_error_tag,
            false,
            None, /*importAttributesType*/
        );
        let mut result = None;
        if let Some(module_symbol) = module_symbol {
            if module_symbol != self.unknown_symbol {
                let resolved = self.resolve_symbol(module_symbol);
                result = Some(self.get_merged_symbol(resolved));
            }
        }
        self.jsx_element_links
            .get(file)
            .jsx_implicit_import_container = Some(result.unwrap_or(self.unknown_symbol));
        result
    }

    /// `func (c *Checker) getJSXRuntimeImportSpecifier` (jsx.go:1486).
    pub(crate) fn get_jsx_runtime_import_specifier(
        &mut self,
        file: NodeId,
    ) -> (String, Option<NodeId>) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((file).file_index());
        let path_key = nodes[file].as_source_file().path_key().clone();
        self.program
            .as_ref()
            .expect("program")
            .get_jsx_runtime_import_specifier(&path_key)
    }

    /// `c.resolveName(...)` — invoke the binder name-resolver thunk (same
    /// pattern as `getGlobalSymbol`/`markJsxAliasReferenced` call sites).
    fn resolve_name_thunk(
        &mut self,
        location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: Option<&'static diagnostics::Message>,
        is_use: bool,
        exclude_globals: bool,
    ) -> Option<SymbolId> {
        let resolve = self.resolve_name.clone().expect("Checker::resolve_name");
        resolve(
            self,
            location,
            name,
            meaning,
            name_not_found_message,
            is_use,
            exclude_globals,
        )
    }
}

/// `func markAsSynthetic` (jsx.go:1443) — visitor over a file arena; `true`
/// stops traversal per `for_each_child` convention (Go returns false).
fn mark_as_synthetic(node: NodeId, nodes: &mut Vec<ast::Node>) -> bool {
    nodes[node].loc = TextRange::new(-1, -1);
    let mut children = Vec::new();
    nodes[node].for_each_child(nodes, &mut |child| {
        children.push(child);
        false
    });
    for child in children {
        mark_as_synthetic(child, nodes);
    }
    false
}

/// `visit` — the local visitor inside `getJsxNamespaceContainerForImplicitImport`
/// (jsx.go:1458): finds the first JSX tag in the file (opening fragment for
/// fragments, to match strada). Returns `true` to stop traversal, matching
/// `ForEachChild` semantics.
fn visit_for_first_jsx_tag(node: NodeId, nodes: &[ast::Node], found: &mut Option<NodeId>) -> bool {
    if ast::is_jsx_element(&nodes[node]) || ast::is_jsx_self_closing_element(&nodes[node]) {
        *found = Some(node);
        return true;
    }
    if ast::is_jsx_fragment(&nodes[node]) {
        // to match strada, fragments issue errors on the opening fragment
        // instead of the whole tag
        *found = nodes[node].as_jsx_fragment().opening_fragment;
        return true;
    }
    nodes[node].for_each_child(nodes, &mut |child| {
        visit_for_first_jsx_tag(child, nodes, found)
    })
}

/// `tag_name_or_none` — `node.TagName()` for opening-like elements.
fn tag_name_or_none(c: &mut Checker, node: NodeId) -> Option<NodeId> {
    let __program = c.program.clone().expect("program");
    let nodes = __program.nodes((node).file_index());
    nodes[node].tag_name()
}
