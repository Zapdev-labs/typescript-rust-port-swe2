// Ported from tsc/internal/checker/pseudotypenodebuilder.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — mapping `pseudochecker` pseudo
// types into AST nodes (`pseudoTypeToNode` family) plus the pseudo-type /
// checker-type equivalence checkers (`pseudoTypeEquivalentToType`,
// `pseudoParametersEquivalentToParameters`,
// `pseudoReturnTypeMatchesPredicate`, `pseudoTypeToType`).
//
// PORT notes:
//
// - `*pseudochecker.PseudoType` → `PseudoTypeRef` (`Rc<PseudoType>`) or
//   `&PseudoType`; the payload accessors `t.AsPseudoTypeX()` become
//   `t.as_pseudo_type_x()` on the enum (they panic on a mismatched kind, as
//   do Go's type assertions).
// - `*ast.Node` → `Option<NodeId>` where nil-able; the returned `*ast.Node`
//   of `pseudoTypeToNode` becomes `Option<NodeId>` (Go's `AssertNever`
//   default arm is a panic here too, so `None` is only ever produced by
//   `pseudoTypeToType`-style propagation, mirroring Go's nil returns).
// - `b.ctx.tracker` is `Option<Rc<RefCell<dyn SymbolTracker>>>` —
//   `ReportInferenceFallback` calls become conditional `borrow_mut()` calls.
// - Go's `defer cleanup()` for `enterNewScope` becomes an explicit
//   `ScopeCleanup::restore` call at the end of the enclosing match arm.
// - `debug.Assert(t != nil)` is unrepresentable (`PseudoTypeRef` cannot be
//   nil); `debug.AssertNever`/`debug.Fail` map to `tsc_debug`.

use tsc_ast::{self as ast, Kind, NodeId, NodeList, SymbolFlags, SymbolId};
use tsc_nodebuilder as nodebuilder;
use tsc_printer as printer;
use tsc_pseudochecker::{
    self as pseudochecker, PseudoParameter, PseudoType, PseudoTypeKind, PseudoTypeRef,
};

use crate::checker_core::Checker;
use crate::checker_types::TypeFacts;
use crate::nodebuilderimpl::NodeBuilderImpl;
use crate::nodebuilderscopes::ScopeCleanup;
use crate::types::{
    ContextFlags, ElementFlags, SignatureId, Ternary, TypeFlags, TypeId, TypePredicate,
    TypePredicateKind,
};

// ----------------------------------------------------------------------------
// Local arena helpers — short-borrow copies of symbol fields so `&mut
// Checker` calls never alias a live borrow (same pattern as
// nodebuilderimpl.rs's private helpers).
// ----------------------------------------------------------------------------

/// `symbol.flags` read through the arena.
fn symbol_flags(c: &Checker, s: SymbolId) -> SymbolFlags {
    if s == SymbolId::NONE {
        return SymbolFlags::NONE;
    }
    c.symbol_arena.borrow()[s.index()].flags
}

/// `symbol.name` (cloned) read through the arena.
fn symbol_name(c: &Checker, s: SymbolId) -> String {
    c.symbol_arena.borrow()[s.index()].name.to_string()
}

/// `symbol.declarations` (cloned) read through the arena.
fn symbol_declarations(c: &Checker, s: SymbolId) -> Vec<NodeId> {
    c.symbol_arena.borrow()[s.index()].declarations.clone()
}

/// `symbol.valueDeclaration` read through the arena.
fn symbol_value_declaration(c: &Checker, s: SymbolId) -> Option<NodeId> {
    c.symbol_arena.borrow()[s.index()].value_declaration
}

/// `b.ctx.tracker.ReportInferenceFallback(node)` — reports through the
// tracker when one is installed.
fn report_inference_fallback(b: &NodeBuilderImpl<'_>, node: Option<NodeId>, nodes: &[ast::Node]) {
    if let (Some(tracker), Some(node)) = (b.ctx.tracker.clone(), node) {
        tracker.borrow_mut().report_inference_fallback(node, nodes);
    }
}

/// `e.Name.Parent` — the parent of a pseudo element's name node, resolved
/// through the owning program arena.
fn name_parent(c: &Checker, name: Option<NodeId>,
        nodes: &[ast::Node],) -> Option<NodeId> {
    name.and_then(|n| {
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, nodes, (n).file_index());
        nn[n].parent
    })
}

/// `appendTypeNode` — the recursive closure inside `pseudoTypeToNode`'s
/// union case: flattens nested union type nodes and deduplicates `undefined`.
fn append_type_node(
    node: NodeId,
    res: &mut Vec<NodeId>,
    has_undefined: &mut bool,
    nodes: &[ast::Node],
) {
    if ast::is_union_type_node(&nodes[node]) {
        if let Some(types) = &nodes[node]
            .as_union_type_node()
            .union_or_intersection_type_node_base
            .types
        {
            for &sub in types.nodes.iter() {
                append_type_node(sub, res, has_undefined, nodes);
            }
        }
        return;
    }
    if nodes[node].kind == Kind::UndefinedKeyword {
        if *has_undefined {
            return;
        }
        *has_undefined = true;
    }
    res.push(node);
}

/// `isStructuralPseudoType`.
fn is_structural_pseudo_type(t: &PseudoType) -> bool {
    match t.kind() {
        PseudoTypeKind::ObjectLiteral
        | PseudoTypeKind::Tuple
        | PseudoTypeKind::SingleCallSignature => true,
        PseudoTypeKind::MaybeConstLocation => {
            let d = t.as_pseudo_type_maybe_const_location();
            is_structural_pseudo_type(&d.const_type) || is_structural_pseudo_type(&d.regular_type)
        }
        _ => false,
    }
}

impl<'a> NodeBuilderImpl<'a> {
    /// `(b *NodeBuilderImpl) pseudoTypeToNodeWithCheckerFallback` — like
    /// `pseudoTypeToNode` but when the top-level pseudo type is
    /// `PseudoTypeInferred`, it reports any error nodes and then serializes
    /// from the checker's type. This avoids incorrect type output when
    /// `PseudoTypeInferred` would derive the type from the original
    /// declaration expression in an instantiated context.
    pub(crate) fn pseudo_type_to_node_with_checker_fallback(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: PseudoTypeRef,
        checker_type: Option<TypeId>,
    ) -> Option<NodeId> {
        if t.kind() == PseudoTypeKind::Inferred {
            if !self.ctx.suppress_report_inference_fallback {
                let inferred = t.as_pseudo_type_inferred();
                if !inferred.error_nodes.is_empty() {
                    for &n in &inferred.error_nodes {
                        report_inference_fallback(self, Some(n), nodes);
                    }
                } else {
                    report_inference_fallback(self, Some(inferred.expression), nodes);
                }
            }
            let old_suppress = self.ctx.suppress_report_inference_fallback;
            self.ctx.suppress_report_inference_fallback = true;
            let result = self.type_to_type_node_opt(c, nodes, checker_type);
            self.ctx.suppress_report_inference_fallback = old_suppress;
            return result;
        } else if t.kind() == PseudoTypeKind::Direct {
            let existing = t.as_pseudo_type_direct().type_node;
            if !self.can_reuse_existing_js_type_node(
                c,
                nodes,
                existing,
                checker_type.unwrap_or(c.error_type),
            ) {
                if !self.ctx.suppress_report_inference_fallback {
                    report_inference_fallback(self, Some(existing), nodes);
                }
                let old_suppress = self.ctx.suppress_report_inference_fallback;
                self.ctx.suppress_report_inference_fallback = true;
                let result = self.type_to_type_node_opt(c, nodes, checker_type);
                self.ctx.suppress_report_inference_fallback = old_suppress;
                return result;
            }
        }
        self.pseudo_type_to_node(c, nodes, t)
    }

    /// `(b *NodeBuilderImpl) pseudoTypeToNode` — maps a pseudochecker's
    /// pseudotypes into ast nodes and reports any inference fallback errors
    /// the pseudotype structure implies.
    pub(crate) fn pseudo_type_to_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: PseudoTypeRef,
    ) -> Option<NodeId> {
        // debug.Assert(t != nil) — `PseudoTypeRef` is non-nil by construction.
        match t.kind() {
            PseudoTypeKind::Direct => {
                self.reuse_type_node(c, nodes, Some(t.as_pseudo_type_direct().type_node))
            }
            PseudoTypeKind::Inferred => {
                let (expression, error_nodes, is_signature_return) = {
                    let inferred = t.as_pseudo_type_inferred();
                    (
                        inferred.expression,
                        inferred.error_nodes.clone(),
                        inferred.is_signature_return,
                    )
                };
                let node = expression;
                if !error_nodes.is_empty() {
                    for &n in &error_nodes {
                        report_inference_fallback(self, Some(n), nodes);
                    }
                } else {
                    let (report_node,) = {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
                        let parent = nn[node].parent;
                        if ast::is_entity_name_expression(&nn[node], &nn)
                            && parent.is_some_and(|p| ast::is_declaration(&nn[p]))
                        {
                            (parent,)
                        } else {
                            (Some(node),)
                        }
                    };
                    report_inference_fallback(self, report_node, nodes);
                }
                if is_signature_return {
                    let sig = c.get_signature_from_declaration(node);
                    return self.serialize_return_type_for_signature(c, nodes, sig, false);
                }
                // use symbol type from parent declaration to automatically
                // handle expression type widening without duplicating logic
                let parent = {
                    let __program = c.program.clone().expect("program");
                    let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
                    nn[node].parent
                };
                if let Some(parent) = parent {
                    let parent_is_return = {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (parent).file_index());
                        ast::is_return_statement(&nn[parent])
                    };
                    if parent_is_return {
                        let enclosing = {
                            let __program = c.program.clone().expect("program");
                            let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
                            ast::get_containing_function(node, &nn)
                        };
                        if enclosing.is_some_and(|e| {
                            let __program = c.program.clone().expect("program");
                            let nn = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
                            ast::is_accessor(&nn[e])
                        }) {
                            return Some(self.serialize_type_for_declaration(
                                c, nodes, enclosing, None, None, false,
                            ));
                        }
                        let sig = c.get_signature_from_declaration(enclosing?);
                        return self.serialize_return_type_for_signature(c, nodes, sig, false);
                    }
                    let parent_is_arrow_body = {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (parent).file_index());
                        ast::is_arrow_function(&nn[parent])
                            && nn[parent]
                                .as_arrow_function()
                                .function_like_with_body_base
                                .body_base
                                .body
                                == Some(node)
                    };
                    if parent_is_arrow_body {
                        let sig = c.get_signature_from_declaration(parent);
                        return self.serialize_return_type_for_signature(c, nodes, sig, false);
                    }
                    let parent_is_declaration = {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (parent).file_index());
                        ast::is_declaration(&nn[parent])
                    };
                    if parent_is_declaration {
                        return Some(self.serialize_type_for_declaration(
                            c,
                            nodes,
                            Some(parent),
                            None,
                            None,
                            false,
                        ));
                    }
                }
                // This might be effectively unreachable. If it's not, it may
                // need more widening rules to mirror checker behavior for
                // whatever expressions are serialized here
                let ty = c.get_type_of_expression(node);
                Some(self.type_to_type_node(c, nodes, ty))
            }
            PseudoTypeKind::NoResult => {
                let node = t.as_pseudo_type_no_result().declaration;
                report_inference_fallback(self, Some(node), nodes);
                let is_fn_non_accessor = {
                    let __program = c.program.clone().expect("program");
                    let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
                    ast::is_function_like(Some(node), &nn) && !ast::is_accessor(&nn[node])
                };
                if is_fn_non_accessor {
                    let sig = c.get_signature_from_declaration(node);
                    return self.serialize_return_type_for_signature(c, nodes, sig, false);
                }
                Some(self.serialize_type_for_declaration(c, nodes, Some(node), None, None, false))
            }
            PseudoTypeKind::MaybeConstLocation => {
                let d = t.as_pseudo_type_maybe_const_location();
                // see checkExpressionWithContextualType for general literal
                // widening rules which need to be emulated here, plus
                // checkTemplateLiteralExpression for template literal
                // widening rules if the pseudochecker ever supports
                // literalized templates
                let mut is_in_const_context = c.is_const_context(d.node);
                if !is_in_const_context && {
                    let __program = c.program.clone().expect("program");
                    let nn = crate::printer_util::arena_view(&__program, nodes, (d.node).file_index());
                    pseudochecker::is_in_const_context(d.node, &nn)
                } {
                    // Only consult the contextual type if the pseudochecker's
                    // syntactic check also puts us in a const context.
                    // getContextualType returns post-inference results at
                    // node-printing time which may not have existed during
                    // initial checking (e.g. when the contextual type depends
                    // on inference), causing incorrect literal type
                    // preservation.
                    let contextual_type = c.get_contextual_type(d.node, ContextFlags::NONE);
                    let instantiated =
                        c.instantiate_contextual_type(contextual_type, d.node, ContextFlags::NONE);
                    if let Some(t2) = self.pseudo_type_to_type(c, &d.const_type)
                        && c.is_literal_of_contextual_type(t2, instantiated)
                    {
                        is_in_const_context = true;
                    }
                }
                if is_in_const_context {
                    self.pseudo_type_to_node(c, nodes, d.const_type.clone())
                } else {
                    self.pseudo_type_to_node(c, nodes, d.regular_type.clone())
                }
            }
            PseudoTypeKind::Union => {
                let mut res: Vec<NodeId> = Vec::new();
                let mut has_elided_type = false;
                let mut has_undefined = false;
                let members = t.as_pseudo_type_union().types.clone();
                for m in members {
                    if !c.strict_null_checks
                        && matches!(m.kind(), PseudoTypeKind::Undefined | PseudoTypeKind::Null)
                    {
                        has_elided_type = true;
                        continue;
                    }
                    if let Some(n) = self.pseudo_type_to_node(c, nodes, m) {
                        append_type_node(n, &mut res, &mut has_undefined, nodes);
                    }
                }
                if res.len() == 1 {
                    return Some(res[0]);
                }
                if res.is_empty() {
                    if has_elided_type {
                        return Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword));
                    }
                    return Some(self.f.new_keyword_type_node(nodes, Kind::NeverKeyword));
                }
                let list = self.f.new_node_list(res);
                Some(self.f.new_union_type_node(nodes, Some(list)))
            }
            PseudoTypeKind::Undefined => {
                if !c.strict_null_checks {
                    return Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword));
                }
                Some(self.f.new_keyword_type_node(nodes, Kind::UndefinedKeyword))
            }
            PseudoTypeKind::Null => {
                if !c.strict_null_checks {
                    return Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword));
                }
                let lit = self.f.new_keyword_expression(nodes, Kind::NullKeyword);
                Some(self.f.new_literal_type_node(nodes, Some(lit)))
            }
            PseudoTypeKind::Any => Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword)),
            PseudoTypeKind::String => {
                Some(self.f.new_keyword_type_node(nodes, Kind::StringKeyword))
            }
            PseudoTypeKind::Number => {
                Some(self.f.new_keyword_type_node(nodes, Kind::NumberKeyword))
            }
            PseudoTypeKind::BigInt => {
                Some(self.f.new_keyword_type_node(nodes, Kind::BigIntKeyword))
            }
            PseudoTypeKind::Boolean => {
                Some(self.f.new_keyword_type_node(nodes, Kind::BooleanKeyword))
            }
            PseudoTypeKind::False => {
                let lit = self.f.new_keyword_expression(nodes, Kind::FalseKeyword);
                Some(self.f.new_literal_type_node(nodes, Some(lit)))
            }
            PseudoTypeKind::True => {
                let lit = self.f.new_keyword_expression(nodes, Kind::TrueKeyword);
                Some(self.f.new_literal_type_node(nodes, Some(lit)))
            }
            PseudoTypeKind::SingleCallSignature => {
                let d = t.as_pseudo_type_single_call_signature();
                let signature = c.get_signature_from_declaration(d.signature);
                let expanded_params: Vec<Option<SymbolId>> = c
                    .get_expanded_parameters(signature, true /*skipUnionExpanding*/)
                    .into_iter()
                    .next()
                    .map(|v| v.into_iter().map(Some).collect())
                    .unwrap_or_default();
                let (sig_type_parameters, sig_parameters, sig_mapper) = {
                    let sig = c.signature_arena.get(signature);
                    (
                        sig.type_parameters.clone(),
                        sig.parameters.clone(),
                        sig.mapper,
                    )
                };
                let cleanup: ScopeCleanup = self.enter_new_scope(
                    c,
                    nodes,
                    Some(d.signature),
                    Some(expanded_params),
                    Some(sig_type_parameters),
                    Some(sig_parameters),
                    sig_mapper,
                );
                let type_params = if !d.type_parameters.is_empty() {
                    let mut res = Vec::with_capacity(d.type_parameters.len());
                    for &tp in &d.type_parameters {
                        if let Some(n) = self.reuse_node(c, nodes, tp) {
                            res.push(n);
                        }
                    }
                    Some(self.f.new_node_list(res))
                } else {
                    None
                };
                let params = self.pseudo_parameters_to_node_list(c, nodes, &d.parameters);
                let return_type = self.pseudo_type_to_node(c, nodes, d.return_type.clone());
                let result =
                    self.f
                        .new_function_type_node(nodes, type_params, Some(params), return_type);
                // Go `defer cleanup()`.
                cleanup.restore(self, nodes);
                Some(result)
            }
            PseudoTypeKind::Tuple => {
                let elements = t.as_pseudo_type_tuple().elements.clone();
                let mut res: Vec<NodeId> = Vec::with_capacity(elements.len());
                for e in elements {
                    if let Some(n) = self.pseudo_type_to_node(c, nodes, e) {
                        res.push(n);
                    }
                }
                // pseudo-tuples are implicitly `readonly` since they originate
                // from `as const` contexts but strada *sometimes* fails to add
                // the `readonly` modifier to the generated node.
                let element_list = self.f.new_node_list(res);
                let result = self.f.new_tuple_type_node(nodes, Some(element_list));
                self.e
                    .borrow()
                    .add_emit_flags(result, printer::EmitFlags::SINGLE_LINE);
                Some(
                    self.f
                        .new_type_operator_node(nodes, Kind::ReadonlyKeyword, Some(result)),
                )
            }
            PseudoTypeKind::ObjectLiteral => {
                let element_count = t.as_pseudo_type_object_literal().elements.len();
                if element_count == 0 {
                    let member_list = self.f.new_node_list(Vec::new());
                    let result = self.f.new_type_literal_node(nodes, Some(member_list));
                    self.e
                        .borrow()
                        .add_emit_flags(result, printer::EmitFlags::SINGLE_LINE);
                    return Some(result);
                }
                // NOTE: using the checker's `isConstContext` instead of the
                // pseudochecker's `isInConstContext` results in different
                // results here. The checker one is more "correct" but means
                // we'll mark objects in parameter positions contextually
                // typed by const type parameters as readonly - something a
                // true syntactic ID emitter couldn't possibly know (since the
                // signature could be from across files). This can't *really*
                // happen in any cases ID doesn't already error on, though.
                // Just something to keep in mind if the ID checker keeps
                // growing.
                let is_const = {
                    let first_name = t.as_pseudo_type_object_literal().elements[0].name;
                    let grandparent = first_name.and_then(|n| {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (n).file_index());
                        nn[n].parent.and_then(|p| nn[p].parent)
                    });
                    grandparent.is_some_and(|gp| c.is_const_context(gp))
                };
                let mut new_elements: Vec<NodeId> = Vec::with_capacity(element_count);

                // Member types are serialized within an object type literal,
                // so set the corresponding flag to mirror
                // createTypeNodeFromObjectType. This ensures inaccessible
                // `this` references inside the members are reported (TS2527).
                let restore_object_literal_flags = self.save_restore_flags();
                self.ctx.flags |= nodebuilder::Flags::IN_OBJECT_TYPE_LITERAL;

                for i in 0..element_count {
                    let (e_kind, e_name, _e_optional, e_signature) = {
                        let e = &t.as_pseudo_type_object_literal().elements[i];
                        (e.kind(), e.name, e.optional, e.signature())
                    };
                    let mut modifiers = None;
                    let readonly_element = {
                        let e = &t.as_pseudo_type_object_literal().elements[i];
                        e_kind == pseudochecker::PseudoObjectElementKind::PropertyAssignment
                            && e.as_pseudo_property_assignment().readonly
                    };
                    if is_const || readonly_element {
                        let m = self.f.new_token(nodes, Kind::ReadonlyKeyword);
                        modifiers = Some(self.f.new_modifier_list(nodes, vec![m]));
                    }
                    let mut cleanup: Option<ScopeCleanup> = None;
                    if e_kind != pseudochecker::PseudoObjectElementKind::PropertyAssignment {
                        let signature =
                            c.get_signature_from_declaration(e_signature.expect("signature"));
                        let expanded_params: Vec<Option<SymbolId>> = c
                            .get_expanded_parameters(signature, true /*skipUnionExpanding*/)
                            .into_iter()
                            .next()
                            .map(|v| v.into_iter().map(Some).collect())
                            .unwrap_or_default();
                        let (sig_type_parameters, sig_parameters, sig_mapper) = {
                            let sig = c.signature_arena.get(signature);
                            (
                                sig.type_parameters.clone(),
                                sig.parameters.clone(),
                                sig.mapper,
                            )
                        };
                        cleanup = Some(self.enter_new_scope(
                            c,
                            nodes,
                            e_signature,
                            Some(expanded_params),
                            Some(sig_type_parameters),
                            Some(sig_parameters),
                            sig_mapper,
                        ));
                    }
                    let new_prop = match e_kind {
                        pseudochecker::PseudoObjectElementKind::Method => {
                            let (d_type_parameters, d_parameters, d_return_type) = {
                                let d = t.as_pseudo_type_object_literal().elements[i]
                                    .as_pseudo_object_method();
                                (
                                    d.type_parameters.clone(),
                                    // PORT: `Vec<PseudoParameter>` isn't
                                    // `Clone` on the field itself — clone the
                                    // Vec so the borrow ends before the
                                    // `&mut self` serialization calls.
                                    d.parameters
                                        .iter()
                                        .map(|p| PseudoParameter {
                                            rest: p.rest,
                                            name: p.name,
                                            optional: p.optional,
                                            type_: p.type_.clone(),
                                        })
                                        .collect::<Vec<_>>(),
                                    d.return_type.clone(),
                                )
                            };
                            let type_params = if !d_type_parameters.is_empty() {
                                let mut res = Vec::with_capacity(d_type_parameters.len());
                                for tp in d_type_parameters {
                                    if let Some(n) = self.reuse_node(c, nodes, tp) {
                                        res.push(n);
                                    }
                                }
                                Some(self.f.new_node_list(res))
                            } else {
                                None
                            };
                            if is_const {
                                let name =
                                    self.reuse_name(c, nodes, e_name, false /*isMethod*/);
                                let params =
                                    self.pseudo_parameters_to_node_list(c, nodes, &d_parameters);
                                let return_type = self.pseudo_type_to_node(c, nodes, d_return_type);
                                let fn_type = self.f.new_function_type_node(
                                    nodes,
                                    type_params,
                                    Some(params),
                                    return_type,
                                );
                                self.f.new_property_signature_declaration(
                                    nodes,
                                    modifiers,
                                    name,
                                    None,
                                    Some(fn_type),
                                    None,
                                )
                            } else {
                                let name =
                                    self.reuse_name(c, nodes, e_name, true /*isMethod*/);
                                let params =
                                    self.pseudo_parameters_to_node_list(c, nodes, &d_parameters);
                                let return_type = self.pseudo_type_to_node(c, nodes, d_return_type);
                                self.f.new_method_signature_declaration(
                                    nodes,
                                    modifiers,
                                    name,
                                    None,
                                    type_params,
                                    Some(params),
                                    return_type,
                                )
                            }
                        }
                        pseudochecker::PseudoObjectElementKind::PropertyAssignment => {
                            let d_type = {
                                let d = t.as_pseudo_type_object_literal().elements[i]
                                    .as_pseudo_property_assignment();
                                d.type_.clone()
                            };
                            let name = self.reuse_name(c, nodes, e_name, false /*isMethod*/);
                            let type_node = self.pseudo_type_to_node(c, nodes, d_type);
                            self.f.new_property_signature_declaration(
                                nodes, modifiers, name, None, type_node, None,
                            )
                        }
                        pseudochecker::PseudoObjectElementKind::SetAccessor => {
                            let d_parameter = {
                                let d = t.as_pseudo_type_object_literal().elements[i]
                                    .as_pseudo_set_accessor();
                                PseudoParameter {
                                    rest: d.parameter.rest,
                                    name: d.parameter.name,
                                    optional: d.parameter.optional,
                                    type_: d.parameter.type_.clone(),
                                }
                            };
                            let name = self.reuse_name(c, nodes, e_name, false /*isMethod*/);
                            let param = self.pseudo_parameter_to_node(c, nodes, &d_parameter);
                            let param_list = self.f.new_node_list(vec![param]);
                            self.f.new_set_accessor_declaration(
                                nodes,
                                None,
                                name,
                                None,
                                Some(param_list),
                                None,
                                None,
                                None,
                            )
                        }
                        pseudochecker::PseudoObjectElementKind::GetAccessor => {
                            let d_type = {
                                let d = t.as_pseudo_type_object_literal().elements[i]
                                    .as_pseudo_get_accessor();
                                d.type_.clone()
                            };
                            let name = self.reuse_name(c, nodes, e_name, false /*isMethod*/);
                            let type_node = self.pseudo_type_to_node(c, nodes, d_type);
                            self.f.new_get_accessor_declaration(
                                nodes, None, name, None, None, type_node, None, None,
                            )
                        }
                    };
                    let in_enclosing_file = e_name.is_some_and(|n| {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (n).file_index());
                        self.ctx.enclosing_file == ast::get_source_file_of_node(e_name, &nn)
                    });
                    if in_enclosing_file {
                        let loc = {
                            let __program = c.program.clone().expect("program");
                            let nn = crate::printer_util::arena_view(&__program, nodes, (e_name.unwrap()).file_index());
                            e_name.and_then(|n| nn[n].parent).map(|p| nn[p].loc)
                        };
                        if let Some(loc) = loc {
                            self.e.borrow().set_comment_range(new_prop, loc);
                        }
                    }
                    new_elements.push(new_prop);
                    if let Some(cleanup) = cleanup {
                        // Go `if cleanup != nil { cleanup() }`.
                        cleanup.restore(self, nodes);
                    }
                }
                restore_object_literal_flags.restore(&mut self.ctx);
                let member_list = self.f.new_node_list(new_elements);
                let result = self.f.new_type_literal_node(nodes, Some(member_list));
                if !self
                    .ctx
                    .flags
                    .intersects(nodebuilder::Flags::MULTILINE_OBJECT_LITERALS)
                {
                    self.e
                        .borrow()
                        .add_emit_flags(result, printer::EmitFlags::SINGLE_LINE);
                }
                Some(result)
            }
            PseudoTypeKind::StringLiteral
            | PseudoTypeKind::NumericLiteral
            | PseudoTypeKind::BigIntLiteral => {
                let source = t.as_pseudo_type_literal().node;
                let literal = self.reuse_node(c, nodes, source);
                Some(self.f.new_literal_type_node(nodes, literal))
            }
        }
    }

    /// `(b *NodeBuilderImpl) pseudoParametersToNodeList`.
    pub(crate) fn pseudo_parameters_to_node_list(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        params: &[PseudoParameter],
    ) -> NodeList {
        let mut res = Vec::with_capacity(params.len());
        for p in params {
            res.push(self.pseudo_parameter_to_node(c, nodes, p));
        }
        self.f.new_node_list(res)
    }

    /// `(b *NodeBuilderImpl) pseudoParameterToNode`.
    pub(crate) fn pseudo_parameter_to_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        p: &PseudoParameter,
    ) -> NodeId {
        let dot_dot_dot = if p.rest {
            Some(self.f.new_token(nodes, Kind::DotDotDotToken))
        } else {
            None
        };
        let question_mark = if p.optional {
            Some(self.f.new_token(nodes, Kind::QuestionToken))
        } else {
            None
        };
        // matches strada behavior of always reserializing param names from
        // scratch
        let name = {
            let parent = name_parent(c, p.name, &[]);
            let symbol = parent.and_then(|par| {
                let __program = c.program.clone().expect("program");
                let pn = crate::printer_util::arena_view(&__program, nodes, (par).file_index());
                pn[par].symbol()
            });
            self.parameter_to_parameter_declaration_name(
                c,
                nodes,
                symbol.unwrap_or(SymbolId::NONE),
                parent,
            )
        };
        let type_node = self.pseudo_type_to_node(c, nodes, p.type_.clone());
        let parameter = self.f.new_parameter_declaration(
            nodes,
            None,
            dot_dot_dot,
            name,
            question_mark,
            type_node,
            None,
        );
        if let Some(original) = name_parent(c, p.name, &[]) {
            let is_param = {
                let __program = c.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, nodes, (original).file_index());
                ast::is_parameter_declaration(&nn[original])
            };
            if is_param {
                self.set_comment_range(c, nodes, parameter, Some(original));
            }
        }
        parameter
    }

    /// `(b *NodeBuilderImpl) pseudoTypeEquivalentToType` — see
    /// `typeNodeIsEquivalentToType` in strada, but applied more broadly here,
    /// so is setup to handle more equivalences - strada only used it via the
    /// `canReuseTypeNodeAnnotation` host hook and not the `canReuseTypeNode`
    /// hook, which meant locations using the later were reliant on
    /// over-invalidation by the ID inference engine to not emit incorrect
    /// types.
    pub(crate) fn pseudo_type_equivalent_to_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: &PseudoTypeRef,
        type_: TypeId,
        is_optional_annotated: bool,
        report_errors: bool,
    ) -> bool {
        // if type_ resolves to an error, we charitably assume equality, since
        // we might be in a single-file checking mode
        if c.is_error_type(type_) {
            return true;
        }
        // If we can easily operate on just types, we should
        let type_from_pseudo = self.pseudo_type_to_type(c, t); // note: cannot convert complex types like objects, which must be validated separately
        if type_from_pseudo == Some(type_) {
            return true;
        }
        let undefined_stripped = if is_optional_annotated {
            c.get_type_with_facts(type_, TypeFacts::NE_UNDEFINED)
        } else {
            type_
        };
        if let Some(tfp) = type_from_pseudo {
            if is_optional_annotated {
                if undefined_stripped == tfp {
                    return true;
                }
                if c.types_handle().get(tfp).flags.intersects(TypeFlags::UNION)
                    && c.types_handle()
                        .get(undefined_stripped)
                        .flags
                        .intersects(TypeFlags::UNION)
                {
                    // does union comparison in general, since the unions may
                    // not be `==` identical due to aliasing and the like
                    if c.compare_types_identical(tfp, undefined_stripped) == Ternary::TRUE {
                        return true;
                    }
                }
            }
            // handles freshness mismatches (e.g., fresh true vs regular true
            // in as const)
            if c.get_regular_type_of_literal_type(tfp) == c.get_regular_type_of_literal_type(type_)
            {
                return true;
            }
            if c.types_handle().get(tfp).flags.intersects(TypeFlags::UNION)
                && c.types_handle()
                    .get(type_)
                    .flags
                    .intersects(TypeFlags::UNION)
            {
                // handles union comparison in general, since unions may not
                // be `==` identical due to aliasing
                if c.compare_types_identical(tfp, type_) == Ternary::TRUE {
                    return true;
                }
            }
        }
        // otherwise, fallback to actual pseudo/type cross-comparisons
        match t.kind() {
            PseudoTypeKind::Inferred => {
                // PseudoTypeInferred with error nodes identifies specific
                // problematic children. Report fine-grained errors on them,
                // then return false so the parent falls back to checker-based
                // serialization (avoiding issues like reusing raw JSON string
                // literal property names from the pseudochecker's AST).
                let inferred = t.as_pseudo_type_inferred();
                if !inferred.error_nodes.is_empty() {
                    if report_errors {
                        for &n in &inferred.error_nodes {
                            report_inference_fallback(self, Some(n), nodes);
                        }
                    }
                    return false;
                }
                if report_errors {
                    report_inference_fallback(self, Some(inferred.expression), nodes);
                }
                false
            }
            PseudoTypeKind::ObjectLiteral => {
                let element_count = t.as_pseudo_type_object_literal().elements.len();
                let target_props = c.get_properties_of_type(undefined_stripped);
                // Count total declarations across all target prop symbols to
                // handle getter/setter pairs, which are two elements in
                // pt.Elements but only one symbol in targetProps.
                let mut target_decl_count = 0usize;
                for &prop in &target_props {
                    target_decl_count += symbol_declarations(c, prop).len();
                }
                if element_count != target_decl_count {
                    return false;
                }
                for i in 0..element_count {
                    let (e_kind, e_name, e_optional) = {
                        let e = &t.as_pseudo_type_object_literal().elements[i];
                        (e.kind(), e.name, e.optional)
                    };
                    let mut target_prop: Option<SymbolId> = None;
                    let elem_symbol = name_parent(c, e_name, &[]).and_then(|parent| {
                        let __program = c.program.clone().expect("program");
                        let pn = crate::printer_util::arena_view(&__program, nodes, (parent).file_index());
                        pn[parent].symbol()
                    });
                    if let Some(elem_symbol) = elem_symbol {
                        target_prop = c
                            .get_property_of_type(undefined_stripped, &symbol_name(c, elem_symbol));
                    }
                    if target_prop.is_none() {
                        // Name lookup failed or returned no result; search
                        // target properties for one whose declaration name
                        // node matches the one we have
                        for &prop in &target_props {
                            if symbol_value_declaration(c, prop).and_then(|vd| {
                                let __program = c.program.clone().expect("program");
                                let vn = crate::printer_util::arena_view(&__program, nodes, (vd).file_index());
                                vn[vd].name()
                            }) == e_name
                            {
                                target_prop = Some(prop);
                                break;
                            }
                        }
                        if target_prop.is_none() {
                            if report_errors {
                                report_inference_fallback(self, name_parent(c, e_name, &[]), nodes);
                            }
                            return false;
                        }
                    }
                    let target_prop = target_prop.unwrap();
                    let target_is_optional =
                        symbol_flags(c, target_prop).intersects(SymbolFlags::OPTIONAL);
                    if e_optional != target_is_optional {
                        if report_errors {
                            report_inference_fallback(self, name_parent(c, e_name, &[]), nodes);
                        }
                        return false;
                    }
                    let mut prop_type = c.get_type_of_symbol(target_prop);
                    prop_type = c.remove_missing_type(prop_type, target_is_optional);
                    match e_kind {
                        pseudochecker::PseudoObjectElementKind::PropertyAssignment => {
                            let d_type = t.as_pseudo_type_object_literal().elements[i]
                                .as_pseudo_property_assignment()
                                .type_
                                .clone();
                            if !self.pseudo_type_equivalent_to_type(
                                c, nodes, &d_type, prop_type, e_optional, false,
                            ) {
                                if report_errors {
                                    if d_type.kind() == PseudoTypeKind::Inferred
                                        && !d_type.as_pseudo_type_inferred().error_nodes.is_empty()
                                    {
                                        // Re-report the fine-grained error
                                        // nodes; the recursive call used
                                        // reportErrors=false
                                        for &n in &d_type.as_pseudo_type_inferred().error_nodes {
                                            report_inference_fallback(self, Some(n), nodes);
                                        }
                                    } else if !is_structural_pseudo_type(&d_type) {
                                        report_inference_fallback(
                                            self,
                                            name_parent(c, e_name, &[]),
                                            nodes,
                                        );
                                    }
                                }
                                return false;
                            }
                        }
                        pseudochecker::PseudoObjectElementKind::Method => {
                            let (d_parameters, d_return_type) = {
                                let d = t.as_pseudo_type_object_literal().elements[i]
                                    .as_pseudo_object_method();
                                (
                                    d.parameters
                                        .iter()
                                        .map(|p| PseudoParameter {
                                            rest: p.rest,
                                            name: p.name,
                                            optional: p.optional,
                                            type_: p.type_.clone(),
                                        })
                                        .collect::<Vec<_>>(),
                                    d.return_type.clone(),
                                )
                            };
                            let Some(target_sig) = c.get_single_call_signature(prop_type) else {
                                // Target property type doesn't have a single
                                // call signature; can't validate
                                continue;
                            };
                            let param_eq = self.pseudo_parameters_equivalent_to_parameters(
                                c,
                                nodes,
                                &d_parameters,
                                target_sig,
                                report_errors,
                                name_parent(c, e_name, &[]),
                            );
                            if !param_eq {
                                return false;
                            }
                            let target_predicate = c.get_type_predicate_of_signature(target_sig);
                            if let Some(target_predicate) = target_predicate.as_ref() {
                                if !self.pseudo_return_type_matches_predicate(
                                    c,
                                    &d_return_type,
                                    target_predicate, &[]) {
                                    if report_errors {
                                        report_inference_fallback(
                                            self,
                                            name_parent(c, e_name, &[]),
                                            nodes,
                                        );
                                    }
                                    return false;
                                }
                            } else {
                                let return_type = c.get_return_type_of_signature(target_sig);
                                if !self.pseudo_type_equivalent_to_type(
                                    c,
                                    nodes,
                                    &d_return_type,
                                    return_type,
                                    false,
                                    false,
                                ) {
                                    if report_errors {
                                        report_inference_fallback(
                                            self,
                                            name_parent(c, e_name, &[]),
                                            nodes,
                                        );
                                    }
                                    return false;
                                }
                            }
                        }
                        pseudochecker::PseudoObjectElementKind::GetAccessor => {
                            let d_type = t.as_pseudo_type_object_literal().elements[i]
                                .as_pseudo_get_accessor()
                                .type_
                                .clone();
                            if !self.pseudo_type_equivalent_to_type(
                                c, nodes, &d_type, prop_type, false, false,
                            ) {
                                if report_errors {
                                    report_inference_fallback(self, name_parent(c, e_name, &[]), nodes);
                                }
                                return false;
                            }
                        }
                        pseudochecker::PseudoObjectElementKind::SetAccessor => {
                            let d_parameter_type = t.as_pseudo_type_object_literal().elements[i]
                                .as_pseudo_set_accessor()
                                .parameter
                                .type_
                                .clone();
                            let write_type = c.get_write_type_of_symbol(target_prop);
                            if !self.pseudo_type_equivalent_to_type(
                                c,
                                nodes,
                                &d_parameter_type,
                                write_type,
                                false,
                                false,
                            ) {
                                if report_errors {
                                    report_inference_fallback(self, name_parent(c, e_name, &[]), nodes);
                                }
                                return false;
                            }
                        }
                    }
                }
                true
            }
            PseudoTypeKind::Tuple => {
                let element_count = t.as_pseudo_type_tuple().elements.len();
                if !crate::checker_core::is_tuple_type(&c.types, undefined_stripped) {
                    return false;
                }
                let __arena_tuple_target = c.types.clone();
                let tuple_target = __arena_tuple_target.target_tuple_type(undefined_stripped);
                let Some(tuple_target) = tuple_target else {
                    return false;
                };
                // Pseudo-tuples come from `as const` array literals, so they
                // only ever have required elements. If the target tuple has
                // optional, rest, or variadic elements, the structures can't
                // match.
                if c.types_handle()
                    .get(tuple_target)
                    .as_tuple_type()
                    .combined_flags
                    .intersects(ElementFlags::NON_REQUIRED)
                {
                    return false;
                }
                let element_types = c.get_type_arguments(undefined_stripped);
                if element_count != element_types.len() {
                    return false;
                }
                for i in 0..element_count {
                    let elem = t.as_pseudo_type_tuple().elements[i].clone();
                    if !self.pseudo_type_equivalent_to_type(
                        c,
                        nodes,
                        &elem,
                        element_types[i],
                        false,
                        report_errors,
                    ) {
                        return false;
                    }
                }
                true
            }
            PseudoTypeKind::SingleCallSignature => {
                let Some(target_sig) = c.get_single_call_signature(undefined_stripped) else {
                    return false;
                };
                let (pt_type_parameters_len, pt_signature, pt_return_type, pt_parameters) = {
                    let pt = t.as_pseudo_type_single_call_signature();
                    (
                        pt.type_parameters.len(),
                        pt.signature,
                        pt.return_type.clone(),
                        pt.parameters
                            .iter()
                            .map(|p| PseudoParameter {
                                rest: p.rest,
                                name: p.name,
                                optional: p.optional,
                                type_: p.type_.clone(),
                            })
                            .collect::<Vec<_>>(),
                    )
                };
                if c.signature_arena.get(target_sig).type_parameters.len() != pt_type_parameters_len
                {
                    if report_errors {
                        report_inference_fallback(self, Some(pt_signature), nodes);
                    }
                    return false;
                }
                let param_eq = self.pseudo_parameters_equivalent_to_parameters(
                    c,
                    nodes,
                    &pt_parameters,
                    target_sig,
                    report_errors,
                    Some(pt_signature),
                );
                if !param_eq {
                    return false;
                }
                let target_predicate = c.get_type_predicate_of_signature(target_sig);
                if let Some(target_predicate) = target_predicate.as_ref() {
                    if !self.pseudo_return_type_matches_predicate(
                        c,
                        &pt_return_type,
                        target_predicate, &[]) {
                        if report_errors {
                            report_inference_fallback(self, Some(pt_signature), nodes);
                        }
                        return false;
                    }
                } else {
                    let return_type = c.get_return_type_of_signature(target_sig);
                    if !self.pseudo_type_equivalent_to_type(
                        c,
                        nodes,
                        &pt_return_type,
                        return_type,
                        false,
                        report_errors,
                    ) {
                        // error reported within the return type
                        return false;
                    }
                }
                true
            }
            PseudoTypeKind::NoResult => {
                if report_errors {
                    let declaration = t.as_pseudo_type_no_result().declaration;
                    report_inference_fallback(self, Some(declaration), nodes);
                }
                false
            }
            _ => false,
        }
    }

    /// `(b *NodeBuilderImpl) pseudoParametersEquivalentToParameters`.
    pub(crate) fn pseudo_parameters_equivalent_to_parameters(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        params: &[PseudoParameter],
        target_sig: SignatureId,
        report_errors: bool,
        non_param_error_location: Option<NodeId>,
    ) -> bool {
        let (this_parameter, sig_parameters) = {
            let sig = c.signature_arena.get(target_sig);
            (sig.this_parameter, sig.parameters.clone())
        };
        let mut params = params;
        if let Some(this_param) = this_parameter {
            if params.is_empty() {
                if report_errors {
                    // missing `this` param
                    report_inference_fallback(self, non_param_error_location, nodes);
                }
                return false;
            } else if params[0].name.is_some_and(|n| {
                let __program = c.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, nodes, (n).file_index());
                ast::is_this_identifier(&nn[n])
            }) {
                let param_type = c.get_type_of_parameter(this_param);
                if !self.pseudo_type_equivalent_to_type(
                    c,
                    nodes,
                    &params[0].type_,
                    param_type,
                    params[0].optional,
                    false,
                ) {
                    if report_errors {
                        report_inference_fallback(self, name_parent(c, params[0].name, &[]), nodes);
                    }
                    return false;
                }
                params = &params[1..];
            } else {
                if report_errors {
                    report_inference_fallback(self, non_param_error_location, nodes);
                }
                return false;
            }
        }
        if sig_parameters.len() != params.len() {
            if report_errors {
                report_inference_fallback(self, non_param_error_location, nodes);
            }
            return false; // TODO: spread tuple params may mess with this check
        }
        for (i, p) in params.iter().enumerate() {
            let target_param = sig_parameters[i];
            let target_is_optional = symbol_value_declaration(c, target_param)
                .is_some_and(|vd| c.is_optional_parameter(vd));
            if p.optional != target_is_optional {
                if report_errors {
                    report_inference_fallback(self, name_parent(c, p.name, &[]), nodes);
                }
                return false;
            }
            let param_type = c.get_type_of_parameter(target_param);
            if !self
                .pseudo_type_equivalent_to_type(c, nodes, &p.type_, param_type, p.optional, false)
            {
                if report_errors {
                    report_inference_fallback(self, name_parent(c, p.name, &[]), nodes);
                }
                return false;
            }
        }
        true
    }

    /// `(b *NodeBuilderImpl) pseudoReturnTypeMatchesPredicate` — checks if a
    /// pseudo return type (which should be a Direct type wrapping a
    /// TypePredicate) matches the given type predicate from the checker.
    pub(crate) fn pseudo_return_type_matches_predicate(
        &mut self,
        c: &mut Checker,
        rt: &PseudoTypeRef,
        predicate: &TypePredicate,
            nodes: &[ast::Node],) -> bool {
        if rt.kind() != PseudoTypeKind::Direct {
            return false;
        }
        let node = rt.as_pseudo_type_direct().type_node;
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
        if !ast::is_type_predicate_node(&nn[node]) {
            return false;
        }
        let (asserts_modifier, parameter_name, tp_type) = {
            let tp = nn[node].as_type_predicate_node();
            (tp.asserts_modifier, tp.parameter_name, tp.type_)
        };
        // Check asserts modifier matches
        let is_asserts = asserts_modifier.is_some();
        let predicate_is_asserts = matches!(
            predicate.kind,
            TypePredicateKind::AssertsThis | TypePredicateKind::AssertsIdentifier
        );
        if is_asserts != predicate_is_asserts {
            return false;
        }
        // Check this vs identifier matches
        let is_this = parameter_name.is_some_and(|pn| ast::is_this_type_node(&nn[pn]));
        let predicate_is_this = matches!(
            predicate.kind,
            TypePredicateKind::This | TypePredicateKind::AssertsThis
        );
        if is_this != predicate_is_this {
            return false;
        }
        // For identifier predicates, check parameter name matches
        if !is_this {
            let name_text = parameter_name.map(|pn| nn[pn].text(&nn).into_owned());
            if name_text.as_deref() != Some(predicate.parameter_name.as_str()) {
                return false;
            }
        }
        // Check the narrowed type, if any
        if let Some(predicate_t) = predicate.t {
            let Some(tp_type) = tp_type else {
                return false;
            };
            let predicate_type_from_node = c.get_type_from_type_node(tp_type);
            if predicate_type_from_node != predicate_t
                && c.compare_types_identical(predicate_type_from_node, predicate_t) != Ternary::TRUE
            {
                return false;
            }
        } else if tp_type.is_some() {
            return false;
        }
        true
    }

    /// `(b *NodeBuilderImpl) pseudoTypeToType`.
    ///
    /// !!! TODO: only literal types currently mapped because this is only
    /// used to determine if literal contextual typing need apply to the
    /// pseudotype. If this is used more broadly, the implementation needs to
    /// be filled out more to handle the structural pseudotypes - signatures,
    /// objects, tuples, etc.
    pub(crate) fn pseudo_type_to_type(
        &mut self,
        c: &mut Checker,
        t: &PseudoType,
    ) -> Option<TypeId> {
        // debug.Assert(t != nil) — `&PseudoType` is non-nil by construction.
        match t.kind() {
            PseudoTypeKind::Direct => {
                Some(c.get_type_from_type_node(t.as_pseudo_type_direct().type_node))
            }
            PseudoTypeKind::Inferred => {
                let node = t.as_pseudo_type_inferred().expression;
                if t.as_pseudo_type_inferred().is_signature_return {
                    let sig = c.get_signature_from_declaration(node);
                    return Some(c.get_return_type_of_signature(sig));
                }
                let regular = c.get_regular_type_of_expression(node);
                let ty = c.get_widened_type(regular);
                Some(ty)
            }
            // TODO: extract type selection logic from
            // `serializeTypeForDeclaration`, not needed for current usecases
            // but needed if completeness becomes required
            PseudoTypeKind::NoResult => None,
            PseudoTypeKind::MaybeConstLocation => {
                let d = t.as_pseudo_type_maybe_const_location();
                if c.is_const_context(d.node) {
                    self.pseudo_type_to_type(c, &d.const_type)
                } else {
                    self.pseudo_type_to_type(c, &d.regular_type)
                }
            }
            PseudoTypeKind::Union => {
                let mut res: Vec<TypeId> = Vec::new();
                let mut has_elided_type = false;
                let members = t.as_pseudo_type_union().types.clone();
                for m in members {
                    if !c.strict_null_checks
                        && matches!(m.kind(), PseudoTypeKind::Undefined | PseudoTypeKind::Null)
                    {
                        has_elided_type = true;
                        continue;
                    }
                    let t2 = self.pseudo_type_to_type(c, &m);
                    let Some(t2) = t2 else {
                        return None; // propagate failure
                    };
                    res.push(t2);
                }
                if res.len() == 1 {
                    return Some(res[0]);
                }
                if res.is_empty() {
                    if has_elided_type {
                        return Some(c.any_type);
                    }
                    return Some(c.never_type);
                }
                Some(c.get_union_type(&res))
            }
            PseudoTypeKind::Undefined => Some(c.undefined_widening_type),
            PseudoTypeKind::Null => Some(c.null_widening_type),
            PseudoTypeKind::Any => Some(c.any_type),
            PseudoTypeKind::String => Some(c.string_type),
            PseudoTypeKind::Number => Some(c.number_type),
            PseudoTypeKind::BigInt => Some(c.bigint_type),
            PseudoTypeKind::Boolean => Some(c.boolean_type),
            PseudoTypeKind::False => Some(c.false_type),
            PseudoTypeKind::True => Some(c.true_type),
            PseudoTypeKind::StringLiteral
            | PseudoTypeKind::NumericLiteral
            | PseudoTypeKind::BigIntLiteral => {
                let source = t.as_pseudo_type_literal().node;
                // big shortcut, uses cached expression types where possible
                Some(c.get_regular_type_of_expression(source))
            }
            // no simple mapping to a type, since these are structural types
            PseudoTypeKind::ObjectLiteral
            | PseudoTypeKind::SingleCallSignature
            | PseudoTypeKind::Tuple => None,
        }
    }
}
